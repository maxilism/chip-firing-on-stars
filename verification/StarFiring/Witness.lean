import StarFiring.Balance

/-! A certificate of full, unpinned reachability on fourteen arms.  The script
uses actual chip choices even at sites containing three chips. All finite
checks reduce inside Lean; they do not invoke the native compiler.
-/
namespace StarFiring.Witness

/-- Trace execution; intermediate states are the unreduced game's ledgers. -/
def execute (s : Config k) : List (Move k) → Config k
  | [] => s
  | m :: ms => execute (m.act s) ms

/-- This check tests legality *before* applying each move. -/
def valid (s : Config k) : List (Move k) → Bool
  | [] => true
  | m :: ms => decide (m.Legal s) && valid (m.act s) ms

theorem run_of_valid {s : Config k} {ms : List (Move k)} (h : valid s ms = true) :
    Run s ms (execute s ms) := by
  induction ms generalizing s with
  | nil => exact .nil
  | cons m ms ih =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .cons h.1 (ih h.2)

-- One-based notation in the data, converted once to Core's zero-based types.
private def batch (v : Vector Nat 14) : Batch 14 := fun i =>
  Fin.ofNat 42 (v[i] - 1)
private def cmp (row level lo hi : Nat) : Move 14 :=
  .arm (Fin.ofNat 14 (row-1)) (level-1) (Fin.ofNat 42 (lo-1)) (Fin.ofNat 42 (hi-1))

/-- The two initial deliveries; early comparisons; third delivery; late
comparisons; fourth delivery; comparisons at levels one and two; fifth
delivery; final comparisons at level one; last delivery. -/
def moves : List (Move 14) :=
  [.center (batch #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 28, 29, 30, 31, 32]), .center (batch #v[20, 21, 22, 23, 24, 25, 26, 27, 37, 38, 39, 40, 41, 42]),
   cmp 1 1 1 20, cmp 6 1 6 25, cmp 8 1 8 27, cmp 9 1 9 37, cmp 11 1 29 39, cmp 13 1 31 41, cmp 14 1 32 42,
   .center (batch #v[13, 14, 15, 16, 17, 18, 19, 29, 31, 32, 33, 34, 35, 36]),
   cmp 2 1 14 21, cmp 3 1 15 22, cmp 4 1 16 23, cmp 5 1 17 24, cmp 7 1 19 26, cmp 10 1 32 38, cmp 12 1 34 40,
   .center (batch #v[1, 6, 8, 9, 10, 11, 12, 14, 15, 16, 17, 19, 32, 34]),
   cmp 1 1 1 13, cmp 1 2 13 20, cmp 2 1 2 6, cmp 2 2 6 21, cmp 3 1 3 8, cmp 3 2 8 22, cmp 4 1 4 9, cmp 4 2 9 23, cmp 5 1 5 10, cmp 5 2 10 24, cmp 6 1 11 18, cmp 6 2 18 25, cmp 7 1 7 12, cmp 7 2 12 26,
   cmp 8 1 14 29, cmp 8 2 27 29, cmp 9 1 15 31, cmp 9 2 31 37, cmp 10 1 16 28, cmp 10 2 28 38, cmp 11 1 17 33, cmp 11 2 33 39, cmp 12 1 19 30, cmp 12 2 30 40, cmp 13 1 32 35, cmp 13 2 35 41, cmp 14 1 34 36, cmp 14 2 36 42,
   .center (batch #v[1, 2, 3, 4, 5, 7, 11, 14, 15, 16, 17, 19, 32, 34]),
   cmp 1 1 1 13, cmp 2 1 2 6, cmp 3 1 3 8, cmp 4 1 4 9, cmp 5 1 5 10, cmp 6 1 7 18, cmp 7 1 11 12, cmp 8 1 14 27, cmp 9 1 15 31, cmp 10 1 16 28, cmp 11 1 17 33, cmp 12 1 19 30, cmp 13 1 32 35, cmp 14 1 34 36,
   .center (batch #v[1, 2, 3, 4, 5, 7, 11, 14, 15, 16, 17, 19, 32, 34])]

def finalState : Config 14 := execute (initial 14) moves

/-- Middle ranks: `6,1,2,3,4,7,5,8,11,9,12,10,13,14` in one-based notation. -/
def perm14 (i : Row 14) : Row 14 :=
  (#v[5,0,1,2,3,6,4,7,10,8,11,9,12,13] : Vector (Fin 14) 14)[i]

theorem length_moves : moves.length = 62 := by decide

set_option maxRecDepth 15000
set_option maxHeartbeats 6000000

theorem run14 : Run (initial 14) moves finalState := run_of_valid (by decide +kernel)

/-- No firing in this trace originates beyond physical level two. -/
private def low : Move k → Bool
  | .center _ => true
  | .arm _ d _ _ => d < 2

private theorem delta_far (m : Move k) (hm : low m = true) (i : Row k)
    (d : Nat) (x : Chip k) : m.delta (.arm i (d+3)) x = 0 := by
  cases m with
  | center b => rfl
  | arm j e a b =>
    have he : e < 2 := by simpa [low] using hm
    have : e = 0 ∨ e = 1 := by omega
    rcases this with rfl | rfl <;> simp [Move.delta, inward, ind]

private theorem execute_far {s : Config k} {ms : List (Move k)} (h : ms.all low = true)
    (i : Row k) (d : Nat) (x : Chip k) : execute s ms (.arm i (d+3)) x = s (.arm i (d+3)) x := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [execute, ih h.2]; simp [Move.act, delta_far m h.1]

private theorem load_trace {s t : Config k} {ms : List (Move k)} (r : Run s ms t)
    (v : Site k) : load t v = load s v + (ms.map fun m => m.loadDelta v).sum := by
  induction r with
  | nil => simp
  | cons hl _ ih => rw [ih, load_act hl]; simp [Int.add_assoc]

/-- The center is empty, the first three sites on every ray have load exactly
one, and every other site has load zero. -/
theorem final_loads : load finalState .center = 0 ∧
    (∀ (i : Row 14) (d : Fin 3), load finalState (.arm i d) = 1) ∧
    (∀ (i : Row 14) (d : Nat), load finalState (.arm i (d+3)) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [load_trace run14, load_initial_center]; decide +kernel
  · have h : ∀ (i : Row 14) (d : Fin 3),
        (moves.map fun m => m.loadDelta (.arm i d)).sum = 1 := by decide +kernel
    intro i d; rw [load_trace run14, load_initial_arm, h]; decide
  intro i d
  have he : finalState (.arm i (d+3)) = fun _ => 0 := by
    funext x; exact execute_far (s := initial 14) (ms := moves) (by decide) i d x
  simp [load, he, List.map_const']

theorem stable14 : Stable finalState := by
  refine ⟨by simp [final_loads.1], ?_⟩
  intro i d
  by_cases hd : d < 3
  · rw [final_loads.2.1 i ⟨d, hd⟩]; decide
  · rw [show d = (d-3)+3 by omega, final_loads.2.2]; decide

/-- The numerical middle labels, in the one-based convention of the script. -/
def middle14 : Batch 14 := batch #v[13,6,8,9,10,18,12,27,31,28,33,30,35,36]

theorem order14 : MiddleOrder finalState perm14 :=
  ⟨middle14, by decide +kernel, by decide +kernel⟩

theorem realizable14 : Realizable perm14 :=
  ⟨finalState, ⟨moves, run14⟩, stable14, order14⟩

end StarFiring.Witness
