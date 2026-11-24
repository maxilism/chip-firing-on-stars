import StarFiring.Balance
import StarFiring.Physical

/-! Unlabeled balance, the least-action bound on arbitrary legal prefixes,
and the exact odometer and loads of a stable terminal run. -/
namespace StarFiring

def Move.source : Move k → Site k
  | .center _ => .center
  | .arm i d _ _ => .arm i d

namespace Counts
variable {k : Nat}
/-- Total firings at each site at equilibrium. -/
def quota : Site k → Nat
  | .center => 6 | .arm _ 0 => 3 | .arm _ 1 => 1 | .arm _ (_ + 2) => 0
abbrev Tally (k : Nat) := Site k → Nat
def rowSum (f : Row k → Int) : Int := ((List.finRange k).map f).sum
private theorem map_sum_le {α : Type} (l : List α) (f g : α → Int)
    (h : ∀ x, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp; exact Int.add_le_add (h x) ih
theorem rowSum_le {f g : Row k → Int} (h : ∀ i, f i ≤ g i) : rowSum f ≤ rowSum g :=
  map_sum_le _ _ _ h
theorem rowSum_const (b : Int) : rowSum (k:=k) (fun _ => b) = k*b := by
  have aux {α : Type} (l : List α) : (l.map (fun _ => b)).sum = l.length * b := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih, Int.add_mul, Int.add_comm]
  simpa [rowSum] using aux (List.finRange k)
/-- The load forced by the odometer: each site receives from its neighbors and
spends its own degree on each firing. Depth zero is the first site on an arm. -/
def predicted (c : Tally k) : Site k → Int
  | .center => 3 * (k : Int) - (c .center : Int) * k + rowSum (fun i => c (.arm i 0))
  | .arm i 0 => c .center - 2 * (c (.arm i 0) : Int) + c (.arm i 1)
  | .arm i (d+1) => c (.arm i d) - 2 * (c (.arm i (d+1)) : Int) + c (.arm i (d+2))
private def cost : Site k → Int
  | .center => k | .arm _ _ => 2
private theorem quota_stable (hk : 0 < k) (v : Site k) : predicted quota v < cost v := by
  cases v with
  | center => simp [predicted, quota, cost, rowSum_const, Int.mul_comm]; omega
  | arm i d => cases d with
    | zero => simp [predicted, quota, cost]
    | succ d => cases d with
      | zero => simp [predicted, quota, cost]
      | succ d => cases d <;> simp [predicted, quota, cost]
private theorem monotone_other (c e : Tally k) (v : Site k)
    (hle : ∀ x, c x ≤ e x) (heq : c v = e v) : predicted c v ≤ predicted e v := by
  cases v with
  | center => simp only [predicted, heq]; exact Int.add_le_add_left (rowSum_le (fun i => Int.ofNat_le.mpr (hle (.arm i 0)))) _
  | arm i d => cases d with
    | zero => simp only [predicted, heq]; have := hle .center; have := hle (.arm i 1); omega
    | succ d => simp only [predicted, heq]; have := hle (.arm i d); have := hle (.arm i (d+2)); omega
private theorem exact_of_stable (c : Tally k) (hcap : ∀ x, c x ≤ quota x)
    (hst : ∀ v, predicted c v < cost v) : ∀ v, c v = quota v := by
  have cen := hst .center
  simp only [predicted, cost] at cen
  have l1 (i : Row k) := hst (.arm i 0)
  have l2 (i : Row k) := hst (.arm i 1)
  simp [predicted, cost] at l1 l2
  -- Five or fewer center firings would force every arm to have returned
  -- at least (number of center firings - 2) chips, leaving a full batch.
  have h6 : c .center = 6 := by
    have hc := hcap .center
    simp only [quota] at hc
    by_cases h : c .center ≤ 5
    · have low (i : Row k) : (c .center : Int) - 2 ≤ c (.arm i 0) := by
        have := l1 i
        have := l2 i
        omega
      have hh := rowSum_le low
      rw [rowSum_const, Int.mul_sub, Int.mul_comm (k : Int) (c .center : Int)] at hh
      omega
    · omega
  intro v
  cases v with
  | center => exact h6
  | arm i d =>
    have h := hcap (.arm i d)
    have := l1 i
    have := l2 i
    cases d with
    | zero => simp [quota] at h ⊢; omega
    | succ d => cases d with
      | zero => simp [quota] at h ⊢; omega
      | succ d => simp only [quota] at h ⊢; omega

/-- Number of firings of each site in the unreduced chronological move list. -/
def fires (ms : List (Move k)) (v : Site k) : Nat := ms.countP (fun m => decide (m.source = v))

@[simp] theorem fires_nil (v : Site k) : fires [] v = 0 := rfl

@[simp] theorem fires_append (xs ys : List (Move k)) (v : Site k) :
    fires (xs ++ ys) v = fires xs v + fires ys v := List.countP_append

@[simp] theorem fires_singleton (m : Move k) (v : Site k) :
    fires [m] v = if m.source = v then 1 else 0 := by simp [fires]

private def bump (c : Tally k) (v : Site k) : Tally k := fun p => c p + if v = p then 1 else 0

private theorem cast_bump (c : Tally k) (v p : Site k) :
    (bump c v p : Int) = (c p : Int) + ind (v = p) := by
  by_cases h : v = p <;> simp [bump, ind, h]

private theorem predicted_step (c : Tally k) (m : Move k) (v : Site k) :
    predicted (bump c m.source) v = predicted c v + m.loadDelta v := by
  cases m with
  | center b => cases v with
    | center => simp [predicted, bump, Move.source, Move.loadDelta, Int.add_mul]; omega
    | arm i d => cases d <;> simp [predicted, bump, Move.source, Move.loadDelta] <;> omega
  | arm i d a b => cases v with
    | center => cases d with
      | zero =>
        simp only [predicted, Move.source, cast_bump, Move.loadDelta, inward,
          Site.arm.injEq, and_true,
          rowSum, sumMap_add, sum_ind_eq]
        simp [ind] <;> omega
      | succ d => simp [predicted, Move.source, bump, Move.loadDelta, inward, ind]
    | arm j e =>
      cases e <;> cases d <;>
        simp [predicted, Move.source, cast_bump, Move.loadDelta, inward, ind] <;>
        grind

private theorem extend {s t u : Config k} {xs ys : List (Move k)}
    (a : Run s xs t) (b : Run t ys u) : Run s (xs ++ ys) u := by
  induction a with
  | nil => exact b
  | cons h _ ih => exact Run.cons h (ih b)

/-- Forward induction along prefixes of a `Run`, retaining reachability of each
prefix. This is convenient since the primitive constructors are `nil`/`cons`. -/
theorem forward {P : List (Move k) → Config k → Prop}
    (z : P [] (initial k))
    (step : ∀ {ms s m}, Run (initial k) ms s → m.Legal s → P ms s → P (ms ++ [m]) (m.act s))
    {ms s} (r : Run (initial k) ms s) : P ms s := by
  have aux {s t : Config k} {xs : List (Move k)} (r : Run s xs t) :
      ∀ {ys}, Run (initial k) ys s → P ys s → P (ys ++ xs) t := by
    induction r with
    | nil => simp
    | cons h _ ih =>
      intro ys pre p
      have rs := extend pre (Run.cons h Run.nil)
      simpa using ih rs (step pre h p)
  simpa using aux r Run.nil z

/-- Unlabeled balance for every finite legal trace from the initial position. -/
theorem balance {ms : List (Move k)} {s} (r : Run (initial k) ms s) (v : Site k) :
    load s v = predicted (fires ms) v := by
  apply forward (P := fun ms s => load s v = predicted (fires ms) v) _ _ r
  · cases v with
    | center => simp [predicted, rowSum_const]
    | arm i d => cases d <;> simp [predicted]
  · intro xs t m _ h ih
    have ht : fires (xs ++ [m]) = bump (fires xs) m.source := by
      funext p; simp [bump]
    rw [ht, predicted_step, load_act h, ih]

private theorem enabled_load {ms : List (Move k)} {s} {m : Move k} (r : Run (initial k) ms s)
    (h : m.Legal s) : cost m.source ≤ load s m.source := by
  rw [(r.physical (initial_physical k)).load_eq_length]
  cases m with
  | center b => exact Int.ofNat_le.mpr (exists_center_legal_iff.mp ⟨b, h⟩)
  | arm i d a b => exact Int.ofNat_le.mpr ((exists_arm_legal_iff i d).mp ⟨a, b, h⟩)

/-- Generalized least action. Each coordinate of the comparison function need
only be stable *or* already known to majorize its firing count. The latter
option lets us study prefixes with a prescribed number of center deliveries. -/
private theorem bound {ms : List (Move k)} {s} (r : Run (initial k) ms s) (q : Tally k)
    (condition : ∀ v, predicted q v < cost v ∨ fires ms v ≤ q v) : ∀ v, fires ms v ≤ q v := by
  let P := fun (ms : List (Move k)) (_ : Config k) =>
    (∀ v, predicted q v < cost v ∨ fires ms v ≤ q v) → ∀ v, fires ms v ≤ q v
  apply forward (P := P) _ _ r condition
  · intro _ v; simp
  · intro xs u m pre hlegal ih safe v
    have prior := ih (fun p => (safe p).imp_right (by simp; omega))
    -- Only the fired site could newly exceed its bound. At equality its
    -- load before firing is at most that of the comparison odometer.
    by_cases he : m.source = v
    · subst v
      rcases safe m.source with hs | known
      · have hl := enabled_load pre hlegal
        rw [balance pre] at hl
        have hb := prior m.source
        have ne : fires xs m.source ≠ q m.source := by
          intro eq
          have := monotone_other (fires xs) q m.source prior eq
          omega
        simp; omega
      · exact known
    · simpa [he] using prior v

/-- Uniform arm budget on all prefixes whose center count does not exceed the
chosen comparison center count. `q` may be set separately for each phase. -/
theorem partial_bound (_hk : 0 < k) {ms : List (Move k)} {s}
    (r : Run (initial k) ms s) (q : Tally k)
    (ha : ∀ i d, predicted q (.arm i d) < 2) (hc : fires ms .center ≤ q .center) :
    ∀ v, fires ms v ≤ q v := by
  apply bound r q
  intro p
  cases p with
  | center => exact Or.inr hc
  | arm i d => exact Or.inl (ha i d)

/-- Upper odometer bound on every legal prefix. -/
theorem prefix_bound (hk : 0 < k) {ms : List (Move k)} {s}
    (r : Run (initial k) ms s) : ∀ v, fires ms v ≤ quota v :=
  bound r quota (fun v => Or.inl (quota_stable hk v))

/-- Every stable run from the initial state fires exactly six center batches
and exactly three level-one and one level-two comparison per arm; no site
farther out fires. This is a statement about the actual legal labeled run. -/
theorem stable_counts {ms : List (Move k)} {s} (r : Run (initial k) ms s) (st : Stable s) :
    ∀ v, fires ms v = quota v := by
  have hn := (r.physical (initial_physical k)).load_eq_length .center
  have hc := st.1
  have hk : 0 < k := by omega
  apply exact_of_stable (fires ms) (prefix_bound hk r)
  intro v; rw [← balance r]
  cases v with
  | center => exact hc
  | arm i d => have := st.2 i d; simp [cost]; omega

/-- Stable unlabeled shape: empty center, followed by exactly one chip at
levels 1, 2, 3 on each arm, with the entire infinite tail empty. -/
theorem stable_shape {ms : List (Move k)} {s} (r : Run (initial k) ms s) (st : Stable s) :
    load s .center = 0 ∧ ∀ i d, load s (.arm i d) = if d < 3 then 1 else 0 := by
  have e := funext (stable_counts r st)
  constructor
  · simp [balance r, e, predicted, quota, rowSum_const, Int.mul_comm]; omega
  · intro i d
    rw [balance r, e]
    cases d with
    | zero => rfl
    | succ d => cases d with
      | zero => rfl
      | succ d => cases d <;> simp [predicted, quota]

end Counts
end StarFiring
