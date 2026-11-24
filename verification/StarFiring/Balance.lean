import StarFiring.Core

/-! Forgetting labels turns each legal firing into the usual discrete Laplacian
on the star.  The only use of legality in computing a load change is that a
center batch has no repeated label. -/
namespace StarFiring

def Move.loadDelta (m : Move k) (t : Site k) : Int := match m with
  | .center _ => match t with
    | .center => -(k : Int)
    | .arm _ 0 => 1
    | .arm _ (_+1) => 0
  | .arm i d _ _ => ind (t = inward i d) + ind (t = .arm i (d+1)) - 2 * ind (t = .arm i d)

private theorem sum_ind_filter (xs : List α) (p : α → Prop) [DecidablePred p] :
    (xs.map (fun x => ind (p x))).sum = ((xs.filter (fun x => decide (p x))).length : Int) := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases hx : p x <;> simp [hx, ind, ih, Int.add_comm] at *

theorem sum_ind_eq (x : Fin n) :
    ((List.finRange n).map (fun y => ind (x = y))).sum = 1 := by
  rw [sum_ind_filter]
  have hp : List.Perm ((List.finRange n).filter (fun y => decide (x = y))) [x] := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange n).filter _) (by simp)).mpr
    intro z
    simp [List.mem_finRange, eq_comm]
  simpa using congrArg Int.ofNat hp.length_eq

/-- Count a strictly increasing batch in the universe of labels. -/
theorem sum_ind_has (b : Batch k) (hb : Increasing b) :
    ((List.finRange (3*k)).map (fun x => ind (Has b x))).sum = k := by
  rw [sum_ind_filter]
  have inj : ∀ i j, b i = b j → i = j := by
    intro i j heq
    by_cases h : i < j
    · exact False.elim (Fin.ne_of_lt (hb i j h) heq)
    · by_cases h' : j < i
      · exact False.elim (Fin.ne_of_lt (hb j i h') heq.symm)
      · apply Fin.ext
        change ¬ i.val < j.val at h
        change ¬ j.val < i.val at h'
        omega
  have hn : ((List.finRange k).map b).Nodup :=
    (List.nodup_finRange k).map b (fun i j h he => h (inj i j he))
  have hp : List.Perm ((List.finRange (3*k)).filter (fun x => decide (Has b x)))
      ((List.finRange k).map b) := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) hn).mpr
    intro x
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, List.mem_map]
    rfl
  simpa using congrArg Int.ofNat hp.length_eq

theorem sumMap_add (xs : List α) (f g : α → Int) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs <;> simp_all <;> omega

private theorem sumMap_sub (xs : List α) (f g : α → Int) :
    (xs.map (fun x => f x - g x)).sum = (xs.map f).sum - (xs.map g).sum := by
  induction xs <;> simp_all <;> omega

private theorem sumMap_neg (xs : List α) (f : α → Int) :
    (xs.map (fun x => - f x)).sum = -(xs.map f).sum := by
  induction xs <;> simp_all <;> omega

private theorem sumMap_mul (xs : List α) (c : Int) (f : α → Int) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs <;> simp_all [Int.mul_add]

theorem load_act {m : Move k} {s : Config k} (hm : m.Legal s) (t : Site k) :
    load (m.act s) t = load s t + m.loadDelta t := by
  unfold load Move.act
  rw [sumMap_add]
  apply congrArg (_ + ·)
  cases m with
  | center b =>
    cases t with
    | center => exact (sumMap_neg _ _).trans (congrArg Neg.neg (sum_ind_has b hm.1))
    | arm i d => cases d with
      | zero => exact sum_ind_eq _
      | succ d =>
        change ((List.finRange (3*k)).map (fun _ => (0 : Int))).sum = 0
        simp [List.map_const']
  | arm i d a b =>
    change ((List.finRange (3*k)).map (fun x => ind (t = inward i d) * ind (a = x) +
      ind (t = .arm i (d+1)) * ind (b = x) - ind (t = .arm i d) * (ind (a = x) + ind (b = x)))).sum = _
    simp only [Move.loadDelta, sumMap_sub, sumMap_add, sumMap_mul, sum_ind_eq,
      Int.mul_one]
    omega

@[simp] theorem load_initial_center (k : Nat) : load (initial k) .center = 3 * (k : Int) := by
  change ((List.finRange (3*k)).map (fun _ => (1 : Int))).sum = 3 * (k : Int)
  simp [List.map_const', Int.natCast_mul]

@[simp] theorem load_initial_arm (i : Row k) (d : Nat) : load (initial k) (.arm i d) = 0 := by
  change ((List.finRange (3*k)).map (fun _ => (0 : Int))).sum = 0
  simp [List.map_const']

private theorem sumMap_le (xs : List α) (f g : α → Int) (h : ∀ x, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => exact Int.add_le_add (h x) ih

/-- A legal center firing has its unlabeled threshold available. -/
theorem legal_center_load_ge {s : Config k} {b : Batch k}
    (hn : ∀ t x, 0 ≤ s t x) (hm : (Move.center b).Legal s) : (k : Int) ≤ load s .center := by
  rw [← sum_ind_has b hm.1]
  apply sumMap_le
  intro x
  by_cases hx : Has b x
  · obtain ⟨i, hi⟩ := hx
    have hs := hm.2 i
    rw [hi] at hs
    simp [ind, show Has b x from ⟨i, hi⟩]
    omega
  · simpa [ind, hx] using hn .center x

/-- A legal arm firing has its unlabeled threshold available. -/
theorem legal_arm_load_ge {s : Config k} {i : Row k} {d : Nat} {a b : Chip k}
    (hn : ∀ t x, 0 ≤ s t x) (hm : (Move.arm i d a b).Legal s) : 2 ≤ load s (.arm i d) := by
  have ne := Fin.ne_of_lt hm.1
  have h : ∀ x, ind (a = x) + ind (b = x) ≤ s (.arm i d) x := by
    intro x
    by_cases hax : a = x
    · subst x; have := hm.2.1; simp [ind, Ne.symm ne]; omega
    · by_cases hbx : b = x
      · subst x; have := hm.2.2; simp [ind, ne]; omega
      · simpa [ind, hax, hbx] using hn (.arm i d) x
  have hs := sumMap_le (List.finRange (3*k)) _ _ h
  rw [sumMap_add, sum_ind_eq, sum_ind_eq] at hs
  exact hs

/-- Legal moves cannot create debt when all incidences were nonnegative. -/
theorem nonneg_act {s : Config k} {m : Move k} (hn : ∀ t x, 0 ≤ s t x) (hm : m.Legal s) :
    ∀ t x, 0 ≤ m.act s t x := by
  intro t x
  have h := hn t x
  cases m with
  | center b =>
    cases t with
    | center =>
      by_cases hx : Has b x
      · obtain ⟨i, hi⟩ := hx
        have hs := hm.2 i
        rw [hi] at hs
        simp [Move.act, Move.delta, ind, show Has b x from ⟨i, hi⟩]
        omega
      · simpa [Move.act, Move.delta, ind, hx] using h
    | arm i d =>
      cases d with
      | zero => by_cases hx : b i = x <;> simp [Move.act, Move.delta, ind, hx] <;> omega
      | succ d => simpa [Move.act, Move.delta] using h
  | arm i d a b =>
    have ne := Fin.ne_of_lt hm.1
    have hs : ind (t = .arm i d) * (ind (a = x) + ind (b = x)) ≤ s t x := by
      by_cases ht : t = .arm i d
      · subst t
        by_cases ha : a = x
        · subst x; have := hm.2.1; simp [ind, Ne.symm ne]; omega
        · by_cases hb : b = x
          · subst x; have := hm.2.2; simp [ind, ne]; omega
          · simpa [ind, ha, hb] using h
      · simpa [ind, ht] using h
    have hpos (p : Prop) [Decidable p] : 0 ≤ ind p := by by_cases h' : p <;> simp [ind, h']
    have := Int.mul_nonneg (hpos (t = inward i d)) (hpos (a = x))
    have := Int.mul_nonneg (hpos (t = .arm i (d+1))) (hpos (b = x))
    simp only [Move.act, Move.delta]
    omega

theorem initial_nonneg (t : Site k) (x : Chip k) : 0 ≤ initial k t x := by
  by_cases h : t = .center <;> simp [initial, ind, h]

theorem Run.nonneg {s t : Config k} {ms : List (Move k)} (r : Run s ms t) :
    (∀ p x, 0 ≤ s p x) → ∀ p x, 0 ≤ t p x := by
  induction r with
  | nil => exact id
  | cons hm _ ih => exact fun hn => ih (nonneg_act hn hm)

/-- Nonnegative incidences have nonnegative site loads. -/
theorem load_nonneg {s : Config k} (hn : ∀ p x, 0 ≤ s p x) (p : Site k) : 0 ≤ load s p := by
  have h := sumMap_le (List.finRange (3*k)) (fun _ => 0) (s p) (hn p)
  simpa [load, List.map_const'] using h

end StarFiring
