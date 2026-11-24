import StarFiring.Padding.High

/-! # The gap statistic of a permutation

Rows and values here are zero-based. There is no need to index a second
list of excedances: the arguments `i` to the gap and suffix functions are
original rows, and only high arguments contribute to `U`. Both terminal
sentinels are therefore `n`, not `n+1`. On an avoider the values at the
high rows increase, so the next high *position* supplies the endpoint of
both the position gap and the corresponding value gap. -/
namespace StarFiring.Padding

variable {n : Nat}

private def laterPos (w : Fin n → Fin n) (i : Fin n) : List Nat :=
  ((List.finRange n).filter (fun j => decide (i < j ∧ High w j))).map Fin.val

private theorem mem_laterPos {w : Fin n → Fin n} {i : Fin n} {x : Nat} :
    x ∈ laterPos w i ↔ ∃ j : Fin n, i < j ∧ High w j ∧ j.val = x := by
  simp [laterPos, and_assoc]

/-- Next high position, with `n` for the missing final endpoint. -/
def nextPos (w : Fin n → Fin n) (i : Fin n) : Nat :=
  (n :: laterPos w i).min (by simp)

private theorem nextPos_cases (w : Fin n → Fin n) (i : Fin n) :
    nextPos w i = n ∨ ∃ j : Fin n, i < j ∧ High w j ∧ j.val = nextPos w i := by
  have hm : nextPos w i ∈ n :: laterPos w i := List.min_mem _
  simpa only [List.mem_cons, mem_laterPos] using hm

theorem lt_nextPos (w : Fin n → Fin n) (i : Fin n) : i.val < nextPos w i := by
  rcases nextPos_cases w i with he | ⟨j, hij, _, he⟩
  · simpa only [he] using i.isLt
  · exact he ▸ hij

theorem nextPos_le_n (w : Fin n → Fin n) (i : Fin n) : nextPos w i ≤ n :=
  List.min_le_of_mem (List.mem_cons_self (a := n) (l := laterPos w i))

theorem nextPos_le_of_high {w : Fin n → Fin n} {i h : Fin n} (hih : i < h) (hh : High w h) :
    nextPos w i ≤ h.val :=
  List.min_le_of_mem (List.mem_cons_of_mem n (mem_laterPos.mpr ⟨h, hih, hh, rfl⟩))

theorem high_nextPos {w : Fin n → Fin n} {i : Fin n} (h : nextPos w i < n) :
    High w ⟨nextPos w i, h⟩ := by
  rcases nextPos_cases w i with he | ⟨j, _, hj, he⟩
  · omega
  · have eqj : j = ⟨nextPos w i, h⟩ := Fin.ext he
    exact eqj ▸ hj

theorem not_high_between {w : Fin n → Fin n} {i a : Fin n}
    (hia : i < a) (ha : a.val < nextPos w i) : ¬ High w a :=
  fun hh => Nat.not_le_of_lt ha (nextPos_le_of_high hia hh)

/-- Value at the next high, or the upper value sentinel `n`. -/
def nextVal (w : Fin n → Fin n) (i : Fin n) : Nat :=
  if h : nextPos w i < n then (w ⟨_, h⟩).val else n

theorem nextVal_of_lt {w : Fin n → Fin n} {i : Fin n} (h : nextPos w i < n) :
    nextVal w i = (w ⟨nextPos w i, h⟩).val := by simp [nextVal, h]

theorem nextVal_of_eq {w : Fin n → Fin n} {i : Fin n} (h : nextPos w i = n) :
    nextVal w i = n := by simp [nextVal, h]

theorem nextVal_le_n (w : Fin n → Fin n) (i : Fin n) : nextVal w i ≤ n := by
  unfold nextVal
  split <;> omega

theorem val_lt_nextVal {w : Fin n → Fin n} {i : Fin n} (hi : High w i)
    (hinc : ∀ a b, a < b → High w a → High w b → w a < w b) :
    (w i).val < nextVal w i := by
  unfold nextVal
  split
  next h => exact hinc i _ (lt_nextPos w i) hi (high_nextPos h)
  next => exact (w i).isLt

theorem nextVal_le_of_high {w : Fin n → Fin n} {i h : Fin n} (hih : i < h) (hh : High w h)
    (hinc : ∀ a b, a < b → High w a → High w b → w a < w b) :
    nextVal w i ≤ (w h).val := by
  have hp := nextPos_le_of_high hih hh
  have hn : nextPos w i < n := by omega
  let j : Fin n := ⟨nextPos w i, hn⟩
  rw [nextVal_of_lt hn]
  change (w j).val ≤ (w h).val
  by_cases he : nextPos w i = h.val
  · have ej : j = h := Fin.ext he
    simp [ej]
  · exact Nat.le_of_lt (hinc j h (show j.val < h.val by change nextPos w i < _; omega)
      (high_nextPos hn) hh)

/-- Number of low positions skipped before the next high. -/
def gapB (w : Fin n → Fin n) (i : Fin n) := nextPos w i - i.val - 1
/-- Number of skipped values in the corresponding high-value gap. -/
def gapC (w : Fin n → Fin n) (i : Fin n) := nextVal w i - (w i).val - 1
/-- Reused chips contributed by this pair of gaps. -/
def gapR (w : Fin n → Fin n) (i : Fin n) := min (gapB w i) (gapC w i)

theorem gapR_le_gapB (w : Fin n → Fin n) (i : Fin n) : gapR w i ≤ gapB w i := Nat.min_le_left ..
theorem gapR_le_gapC (w : Fin n → Fin n) (i : Fin n) : gapR w i ≤ gapC w i := Nat.min_le_right ..

/-- Number of reuses in gaps beginning at or after the indicated position. -/
def suffixR (w : Fin n → Fin n) (i : Fin n) : Nat :=
  ((List.finRange n).map (fun h => if i ≤ h ∧ High w h then gapR w h else 0)).sum

/-- Excedance-gap bound on identity padding.
Natural subtraction is harmless since the maximum includes zero. -/
def U (w : Fin n → Fin n) : Nat :=
  (0 :: (((List.finRange n).filter (fun i => decide (High w i))).map
    (fun i => (w i).val - i.val - suffixR w i))).max (by simp)

theorem U_le_iff {w : Fin n → Fin n} {t : Nat} :
    U w ≤ t ↔ ∀ i, High w i → (w i).val ≤ i.val + suffixR w i + t := by
  unfold U
  rw [List.max_le_iff]
  simp only [List.mem_cons, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq, forall_eq_or_imp, Nat.zero_le, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, true_and]
  constructor
  · intro H i hi
    have hh := H i hi
    omega
  · intro H i hi
    have hh := H i hi
    omega

theorem excess_le {w : Fin n → Fin n} {i : Fin n} {t : Nat} (h : High w i) (ht : U w ≤ t) :
    (w i).val ≤ i.val + suffixR w i + t := U_le_iff.mp ht i h

/-- No gap contributes in the absence of high rows. This includes `n = 0`. -/
theorem U_eq_zero_of_no_high {w : Fin n → Fin n} (h : ∀ i, ¬High w i) : U w = 0 :=
  Nat.eq_zero_of_le_zero (U_le_iff.mpr (fun i hi => False.elim (h i hi)))

theorem U_le_pred (w : Fin n → Fin n) : U w ≤ n-1 :=
  U_le_iff.mpr (fun i _ => by have := (w i).isLt; omega)


/-- Count a half-open interval, clipping endpoints at the finite universe. -/
theorem countFinInterval (n lo hi : Nat) :
    (List.finRange n).countP (fun a => decide (lo ≤ a.val ∧ a.val < hi)) =
    min n hi - min n lo := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.countP_append, List.countP_map]
    change ((List.finRange n).countP (fun a => decide (lo ≤ a.val ∧ a.val < hi))) + _ = _
    rw [ih]; simp only [List.countP_singleton, decide_eq_true_eq, Fin.val_last]; split <;> omega

/-- A terminal block of the `r` positions immediately below `q` has cardinal `r`. -/
theorem countFinRightBlock {n q r : Nat} (hr : r ≤ q) (hq : q ≤ n) :
    (List.finRange n).countP (fun a => decide (q-r ≤ a.val ∧ a.val < q)) = r := by
  rw [countFinInterval]; omega

private theorem countP_or_eq_add {α : Type u} (xs : List α) (p q : α → Bool)
    (disjoint : ∀ x, p x = true → ¬q x = true) :
    xs.countP (fun x => p x || q x) = xs.countP p + xs.countP q := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons, ih]
    have := disjoint a
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

private theorem countP_by_disjoint_rows {α : Type u} {β : Type v}
    (R : α → β → Bool) (ys : List β) (xs : List α) (nd : xs.Nodup)
    (uniq : ∀ a h j, R h a = true → R j a = true → h = j) :
    (xs.map (fun h => ys.countP (R h))).sum =
      ys.countP (fun a => xs.any (fun h => R h a)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hne,hnd⟩ := List.nodup_cons.mp nd
    simp only [List.map_cons, List.sum_cons, List.any_cons]
    rw [ih hnd, countP_or_eq_add]
    intro a hx hxs
    obtain ⟨j, hj, hja⟩ := List.any_eq_true.mp hxs
    exact hne (uniq a x j hx hja ▸ hj)

/-- Sum row-wise fiber sizes when each column belongs to at most one fiber. -/
theorem sum_countP_fibers {n : Nat} (ys : List β) (R : Fin n → β → Bool)
    (uniq : ∀ a h j, R h a = true → R j a = true → h = j) :
    ((List.finRange n).map (fun h => ys.countP (R h))).sum =
       ys.countP (fun a => decide (∃ h, R h a = true)) := by
  rw [countP_by_disjoint_rows R ys _ (List.nodup_finRange _) uniq]
  apply List.countP_congr; intros; simp

end StarFiring.Padding
