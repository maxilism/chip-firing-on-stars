import Std

/-! Ranking and sorting for the padding construction. Counting labels below a
threshold does both jobs: it standardizes an arbitrary finite ordered alphabet
and characterizes the row occupied by a sorted batch entry. -/
namespace StarFiring.Padding.Rank

section Alphabet

variable {α : Type u} [DecidableEq α] (lt : α → α → Prop) [DecidableRel lt]

private def below (alphabet : List α) (x : α) := alphabet.countP (fun a => decide (lt a x))

omit [DecidableEq α] in
private theorem below_bound {alphabet : List α} {x : α} (hx : x ∈ alphabet) (hirr : ¬ lt x x) :
    below lt alphabet x < alphabet.length := by
  apply Nat.lt_of_le_of_ne List.countP_le_length
  intro h
  exact hirr (of_decide_eq_true ((List.countP_eq_length.mp h) x hx))

private theorem below_strict (trans : ∀ {a b c}, lt a b → lt b c → lt a c)
    {alphabet : List α} {x y : α} (hx : x ∈ alphabet) (hirr : ¬ lt x x) (hxy : lt x y) :
    below lt alphabet x < below lt alphabet y := by
  let tail := alphabet.erase x
  have hperm : alphabet.Perm (x :: tail) := List.perm_cons_erase hx
  have mono : below lt tail x ≤ below lt tail y := by
    apply List.countP_mono_left
    intro a _ ha; exact decide_eq_true (trans (of_decide_eq_true ha) hxy)
  unfold below at *
  rw [hperm.countP_eq (fun a => decide (lt a x)), hperm.countP_eq (fun a => decide (lt a y))]
  simp [hirr, hxy]; omega

/-- Replace the members of an arbitrary list of distinct ordered labels by
`Fin N`, preserving and reflecting strict order. The arbitrary value outside
the given alphabet is immaterial. -/
theorem standardizeWith (irrefl : ∀ a, ¬ lt a a)
    (trans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (compare : ∀ a b, lt a b ∨ a = b ∨ lt b a)
    {alphabet : List α} {N : Nat} (nd : alphabet.Nodup) (len : alphabet.length = N) (hN : 0 < N) :
    ∃ rank : α → Fin N,
      (∀ a ∈ alphabet, ∀ b ∈ alphabet, rank a < rank b ↔ lt a b) ∧
      (alphabet.map rank).Perm (List.finRange N) := by
  let rank : α → Fin N := fun a =>
    if h : a ∈ alphabet then ⟨below lt alphabet a, len ▸ below_bound lt h (irrefl a)⟩ else ⟨0,hN⟩
  have mono {a b} (ha : a ∈ alphabet) (hb : b ∈ alphabet) (hab : lt a b) : rank a < rank b := by
    simpa only [rank, dite_eq_left ha, dite_eq_left hb, Fin.lt_def] using below_strict lt trans ha (irrefl _) hab
  refine ⟨rank, ?_, ?_⟩
  · intro a ha b hb
    refine ⟨?_, mono ha hb⟩
    intro h
    rcases compare a b with lt' | rfl | gt
    · exact lt'
    · exact False.elim (Fin.lt_irrefl _ h)
    · exact False.elim (Fin.not_lt.mpr (Fin.le_of_lt (mono hb ha gt)) h)
  · have nr : (alphabet.map rank).Nodup := by
      apply List.pairwise_map.mpr
      apply nd.imp_of_mem
      intro a b ha hb ne eq
      rcases compare a b with h | h | h
      · exact Fin.ne_of_lt (mono ha hb h) eq
      · exact ne h
      · exact Fin.ne_of_lt (mono hb ha h) eq.symm
    apply (List.perm_ext_iff_of_nodup nr (List.nodup_finRange _)).mpr
    intro i; simp only [List.mem_finRange, iff_true]
    apply Classical.byContradiction; intro hm
    have hn := List.nodup_cons.mpr ⟨hm,nr⟩
    have bound := hn.length_le_of_subset (l₂ := List.finRange N) (fun a _ => List.mem_finRange a)
    simp [len] at bound; omega

end Alphabet

/-- Natural-label version used to construct `Chip k` batches (`N = 3*k`). -/
theorem standardize {alphabet : List Nat} {N : Nat} (nd : alphabet.Nodup)
    (len : alphabet.length = N) (hN : 0 < N) :
    ∃ rank : Nat → Fin N,
      (∀ a ∈ alphabet, ∀ b ∈ alphabet, rank a < rank b ↔ a < b) ∧
      (alphabet.map rank).Perm (List.finRange N) :=
  standardizeWith (· < ·) Nat.lt_irrefl Nat.lt_trans Nat.lt_trichotomy nd len hN

abbrev col (f : Fin n → α) := (List.finRange n).map f

private def sorted (xs : List Nat) := xs.mergeSort (fun a b => decide (a ≤ b))

private theorem sorted_le (xs : List Nat) : (sorted xs).Pairwise (· ≤ ·) := by
  have h := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (by intro a b c; simp only [decide_eq_true_eq]; exact Nat.le_trans)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total _ _) xs
  simpa only [sorted, decide_eq_true_eq] using h

/-- The batch obtained by sorting the input labels in increasing row order. -/
def sortColumn (f : Fin n → Nat) (i : Fin n) : Nat :=
  (sorted (col f))[i.val]'(by simp [sorted])

private theorem sortColumn_col (f : Fin n → Nat) : col (sortColumn f) = sorted (col f) := by
  apply List.ext_getElem
  · simp [sorted]
  · intro i hi hj; simp [sortColumn]

theorem sortColumn_perm (f : Fin n → Nat) : (col f).Perm (col (sortColumn f)) := by
  rw [sortColumn_col]; exact (List.mergeSort_perm ..).symm

theorem sortColumn_inc {f : Fin n → Nat} (h : (col f).Nodup) :
    ∀ i j, i < j → sortColumn f i < sortColumn f j := by
  have nd : (sorted (col f)).Nodup := (List.mergeSort_perm ..).symm.nodup h
  have lt : (sorted (col f)).Pairwise (· < ·) :=
    ((sorted_le _).and nd).imp fun h => Nat.lt_of_le_of_ne h.1 h.2
  intro i j hij
  apply List.Pairwise.rel_getElem_of_lt _ _ lt hij

private theorem getElem_lt_iff_countP {xs : List Nat} (hs : xs.Pairwise (· ≤ ·))
    (i : Nat) (hi : i < xs.length) (z : Nat) :
    xs[i] < z ↔ i < xs.countP (fun a => decide (a < z)) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    have hle := (List.pairwise_cons.mp hs).1
    have hs' := (List.pairwise_cons.mp hs).2
    by_cases ha : a < z
    · cases i with
      | zero => simp [ha]
      | succ i => simpa [List.countP_cons, ha] using ih hs' i (by simpa using hi)
    · have none : ∀ b ∈ as, ¬ b < z := fun b hb h => ha (Nat.lt_of_le_of_lt (hle _ hb) h)
      have zero : as.countP (fun b => decide (b < z)) = 0 :=
        List.countP_eq_zero.mpr fun b hb h => none _ hb (of_decide_eq_true h)
      cases i with
      | zero => simp [ha, zero]
      | succ i =>
        have notlt := none (as[i]'(by simpa using hi)) (List.getElem_mem ..)
        simp [ha, zero, notlt]

/-- The `i`th sorted batch entry is below threshold `z` exactly when at least
`i.val + 1` batch labels lie below `z`, counting occurrences. -/
theorem sortColumn_lt_iff (f : Fin n → Nat) (i : Fin n) (z : Nat) :
    sortColumn f i < z ↔ i.val < (col f).countP (fun a => decide (a < z)) := by
  exact (getElem_lt_iff_countP (sorted_le _) _ _ z).trans (by
    unfold sorted; rw [(List.mergeSort_perm (col f) _).countP_eq])

end StarFiring.Padding.Rank
