import StarFiring.Padding.High
import StarFiring.Avoidance

/-! # Tracks of a 321-avoiding permutation

The high rows here are the *strict* exceedances. They are exactly the left
endpoints of inversions; records with no inversion are fixed points and are
placed on the low track. The number of inversions starting at any row is its
positive displacement (truncated subtraction). Positions and ranks are both
zero-based. -/
namespace StarFiring.Padding
variable {w : Row n → Row n}

/-- The finite rank map has every rank once when it is injective. -/
theorem perm_of_injective (hw : Function.Injective w) :
    ((List.finRange n).map w).Perm (List.finRange n) := by
  have hn : ((List.finRange n).map w).Nodup := (List.nodup_finRange n).map w (fun _ _ h e => h (hw e))
  apply (List.perm_ext_iff_of_nodup hn (List.nodup_finRange n)).mpr
  intro i; simp only [List.mem_finRange, iff_true]
  apply Classical.byContradiction; intro hmissing
  have bigger := List.nodup_cons.mpr ⟨hmissing, hn⟩
  have := bigger.length_le_of_subset (l₂ := List.finRange n) (fun a _ => List.mem_finRange a)
  simp at this; omega

/-- A rank is the number of its strict predecessors. -/
theorem count_lt_finRange (i : Row n) :
    (List.finRange n).countP (fun j => decide (j < i)) = i.val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [List.finRange_succ]; simpa [List.countP_cons, Function.comp_def] using
        congrArg Nat.succ (ih j)

/-- The same threshold count in permuted order. -/
theorem count_lt_rank (hw : Function.Injective w) (i : Row n) :
    (List.finRange n).countP (fun j => decide (w j < w i)) = (w i).val := by
  have h := (perm_of_injective hw).countP_eq (fun x => decide (x < w i))
  simpa only [List.countP_map, Function.comp_def, count_lt_finRange] using h

/-- A strict exceedance must invert some later position, even without avoidance. -/
theorem exists_inv_of_high (hw : Function.Injective w) {i : Row n} (hi : High w i) :
    ∃ j, i < j ∧ w j < w i := by
  apply Classical.byContradiction; intro no
  have h := List.countP_mono_left (l := List.finRange n)
    (p := fun j => decide (w j < w i)) (q := fun j => decide (j < i)) (by
      intro j _ h
      simp only [decide_eq_true_eq] at h ⊢
      have hne : j ≠ i := fun e => Fin.ne_of_lt h (congrArg w e)
      have hn : ¬i < j := fun hj => no ⟨j, hj, h⟩
      simp only [ne_eq, Fin.lt_def, Fin.ext_iff] at *; omega)
  rw [count_lt_rank hw, count_lt_finRange] at h
  exact Nat.not_lt_of_ge h hi

/-- An inversion top must be a record, since an earlier greater value would
complete a decreasing triple. -/
theorem record_of_inv (hw : Function.Injective w) (ha : Avoids321 w)
    {i j : Row n} (hij : i < j) (hji : w j < w i) {p : Row n} (hpi : p < i) : w p < w i := by
  have hn := ha p i j hpi hij hji
  have hne : w p ≠ w i := fun e => Fin.ne_of_lt hpi (hw e)
  simp only [ne_eq, Fin.lt_def, Fin.ext_iff] at *; omega

theorem high_record (hw : Function.Injective w) (ha : Avoids321 w)
    {i j : Row n} (hi : High w i) (hji : j < i) : w j < w i := by
  obtain ⟨p, hip, hpi⟩ := exists_inv_of_high hw hi
  exact record_of_inv hw ha hip hpi hji

/-- At a record, its smaller ranks split into all earlier rows and precisely
those later rows inverted by the record. -/
private theorem record_split (hw : Function.Injective w) {i : Row n}
    (rec : ∀ j, j < i → w j < w i) :
    (w i).val = i.val + (List.finRange n).countP (fun j => decide (i < j ∧ w j < w i)) := by
  rw [← count_lt_rank hw, ← count_lt_finRange i]
  generalize List.finRange n = l
  induction l with
  | nil => simp
  | cons j l ih =>
    by_cases h : j < i
    · have := rec j h
      have := Fin.not_lt.mpr (Fin.le_of_lt h)
      simp [*]; omega
    · by_cases he : j = i
      · subst j; simp [ih]
      · have hij : i < j := by simp only [Fin.lt_def, Fin.ext_iff] at *; omega
        by_cases hr : w j < w i <;> simp [*] <;> omega

theorem high_of_inv (hw : Function.Injective w) (ha : Avoids321 w)
    {i j : Row n} (hij : i < j) (hji : w j < w i) : High w i := by
  have hs := record_split hw (fun _ h => record_of_inv hw ha hij hji h)
  have hp : 0 < (List.finRange n).countP (fun j => decide (i < j ∧ w j < w i)) :=
    List.countP_pos_iff.mpr ⟨j, List.mem_finRange j, decide_eq_true ⟨hij, hji⟩⟩
  change i.val < (w i).val; omega

theorem high_iff_inv (hw : Function.Injective w) (ha : Avoids321 w) (i : Row n) :
    High w i ↔ ∃ j, i < j ∧ w j < w i :=
  ⟨exists_inv_of_high hw, fun ⟨_, h, h'⟩ => high_of_inv hw ha h h'⟩

theorem high_inc (hw : Function.Injective w) (ha : Avoids321 w) {i j : Row n}
    (_hi : High w i) (hj : High w j) (hij : i < j) : w i < w j := high_record hw ha hj hij

theorem low_inc (hw : Function.Injective w) (ha : Avoids321 w) {i j : Row n}
    (hi : ¬High w i) (_hj : ¬High w j) (hij : i < j) : w i < w j := by
  have hn : ¬w j < w i := fun h => hi (high_of_inv hw ha hij h)
  have hne : w i ≠ w j := fun e => Fin.ne_of_lt hij (hw e)
  simp only [ne_eq, Fin.lt_def, Fin.ext_iff] at *; omega

/-- The number of inversions with a given left endpoint equals the positive
part of its rank displacement. Thus bounding single-row displacement bounds
the cardinality of every anchored family of later smaller rows. -/
theorem count_later_smaller (hw : Function.Injective w) (ha : Avoids321 w) (i : Row n) :
    (List.finRange n).countP (fun j => decide (i < j ∧ w j < w i)) = (w i).val - i.val := by
  by_cases hi : High w i
  · have h := record_split hw (fun _ h => high_record hw ha hi h); omega
  · have h := Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hi)
    rw [h, List.countP_eq_zero]
    intro j _ hj; obtain ⟨h1,h2⟩ := of_decide_eq_true hj
    exact hi (high_of_inv hw ha h1 h2)

end StarFiring.Padding
