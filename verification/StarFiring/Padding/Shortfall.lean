import StarFiring.Padding.Match
import StarFiring.Padding.Tracks

/-! # Paying the original rows' shortfall

Work with a Boolean predicate on source rows: a row is cheap if its fourth
input (the ordinary return, or its replacement spare) lies below the target.
In particular this bookkeeping does not require constructing a baseline
multiset of labels. -/
namespace StarFiring.Padding

private theorem first_witness {P : Row n → Prop} [DecidablePred P] (h : ∃ k, P k) :
    ∃ e, P e ∧ ∀ k, P k → e ≤ k := by
  let l := (List.finRange n).filter (fun k => decide (P k))
  have mem (k : Row n) : k ∈ l ↔ P k := by simp [l]
  obtain ⟨k, hk⟩ := h
  have hne := List.ne_nil_of_mem ((mem k).mpr hk)
  exact ⟨l.min hne, (mem _).mp (List.min_mem hne),
    fun j hj => List.min_le_of_mem ((mem j).mpr hj)⟩

private theorem count_prefix (i : Row n) :
    (List.finRange n).countP (fun j => decide (j ≤ i)) = i.val + 1 := by
  simpa only [Fin.le_def, Nat.zero_le, true_and, Nat.lt_succ_iff,
    Nat.min_eq_right (Nat.succ_le_of_lt i.isLt), Nat.min_zero, Nat.sub_zero] using
    countFinInterval n 0 (i.val + 1)

/-- A one-row counting rule. A and B give one request apiece. B always has
credit C; A can use C or D; whenever both request, D is available for A. -/
private theorem charge_two (l : List α) (A B C D : α → Bool)
    (hA : ∀ p, A p → C p ∨ D p) (hB : ∀ p, B p → C p)
    (hAB : ∀ p, A p → B p → D p) :
    l.countP A + l.countP B ≤ l.countP C + l.countP D := by
  induction l with
  | nil => simp
  | cons p _ ih =>
    simp only [List.countP_cons]
    have := hA p
    have := hB p
    have := hAB p
    cases h1 : A p <;> cases h2 : B p <;> cases h3 : C p <;> cases h4 : D p <;>
      simp_all <;> omega

/-- The disjoint-credit estimate underlying the padding construction. A row
that is both in the original prefix and a matched suffix source necessarily
lies among the later smaller entries of the first larger high. -/
theorem shortfall {w : Row n → Row n} {t : Nat}
    (hw : Function.Injective w) (ha : Avoids321 w) (ht : U w ≤ t)
    (i : Row n) (cheap : Row n → Bool)
    (base : ∀ p, p ≤ i → (High w p ∨ ∀ e, e < p → High w e → w e < w i) → cheap p)
    (replayed : ∀ p, (matchValue w p).isSome → cheap p) :
    i.val < t + (List.finRange n).countP cheap := by
  let large (k : Row n) : Prop := k < i ∧ High w k ∧ w i < w k
  have earlier {p k : Row n} (hpi : p ≤ i) (hkp : k < p) (hk : High w k)
      (h : ¬large k) : w k < w i := by
    have hki : k < i := Nat.lt_of_lt_of_le hkp hpi
    have hne : w k ≠ w i := fun eq => (Fin.ne_of_lt hki) (hw eq)
    simp only [large, hki, hk, true_and] at h
    exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt h) (fun eq => hne (Fin.ext eq))
  by_cases h : ∃ e, large e
  · obtain ⟨e, he, hmin⟩ := first_witness h
    obtain ⟨hei, heH, hval⟩ := he
    have ilow : ¬High w i := fun hi => (Nat.not_lt_of_ge (Nat.le_of_lt hval)) (high_record hw ha hi hei)
    have leftCheap {p : Row n} (hpi : p ≤ i) (hpe : p ≤ e) : cheap p := by
      apply base p hpi (.inr ?_)
      intro k hkp hk
      exact earlier hpi hkp hk fun h => Nat.not_le_of_lt (Nat.lt_of_lt_of_le hkp hpe) (hmin k h)
    have afterSmall {p : Row n} (hpi : p ≤ i) (hep : e < p) (hl : ¬High w p) :
        e < p ∧ w p < w e := by
      refine ⟨hep, ?_⟩
      by_cases eq : p = i
      · simpa [eq] using hval
      · have hlt : p < i := by
          simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff] at eq hpi ⊢
          omega
        exact Fin.lt_trans (low_inc hw ha hl ilow hlt) hval
    have hc := charge_two (List.finRange n) (fun p => decide (p ≤ i))
      (fun p => decide (e < p) && (matchValue w p).isSome) cheap
      (fun p => decide (e < p ∧ w p < w e)) (by
        intro p hp
        have hpi : p ≤ i := of_decide_eq_true hp
        by_cases hpe : p ≤ e
        · exact .inl (leftCheap hpi hpe)
        by_cases hl : High w p
        · exact .inl (base p hpi (.inl hl))
        · exact .inr (decide_eq_true (afterSmall hpi (Nat.lt_of_not_ge hpe) hl))) (by
        intro p h; exact replayed p (Bool.and_eq_true_iff.mp h).2) (by
        intro p hp h
        obtain ⟨ha, hm⟩ := Bool.and_eq_true_iff.mp h
        exact decide_eq_true (afterSmall (of_decide_eq_true hp) (of_decide_eq_true ha) (matchValue_isSome_low hm)))
    have hecap := excess_le heH ht
    rw [matchValue_suffix_count heH] at hecap
    rw [count_later_smaller hw ha] at hc
    rw [count_prefix] at hc
    simp only [Row] at hc hecap ⊢
    omega
  · have hc : (List.finRange n).countP (fun p => decide (p ≤ i)) ≤ (List.finRange n).countP cheap := by
      apply List.countP_mono_left
      intro p _ hp
      have hpi : p ≤ i := of_decide_eq_true hp
      exact base p hpi (.inr (fun k hkp hk => earlier hpi hkp hk (fun hl => h ⟨k, hl⟩)))
    rw [count_prefix] at hc
    simp only [Row] at hc ⊢
    omega

end StarFiring.Padding
