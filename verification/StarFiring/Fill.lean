import StarFiring.Core

/-! Assigning leftover labels to two complementary classes of rows. No sorting
or disjointness assumption on the supplied labels is needed for the assignment. -/
namespace StarFiring

/-- Values prescribed along any list of distinct indices extend to a function
on all indices. `fallback` makes no inhabitance assumption necessary. -/
private theorem fill_nodup {α β : Type} [DecidableEq α] (is : List α) (vs : List β)
    (fallback : α → β) (hi : is.Nodup) (hl : is.length = vs.length) :
    ∃ f : α → β, is.map f = vs := by
  induction is generalizing vs with
  | nil =>
    cases vs with
    | nil => exact ⟨fallback, rfl⟩
    | cons => simp at hl
  | cons i is ih =>
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      obtain ⟨hn, ht⟩ := List.nodup_cons.mp hi
      obtain ⟨g, hg⟩ := ih vs ht (by simpa using hl)
      refine ⟨fun j => if j = i then v else g j, ?_⟩
      simp
      rw [← hg]
      apply List.map_eq_map_iff.mpr
      intro j hj
      have hne : j ≠ i := fun h => hn (h ▸ hj)
      simp [hne]

/-- The order of `u` and `w` is respected within their respective row classes. -/
theorem exists_fill_split (r : Row k → Bool) (u w : List (Chip k)) (fallback : Batch k)
    (hu : ((List.finRange k).filter (fun i => !(r i))).length = u.length)
    (hw : ((List.finRange k).filter r).length = w.length) :
    ∃ X : Batch k, (((List.finRange k).filter (fun i => !(r i))).map X = u) ∧
      (((List.finRange k).filter r).map X = w) := by
  have hn := List.nodup_finRange k
  obtain ⟨fu, hfu⟩ := fill_nodup _ _ fallback (hn.filter _) hu
  obtain ⟨fw, hfw⟩ := fill_nodup _ _ fallback (hn.filter _) hw
  refine ⟨fun i => if r i then fw i else fu i, ?_, ?_⟩
  · rw [← hfu]
    apply List.map_eq_map_iff.mpr
    intro i hi
    have h := (List.mem_filter.mp hi).2
    simp_all
  · rw [← hfw]
    apply List.map_eq_map_iff.mpr
    intro i hi
    simp [(List.mem_filter.mp hi).2]

end StarFiring
