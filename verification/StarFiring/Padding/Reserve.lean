import StarFiring.Core

/-! Realizing the spare column: a row which replays its B entry takes its
own tiny spare. All other rows take the entries of T not present in B. -/
namespace StarFiring.Padding.Pin

private theorem map_nodup {f : Fin k → Nat}
    (hf : ∀ i j, i < j → f i < f j) : ((List.finRange k).map f).Nodup := by
  apply (List.nodup_finRange k).map
  intro i j hne eq
  by_cases h : i < j
  · have := hf i j h; omega
  · have := hf j i (by omega); omega

private theorem split_map (xs : List α) (p : α → Bool) (f g : α → β) :
    (xs.map (fun i => if p i then f i else g i)).Perm
      ((xs.filter p).map f ++ (xs.filter fun i => !p i).map g) := by
  have h := (List.filter_append_perm p xs).symm.map (fun i => if p i then f i else g i)
  rw [List.map_append] at h
  refine h.trans (.of_eq ?_)
  congr 1 <;> apply List.map_congr_left
  · intro i hi; simp [(List.mem_filter.mp hi).2]
  · intro i hi; have := (List.mem_filter.mp hi).2; cases e : p i <;> simp_all

/-- Both the physical (B and X distinct) and routed (replayed B plus unused T)
partitions hold for the same choice of X. -/
theorem reserve {B T : Fin k → Nat} {r : Fin k → Bool}
    (incB : ∀ i j, i < j → B i < B j) (incT : ∀ i j, i < j → T i < T j)
    (hB : ∀ i, k ≤ B i) (hT : ∀ i, k ≤ T i)
    (cross : ∀ i, (∃ j, B i = T j) ↔ r i = true) :
    ∃ X : Fin k → Nat, (∀ i, r i = true → X i = i.val) ∧
      (((List.finRange k).map B) ++ (List.finRange k).map X).Nodup ∧
      ((List.finRange k).map (fun i => if r i then B i else X i)).Perm
        ((List.finRange k).map T) := by
  let rows := List.finRange k
  let shared := rows.filter r
  let fresh := rows.filter fun i => !r i
  let bs := rows.map B
  let ts := rows.map T
  let unused := ts.filter fun x => decide (x ∉ bs)
  have memU (x : Nat) : x ∈ unused ↔ x ∈ ts ∧ x ∉ bs := by simp [unused]
  have memB (x : Nat) : x ∈ bs ↔ ∃ i, B i = x := by simp [bs,rows]
  have memT (x : Nat) : x ∈ ts ↔ ∃ j, T j = x := by simp [ts,rows]
  have nB := map_nodup incB
  have nT := map_nodup incT
  have nU : unused.Nodup := nT.filter _
  have nS : (shared.map B).Nodup := (List.filter_sublist.map B).nodup nB
  have nSU : (shared.map B ++ unused).Nodup := List.nodup_append.mpr
    ⟨nS,nU,by
      rintro x hx y hy rfl
      exact ((memU _).mp hy).2 ((List.filter_sublist.map B).subset hx)⟩
  have part : (shared.map B ++ unused).Perm ts := by
    apply (List.perm_ext_iff_of_nodup nSU nT).mpr
    intro x; constructor
    · intro hx; rcases List.mem_append.mp hx with h | h
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
        obtain ⟨j,e⟩ := (cross i).2 (List.mem_filter.mp hi).2
        exact (memT _).2 ⟨j,e.symm⟩
      · exact ((memU _).1 h).1
    · intro hx
      by_cases hb : x ∈ bs
      · obtain ⟨i, rfl⟩ := (memB _).1 hb
        obtain ⟨j,e⟩ := (memT _).1 hx
        have hi := (cross i).1 ⟨j,e.symm⟩
        exact List.mem_append_left _ (List.mem_map.mpr
          ⟨i,List.mem_filter.mpr ⟨List.mem_finRange i,hi⟩,rfl⟩)
      · exact List.mem_append_right _ ((memU _).2 ⟨hx,hb⟩)
  have len : fresh.length = unused.length := by
    have h₁ : shared.length + unused.length = k := by simpa [ts, rows] using part.length_eq
    have h₂ : shared.length + fresh.length = k := by
      simpa [shared, fresh, rows] using (List.filter_append_perm r rows).length_eq
    omega
  -- On fresh rows, index into the ordered list of unused labels by their
  -- position in the fresh row list. Its length is exactly right by `part`.
  let X (i : Fin k) : Nat := if r i then i.val else unused[fresh.idxOf i]?.getD 0
  have tiny (i) (h : r i = true) : X i = i.val := by simp [X,h]
  have nf : fresh.Nodup := (List.nodup_finRange k).filter _
  have fill : fresh.map X = unused := by
    apply List.ext_getElem (by simpa using len)
    intro j hj hu
    have hj' : j < fresh.length := by simpa using hj
    have hm := (List.mem_filter.mp (List.getElem_mem (l := fresh) hj')).2
    simp only [List.getElem_map, X, Bool.not_eq_true'] at *
    simp [hm, nf.idxOf_getElem, hu]
  have pick := split_map rows r B X
  change (rows.map _).Perm (shared.map B ++ fresh.map X) at pick
  rw [fill] at pick
  refine ⟨X,tiny,?_,pick.trans part⟩
  have sx : (rows.map X).Perm (shared.map Fin.val ++ unused) := by
    have h := split_map rows r X X
    simp only [ite_self] at h
    change (rows.map X).Perm (shared.map X ++ fresh.map X) at h
    have e : shared.map X = shared.map Fin.val := List.map_congr_left
      (fun i hi => tiny i (List.mem_filter.mp hi).2)
    rwa [fill, e] at h
  apply (sx.append_left bs).symm.nodup
  have small (x) (hx : x ∈ shared.map Fin.val) : x < k := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; exact i.isLt
  have bigU (x) (hx : x ∈ unused) : k ≤ x := by
    obtain ⟨j,rfl⟩ := (memT _).1 ((memU _).1 hx).1; exact hT j
  have ns : (shared.map Fin.val).Nodup := ((List.nodup_finRange k).filter r).map _
    fun _ _ h e => h (Fin.ext e)
  apply List.nodup_append.mpr
  refine ⟨nB, List.nodup_append.mpr ⟨ns, nU, ?_⟩, ?_⟩
  · intro a ha b hb; have := small a ha; have := bigU b hb; omega
  · rintro a ha b hb rfl
    rcases List.mem_append.mp hb with h | h
    · obtain ⟨i,rfl⟩ := (memB _).mp ha; have := small _ h; have := hB i; omega
    · exact ((memU _).mp h).2 ha

end StarFiring.Padding.Pin
