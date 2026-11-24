import StarFiring.CenterInput
import StarFiring.Fill

/-! Partitioning the spare column.  When a third dispatch uses a returned
low chip, exchange that row's spare into the fourth dispatch.  The proof
works with bags, allowing a label to leave center more than once. -/
namespace StarFiring
namespace Pack
private abbrev R (k : Nat) := List.finRange k
private abbrev col (b : Batch k) := (R k).map b

private theorem split_map (xs : List α) (r : α → Bool) (f g : α → β) :
    (xs.map (fun i => if r i then f i else g i)).Perm
      ((xs.filter r).map f ++ (xs.filter fun i => !r i).map g) := by
  let h := (List.filter_append_perm r xs).symm.map (fun i => if r i then f i else g i)
  rw [List.map_append] at h
  refine h.trans (.of_eq ?_)
  congr 1 <;> apply List.map_congr_left
  · intro i hi; simp [(List.mem_filter.mp hi).2]
  · intro i hi; have := (List.mem_filter.mp hi).2; cases e : r i <;> simp_all

/-- General packing lemma. `sp` is the untouched reserve, `ret` the first
return on each arm, and `early` identifies which returns happened before T. -/
theorem reserve {L ret T D : Batch k} {early : Row k → Bool} {sp : List (Chip k)}
    (hsL : (sp ++ col L).Nodup) (hs : sp.length = k) (hT : (col T).Nodup)
    (hready : ∀ x ∈ col T, x ∈ sp ∨ ∃ i, early i = true ∧ L i = x)
    (hret : ∀ i, early i = true → ret i = L i)
    (hbalance : (col T ++ col D).Perm (sp ++ col ret)) :
    ∃ (r : Row k → Bool) (X : Batch k), (∀ i, r i = true → early i = true) ∧
      (col X).Perm sp ∧ (col (fun i => if r i then L i else X i)).Perm (col T) ∧
      (col (fun i => if r i then X i else ret i)).Perm (col D) := by
  let r : Row k → Bool := fun i => early i && decide (L i ∈ col T)
  let pred : Chip k → Bool := fun x => decide (x ∈ col T)
  let u := sp.filter pred
  let w := sp.filter fun x => !pred x
  let rs := (R k).filter r
  let ns := (R k).filter fun i => !r i
  have nd := List.nodup_append.mp hsL
  have hp : (rs.map L ++ u).Perm (col T) := by
    have hrs : (rs.map L).Nodup := (List.filter_sublist.map L).nodup nd.2.1
    have hu : u.Nodup := List.filter_sublist.nodup nd.1
    have hdis : ∀ a ∈ rs.map L, ∀ b ∈ u, a ≠ b := by
      intro a ha b hb e
      have h' : a ∈ col L := (List.filter_sublist.map L).subset ha
      exact nd.2.2 _ (List.mem_filter.mp hb).1 _ h' e.symm
    apply (List.perm_ext_iff_of_nodup (List.nodup_append.mpr ⟨hrs,hu,hdis⟩) hT).mpr
    intro x; constructor
    · intro hx; rcases List.mem_append.mp hx with hx|hx
      · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp (List.mem_filter.mp hi).2).2
      · exact of_decide_eq_true (List.mem_filter.mp hx).2
    · intro hx; rcases hready x hx with h|⟨i,hi,rfl⟩
      · exact List.mem_append_right _ (List.mem_filter.mpr ⟨h,decide_eq_true hx⟩)
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_filter.mpr
          ⟨List.mem_finRange i,Bool.and_eq_true_iff.mpr ⟨hi,decide_eq_true hx⟩⟩,rfl⟩)
  have hrslen := hp.length_eq
  change ((rs.map L) ++ u).length = (col T).length at hrslen
  simp only [List.length_append,List.length_map,List.length_finRange,R] at hrslen
  have hrow : rs.length + ns.length = k := by simpa [rs,ns,R] using (List.filter_append_perm r (R k)).length_eq
  have hsp := List.filter_append_perm pred sp
  have hspLen : u.length + w.length = k := by simpa [u,w,hs] using hsp.length_eq
  obtain ⟨X,hXn,hXr⟩ := exists_fill_split r u w L (by change ns.length = u.length; omega) (by change rs.length = w.length; omega)
  have he : ∀ i, r i = true → early i = true := fun _ h => (Bool.and_eq_true_iff.mp h).1
  have splitX := split_map (R k) r X X
  simp only [ite_self, hXn,hXr] at splitX
  have hX : (col X).Perm sp := splitX.trans (List.perm_append_comm.trans hsp)
  have splitT := split_map (R k) r L X
  rw [hXn] at splitT
  have sortT := splitT.trans hp
  have splitD := split_map (R k) r X ret
  rw [hXr] at splitD
  have hret' : rs.map ret = rs.map L := List.map_congr_left fun i hi => hret i (he i (List.mem_filter.mp hi).2)
  have splitRet : (col ret).Perm (rs.map L ++ ns.map ret) := by
    rw [← hret']
    simpa only [ite_self] using split_map (R k) r ret ret
  refine ⟨r, X, he, hX, sortT, splitD.trans (List.perm_iff_count.mpr ?_)⟩
  intro x
  have h1 := hp.count x
  have h2 := hbalance.count x
  have h3 := splitRet.count x
  have h4 := hsp.count x
  change (u ++ w).count x = sp.count x at h4
  change (w ++ ns.map ret).count x = _
  simp only [List.count_append] at *
  omega

private def tag (raw : Mode) (b : Bool) : Mode := if b then .r else match raw with
  | .r => .e | m => m

private theorem tagReads {p : ArmTemplate k} {raw : Mode} {b : Bool}
    (h : p.Reads raw) (he : b = true → p.early = true) : p.Reads (tag raw b) := by
  cases b with
  | true =>
    rcases h.pre (he rfl) with rfl|rfl
    · exact p.reads_e_iff_r.mp h
    · exact h
  | false => cases raw <;> first | exact h | exact p.reads_e_iff_r.mpr h

/-- Package the first two deliveries in sorted coordinates and choose a spare
on each row. The only rows tagged R are *sources* of early returns used by
T, regardless of where those labels land. -/
theorem certificate (p : Row k → ArmTemplate k) (raw : Row k → Mode)
    (read : ∀ i, (p i).Reads (raw i)) (ledger : CutLedger p)
    (ha : Increasing (fun i => (p i).A)) (hb : Increasing (fun i => (p i).B))
    (ht : Increasing (fun i => (p i).T)) (hd : Increasing (fun i => (p i).D))
    (he : Increasing (fun i => (p i).E)) (hf : Increasing (fun i => (p i).F)) :
    ∃ c : Cert k, c.Valid ∧ c.F = (fun i => (p i).F) ∧
      c.middle = (fun i => (p i).m) ∧ c.outer = (fun i => (p i).o) := by
  obtain ⟨dis,sp,hpart,hready,hcount⟩ := ledger.resources ha hb
  obtain ⟨incL,incH,lh,_⟩ := Center.sorted_pair_facts ha hb dis
  let L : Batch k := fun i => (p i).L
  let H : Batch k := fun i => (p i).H
  let T : Batch k := fun i => (p i).T
  let D : Batch k := fun i => (p i).D
  let ret : Batch k := fun i => (p i).r1
  change (List.finRange (3*k)).Perm (col L ++ (col H ++ sp)) at hpart
  have hnd := List.nodup_append.mp (hpart.nodup (List.nodup_finRange _))
  have hsL : (sp ++ col L).Nodup := List.nodup_append.mpr
    ⟨(List.nodup_append.mp hnd.2.1).2.1,hnd.1,fun a ha b hb e => hnd.2.2 _ hb _ (List.mem_append_right _ ha) e.symm⟩
  have hs : sp.length = k := by have := hpart.length_eq; simp only [col,R,List.length_append,List.length_map,List.length_finRange] at this; omega
  have hnT : (col T).Nodup := (List.nodup_finRange k).map T (fun i j h e => h (increasing_injective ht e))
  have hret (i) (h : (p i).early = true) : ret i = L i := by
    rcases (read i).pre h with e|e <;> simpa [ret,L,e,ArmTemplate.small] using (read i).firstSmall
  have hready' (x) (hx : x ∈ col T) : x ∈ sp ∨ ∃ i, (p i).early = true ∧ L i = x := by
    rcases hready x ((Center.mem_col T x).mp hx) with e|⟨i,ei,ri⟩
    · exact .inl e
    · exact .inr ⟨i,ei,(hret i ei).symm.trans ri⟩
  have hbal : (col T ++ col D).Perm (sp ++ col ret) := List.perm_iff_count.mpr (fun x => by simpa only [List.count_append] using hcount x)
  obtain ⟨r,X,hr,hX,hT,hD⟩ := reserve hsL hs hnT hready' hret hbal
  let c : Cert k := ⟨fun i => tag (raw i) (r i), L, H, X, T, D, fun i => (p i).E, fun i => (p i).F⟩
  have rd (i) : (p i).Reads (c.mode i) := tagReads (read i) (hr i)
  have ty (i) : (p i).u1 = c.y i := by
    change _ = match c.mode i with | .e | .r => H i | .l => max (L i) (T i) | .h => max (H i) (T i)
    exact (rd i).firstLarge
  have tv (i) : (p i).u2 = c.V i := (rd i).secondLarge
  have tq (i) : (p i).q = c.Q i := by rw [(rd i).inward,ty,tv]; rfl
  have feedE : c.feedE = fun i => (p i).r2 := funext fun i => (rd i).secondSmall.symm
  have feedF : c.feedF = fun i => (p i).r3 := by funext i; rw [(rd i).lastSmall,tq]; rfl
  have feedT : c.feedT = (fun i => if r i then L i else X i) := by
    funext i; cases h : r i <;> cases e : raw i <;> simp [Cert.feedT,c,tag,h,e]
  have feedD : c.feedD = (fun i => if r i then X i else ret i) := by
    funext i
    cases h : r i
    · have e := (read i).firstSmall
      cases m : raw i <;> simpa [tag,Cert.feedD,c,h,m,ret,L,H,T,ArmTemplate.small] using e.symm
    · simp [Cert.feedD,c,tag,h]
  refine ⟨c, ⟨?_,incL,incH,ht,hd,he,hf,lh,?_,?_,?_,?_⟩,rfl,?_,?_⟩
  · exact (hpart.trans ((hX.symm.append_left _).append_left _)).trans (Center.triple_split L H X).symm
  · rw [feedT]; exact hT
  · rw [feedD]; exact hD
  · rw [feedE]; exact ledger.hE
  · rw [feedF]; exact ledger.hF
  · funext i; rw [(rd i).lastLarge,tq]; rfl
  · funext i; rw [(rd i).outward,ty,tv]; rfl

end Pack
end StarFiring
