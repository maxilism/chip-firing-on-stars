import StarFiring.ArmEvents

/-! Reading the labels of a projected trace. A comparison is forced when its
site contains exactly two entries. The first comparison either sees the first
two arrivals, or chooses a pair of three; the complementary entry is retained.
This proof counts *present* labels, not distinct labels across time. -/
namespace StarFiring
namespace ArmTemplate

/-- Explicit contents in the three occupied depths, in arbitrary list order. -/
def bag (X Y Z : List (Chip k)) : ArmConfig k
  | 0,x => X.count x | 1,x => Y.count x | 2,x => Z.count x | _+3,_ => 0

theorem bag_nil : bag ([] : List (Chip k)) [] [] = fun _ _ => 0 := by
  funext n x; match n with | 0 | 1 | 2 | _+3 => simp [bag]

private theorem cons_count (a x : Chip k) (X : List (Chip k)) :
    ((a::X).count x : Int) = X.count x + ind (a=x) := by
  by_cases h : a=x <;> simp [ind,h]

private theorem send (X Y Z : List (Chip k)) (a : Chip k) :
    (ArmEvent.deliver a).act (bag X Y Z) = bag (a::X) Y Z := by
  funext n x
  match n with | 0 | 1 | 2 | _+3 => simp [ArmEvent.act,ArmEvent.delta,bag,cons_count,ind]

private theorem cmp0 (X W Y Z : List (Chip k)) (a b : Chip k) (h : X.Perm (a::b::W)) :
    (ArmEvent.compare 0 a b).act (bag X Y Z) = bag W (b::Y) Z := by
  funext n x
  have hc : (X.count x : Int) = ((a::b::W).count x : Int) := by rw [h.count_eq]
  simp only [cons_count] at hc
  match n with
  | 0 | 1 | 2 | _+3 => simp [ArmEvent.act,ArmEvent.delta,bag,cons_count,ind] at * <;> omega

private theorem cmp1 (X Y W Z : List (Chip k)) (a b : Chip k) (h : Y.Perm (a::b::W)) :
    (ArmEvent.compare 1 a b).act (bag X Y Z) = bag (a::X) W (b::Z) := by
  funext n x
  have hc : (Y.count x : Int) = ((a::b::W).count x : Int) := by rw [h.count_eq]
  simp only [cons_count] at hc
  match n with
  | 0 | 1 | 2 | _+3 => simp [ArmEvent.act,ArmEvent.delta,bag,cons_count,ind] at * <;> omega

private theorem legal0 (X Y Z : List (Chip k)) (a b : Chip k)
    (h : (ArmEvent.compare 0 a b).Legal (bag X Y Z)) : a < b ∧ a ∈ X ∧ b ∈ X := by
  simpa [ArmEvent.Legal,bag,List.count_pos_iff] using h

private theorem legal1 (X Y Z : List (Chip k)) (a b : Chip k)
    (h : (ArmEvent.compare 1 a b).Legal (bag X Y Z)) : a < b ∧ a ∈ Y ∧ b ∈ Y := by
  simpa [ArmEvent.Legal,bag,List.count_pos_iff] using h

private theorem chipMin (a b : Chip k) : min a b = if a.val ≤ b.val then a else b := by split <;> apply Fin.ext <;> change min _ _ = _ <;> omega
private theorem chipMax (a b : Chip k) : max a b = if a.val ≤ b.val then b else a := by split <;> apply Fin.ext <;> change max _ _ = _ <;> omega
private theorem sortPair (u v a b : Chip k) (h : a < b) (ha : a ∈ [u,v]) (hb : b ∈ [u,v]) :
    a = min u v ∧ b = max u v ∧ [u,v].Perm [a,b] := by
  have hle : a.val ≤ b.val := Nat.le_of_lt h
  have hnl : ¬ b.val ≤ a.val := Nat.not_le_of_gt h
  simp at ha hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
  all_goals first
    | exact False.elim ((Fin.lt_irrefl _) h)
    | exact ⟨by simp [chipMin, hle, hnl], by simp [chipMax, hle, hnl], .refl _⟩
    | exact ⟨by simp [chipMin, hnl], by simp [chipMax, hnl], .swap ..⟩

private theorem frontPerm (p : ArmTemplate k) : [p.B,p.A].Perm [p.L,p.H] := by
  simp only [L,H,chipMin,chipMax]; split
  · exact .swap ..
  · rfl

private theorem minLH (p : ArmTemplate k) : min p.L p.H = p.L := by
  apply Fin.ext; simp only [L,H,Fin.val_min,Fin.val_max]; omega
private theorem maxLH (p : ArmTemplate k) : max p.L p.H = p.H := by
  apply Fin.ext; simp only [L,H,Fin.val_min,Fin.val_max]; omega

private theorem takeThree (p : ArmTemplate k) (hlt : p.r1 < p.u1)
    (hr : p.r1 ∈ [p.T,p.B,p.A]) (hu : p.u1 ∈ [p.T,p.B,p.A]) :
    ∃ c : Mode, c ≠ .r ∧ p.r1 = p.small c ∧ p.u1 = p.large c ∧
      [p.T,p.B,p.A].Perm [p.r1,p.u1,p.rest c] := by
  have hp : [p.T,p.B,p.A].Perm [p.L,p.H,p.T] :=
    ((frontPerm p).cons p.T).trans (List.perm_cons_append_cons (l₁ := [p.L,p.H]) (l₂ := []) p.T (.refl _))
  replace hr := hp.mem_iff.mp hr
  replace hu := hp.mem_iff.mp hu
  have hc : (p.r1 ∈ [p.L,p.H] ∧ p.u1 ∈ [p.L,p.H]) ∨
      (p.r1 ∈ [p.L,p.T] ∧ p.u1 ∈ [p.L,p.T]) ∨ (p.r1 ∈ [p.H,p.T] ∧ p.u1 ∈ [p.H,p.T]) := by
    simp at hr hu ⊢; grind
  rcases hc with ⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩
  · obtain ⟨h1,h2,hh⟩ := sortPair _ _ _ _ hlt ha hb
    exact ⟨.e, by decide, h1.trans (minLH p), h2.trans (maxLH p),hp.trans (hh.append_right [_])⟩
  · obtain ⟨h1,h2,hh⟩ := sortPair _ _ _ _ hlt ha hb
    exact ⟨.l, by decide,h1,h2, hp.trans ((List.Perm.cons _ (.swap ..)).trans (hh.append_right [_]))⟩
  · obtain ⟨h1,h2,hh⟩ := sortPair _ _ _ _ hlt ha hb
    exact ⟨.h, by decide,h1,h2, hp.trans ((List.perm_cons_append_cons (l₁ := [p.H,p.T]) (l₂ := []) p.L (.refl _)).trans (hh.append_right [_]))⟩

private theorem uncons {s t : ArmConfig k} {e es} (h : ArmRun s (e::es) t) :
    e.Legal s ∧ ArmRun (e.act s) es t := by cases h; constructor <;> assumption

private theorem takeStart (p : ArmTemplate k) {tail : List (ArmEvent k)} {t : ArmConfig k}
    (h : ArmRun (bag [] [] []) (p.startEvents ++ tail) t) :
    ∃ c : Mode, c ≠ .r ∧ (p.early = true → c = .e ∨ c = .r) ∧
      p.r1 = p.small c ∧ p.u1 = p.large c ∧ ArmRun (bag [p.rest c] [p.u1] []) tail t := by
  cases he : p.early <;> simp [startEvents, he] at h <;>
    obtain ⟨_, h⟩ := uncons h <;> rw [send] at h <;>
    obtain ⟨_, h⟩ := uncons h <;> rw [send] at h
  · obtain ⟨_, h⟩ := uncons h; rw [send] at h
    obtain ⟨hl, h⟩ := uncons h
    obtain ⟨hlt,hr,hu⟩ := legal0 _ _ _ _ _ hl
    obtain ⟨c,hn,ha,hb,hp⟩ := takeThree p hlt hr hu
    rw [cmp0 _ _ _ _ _ _ hp] at h
    exact ⟨c,hn,by simp,ha,hb,h⟩
  · obtain ⟨hl, h⟩ := uncons h
    obtain ⟨hlt,hr,hu⟩ := legal0 _ _ _ _ _ hl
    have hp := frontPerm p
    obtain ⟨ha,hb,hperm⟩ := sortPair _ _ _ _ hlt (hp.mem_iff.mp hr) (hp.mem_iff.mp hu)
    rw [cmp0 _ _ _ _ _ _ (hp.trans hperm)] at h
    obtain ⟨_, h⟩ := uncons h; rw [send] at h
    exact ⟨.e,by decide,fun _ => .inl rfl,ha.trans (minLH p),hb.trans (maxLH p),h⟩

private theorem force0 (X Y Z : List (Chip k)) (u v a b : Chip k) (hp : X.Perm [u,v])
    (hl : (ArmEvent.compare 0 a b).Legal (bag X Y Z)) :
    a = min u v ∧ b = max u v ∧ (ArmEvent.compare 0 a b).act (bag X Y Z) = bag [] (b::Y) Z := by
  obtain ⟨hlt,ha,hb⟩ := legal0 _ _ _ _ _ hl
  obtain ⟨h1,h2,h3⟩ := sortPair _ _ _ _ hlt (hp.mem_iff.mp ha) (hp.mem_iff.mp hb)
  exact ⟨h1,h2,cmp0 _ _ _ _ _ _ (hp.trans h3)⟩

private theorem force1 (X Y Z : List (Chip k)) (u v a b : Chip k) (hp : Y.Perm [u,v])
    (hl : (ArmEvent.compare 1 a b).Legal (bag X Y Z)) :
    a = min u v ∧ b = max u v ∧ (ArmEvent.compare 1 a b).act (bag X Y Z) = bag (a::X) [] (b::Z) := by
  obtain ⟨hlt,ha,hb⟩ := legal1 _ _ _ _ _ hl
  obtain ⟨h1,h2,h3⟩ := sortPair _ _ _ _ hlt (hp.mem_iff.mp ha) (hp.mem_iff.mp hb)
  exact ⟨h1,h2,cmp1 _ _ _ _ _ _ (hp.trans h3)⟩

/-- Read the actual chosen pairs and terminal labels. Does not impose an order
on the depth-two firing relative to batch 5; both placements yield the same result. -/
theorem extract (p : ArmTemplate k) {t : ArmConfig k}
    (h : ArmRun (fun _ _ => 0) p.events t) :
    (∃ c : Mode, c ≠ .r ∧ p.Reads c) ∧ t = bag [p.F] [p.m] [p.o] := by
  rw [← bag_nil] at h
  obtain ⟨c,hn,he,h1,h2,h⟩ := takeStart p (tail := p.endEvents) h
  cases ho : p.outEarly <;> simp [endEvents,ho] at h <;>
    obtain ⟨_, h⟩ := uncons h <;> rw [send] at h <;>
    obtain ⟨hl,h⟩ := uncons h <;>
    obtain ⟨hs,hv,ha⟩ := force0 _ _ _ (p.rest c) p.D _ _ (.swap ..) hl <;>
    rw [ha] at h
  · obtain ⟨_, h⟩ := uncons h; rw [send] at h
    obtain ⟨hl, h⟩ := uncons h
    obtain ⟨hq,ho,ha⟩ := force1 _ _ _ p.u1 p.u2 _ _ (.swap ..) hl
    rw [ha] at h
    obtain ⟨hl, h⟩ := uncons h
    obtain ⟨hf,hm,ha⟩ := force0 _ _ _ p.E p.q _ _ (.swap ..) hl
    rw [ha] at h
    obtain ⟨_, h⟩ := uncons h; rw [send] at h; cases h
    exact ⟨⟨c,hn,he,h1,h2,hs,hv,hq,ho,hf,hm⟩,rfl⟩
  · obtain ⟨hl,h⟩ := uncons h
    obtain ⟨hq,ho,ha⟩ := force1 _ _ _ p.u1 p.u2 _ _ (.swap ..) hl
    rw [ha] at h
    obtain ⟨_, h⟩ := uncons h; rw [send] at h
    obtain ⟨hl, h⟩ := uncons h
    obtain ⟨hf,hm,ha⟩ := force0 _ _ _ p.E p.q _ _ (.refl _) hl
    rw [ha] at h
    obtain ⟨_, h⟩ := uncons h; rw [send] at h; cases h
    exact ⟨⟨c,hn,he,h1,h2,hs,hv,hq,ho,hf,hm⟩,rfl⟩

end ArmTemplate
end StarFiring
