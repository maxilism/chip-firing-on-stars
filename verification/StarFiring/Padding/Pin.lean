import StarFiring.Padding.Rank
import StarFiring.Padding.Reserve
import StarFiring.Cert
import StarFiring.Center

/-! Ordinary pinning: the second delivery is a large sentinel on every arm;
replay on low source rows recycles an earlier chip into the third delivery.
The same sorted fourth delivery can then be fired three times. -/
namespace StarFiring.Padding.Pin

def target (high : Fin k → Bool) (B T : Fin k → α) (i : Fin k) := if high i then B i else T i
def other (high : Fin k → Bool) (B T : Fin k → α) (i : Fin k) := if high i then T i else B i

/-- An ordinary pin certificate with specified high and replay-source rows.
The pin survives: its physical level-one label `z` is the terminal middle
label, and the fourth delivery is also used as the fifth and sixth. -/
def Witness (p : Fin k → Fin k) (high r : Fin k → Bool) : Prop :=
  ∃ c : Cert k, c.Valid ∧
    (∀ i, c.mode i = if high i then .h else if r i then .r else .e) ∧
    c.E = c.D ∧ c.F = c.D ∧ c.middle = c.z ∧
    ∀ i j, c.middle i < c.middle j ↔ p i < p j

/-- Soundness is inherited from the physical replay of the exhibited certificate. -/
theorem Witness.realizable (hk : 0 < k) {p : Fin k → Fin k} {high r : Fin k → Bool}
    (w : Witness p high r) : Realizable p := by
  obtain ⟨c,hc,_,_,_,_,hp⟩ := w
  exact Cert.realizable hc hk hp

private abbrev col {k : Nat} (f : Fin k → α) := (List.finRange k).map f
private def mode (high r : Fin k → Bool) (i : Fin k) : Mode :=
  if r i then .r else if high i then .h else .e

/-- The physical certificate after ranking. The replay row is a *source*, not
necessarily its own destination: the entire third delivery is rebatched. -/
private theorem pinned {p : Fin k → Fin k} (high r : Fin k → Bool)
    (B G X T D : Batch k)
    (part : (List.finRange (3*k)).Perm (col B ++ (col G ++ col X)))
    (hB : Increasing B) (hG : Increasing G) (hT : Increasing T) (hD : Increasing D)
    (bG : ∀ i, B i < G i) (tG : ∀ i, T i < G i)
    (early : ∀ i, r i = true → high i = false)
    (sortT : Cert.Rebatch (fun i => if r i then B i else X i) T)
    (sortD : Cert.Rebatch (fun i => if r i then X i else other high B T i) D)
    (below : ∀ i, D i < target high B T i)
    (order : ∀ i j, target high B T i < target high B T j ↔ p i < p j) : Witness p high r := by
  let c : Cert k := ⟨mode high r,B,G,X,T,D,D,D⟩
  have z : c.z = target high B T := by
    funext i; cases e : r i <;> cases h : high i <;>
      simp_all [Cert.z,c,mode,target]
  have y : c.y = G := by
    funext i; cases e : r i <;> cases h : high i <;>
      simp [Cert.y,c,mode,e,h,CertReplay.Transfer.maxL (Fin.le_of_lt (tG i))]
  have zG (i) : target high B T i < G i := by cases h : high i <;> simp_all [target]
  have e : c.feedE = D := by
    funext i; unfold Cert.feedE; rw [z]; exact CertReplay.Transfer.minR (Fin.le_of_lt (below i))
  have v : c.V = target high B T := by
    funext i; unfold Cert.V; rw [z]; exact CertReplay.Transfer.maxL (Fin.le_of_lt (below i))
  have q : c.Q = target high B T := by
    funext i; unfold Cert.Q; rw [y,v]; exact CertReplay.Transfer.minR (Fin.le_of_lt (zG i))
  have f : c.feedF = D := by
    funext i; unfold Cert.feedF; rw [q]; exact CertReplay.Transfer.minL (Fin.le_of_lt (below i))
  have m : c.middle = target high B T := by
    funext i; unfold Cert.middle; rw [q]; exact CertReplay.Transfer.maxR (Fin.le_of_lt (below i))
  have modes (i) : c.mode i = (if high i then .h else if r i then .r else .e) := by
    cases ri : r i <;> cases hi : high i <;> simp_all [c,mode]
  refine ⟨c,?_,modes,rfl,rfl,m.trans z.symm,m ▸ order⟩
  refine ⟨part.trans (Center.triple_split B G X).symm,hB,hG,hT,hD,hD,hD,bG,?_,?_,?_,?_⟩
  · have eqn : c.feedT = (fun i => if r i then B i else X i) := by
      funext i; cases a : r i <;> cases h : high i <;> simp [Cert.feedT,c,mode,a,h]
    rw [eqn]; exact sortT
  · have eqn : c.feedD = (fun i => if r i then X i else other high B T i) := by
      funext i; cases a : r i <;> cases h : high i <;>
        simp [Cert.feedD,c,mode,other,a,h,CertReplay.Transfer.minR (Fin.le_of_lt (tG i))]
    rw [eqn]; exact sortD
  · rw [e]; exact .refl _
  · rw [f]; exact .refl _

private theorem mem_col (f : Fin k → α) (i : Fin k) : f i ∈ col f :=
  List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩

private theorem inj {f : Fin k → Nat} (h : ∀ i j, i < j → f i < f j) : Function.Injective f := by
  intro i j e; apply Fin.ext; apply Classical.byContradiction; intro ne
  rcases Nat.lt_or_gt_of_ne ne with lt|lt
  · have := h i j lt; omega
  · have := h j i lt; omega

private theorem col_nd {f : Fin k → Nat} (hf : Function.Injective f) : (col f).Nodup :=
  (List.nodup_finRange k).map f (fun _ _ ne eq => ne (hf eq))

private def donor (high r : Fin k → Bool) (B T : Fin k → Nat) (i : Fin k) : Nat :=
  if r i then i.val else other high B T i

/-- Distinct physical donors: replay rows donate tiny spares, while a B donor
from an unreplayed row cannot be any T label. -/
private theorem donor_nd (B T : Fin k → Nat) (high r : Fin k → Bool)
    (hB : ∀ i j, i < j → B i < B j) (hT : ∀ i j, i < j → T i < T j)
    (floorB : ∀ i, k ≤ B i) (floorT : ∀ i, k ≤ T i)
    (cross : ∀ i, (∃ j, B i = T j) ↔ r i = true) : (col (donor high r B T)).Nodup := by
  apply col_nd
  intro i j e
  have base (a : Fin k) : k ≤ other high B T a := by cases h : high a <;> simp_all [other]
  have apart (a : Fin k) (hn : r a = false) (b : Fin k) : B a ≠ T b := fun eq =>
    Bool.noConfusion (hn.symm.trans ((cross a).mp ⟨b,eq⟩))
  cases ri : r i <;> cases rj : r j <;> simp only [donor,ri,rj,Bool.false_eq_true,ite_false,ite_true] at e
  · cases hi : high i <;> cases hj : high j <;> simp [other,hi,hj] at e
    · exact inj hB e
    · exact False.elim (apart i ri j e)
    · exact False.elim (apart j rj i e.symm)
    · exact inj hT e
  · have := base i; omega
  · have := base j; omega
  · exact Fin.ext e

/-- General ordinary pin theorem. `cross` identifies replays by source row;
`enough` counts all fourth-batch donors strictly below the chosen pins,
treating a tiny spare as cheap at every pin. -/
theorem certificate {k : Nat} (hk : 0 < k) (p : Fin k → Fin k)
    (B T : Fin k → Nat) (high r : Fin k → Bool)
    (hB : ∀ i j, i < j → B i < B j) (hT : ∀ i j, i < j → T i < T j)
    (floorB : ∀ i, k ≤ B i) (floorT : ∀ i, k ≤ T i)
    (cross : ∀ i, (∃ j, B i = T j) ↔ r i = true)
    (early : ∀ i, r i = true → high i = false)
    (enough : ∀ i : Fin k, i.val < (List.finRange k).countP
      (fun j => r j || decide (other high B T j < target high B T i)))
    (order : ∀ i j, target high B T i < target high B T j ↔ p i < p j) : Witness p high r := by
  obtain ⟨X,tiny,bxnd,sortT⟩ := reserve hB hT floorB floorT cross
  let Z := target high B T
  let feed := donor high r B T
  let D := Rank.sortColumn feed
  have incD := Rank.sortColumn_inc (donor_nd B T high r hB hT floorB floorT cross)
  have sortD := Rank.sortColumn_perm feed
  have feed_eq (i) : feed i = if r i then X i else other high B T i := by
    cases h : r i <;> simp [feed,donor,h,tiny]
  have below (i : Fin k) : D i < Z i := by
    apply (Rank.sortColumn_lt_iff feed i (Z i)).mpr
    rw [Rank.col,List.countP_map]
    have zpos : k ≤ Z i := by cases h : high i <;> simp_all [Z,target]
    have pred : (fun a => decide (a < Z i)) ∘ feed =
        (fun j => r j || decide (other high B T j < target high B T i)) := by
      funext j; cases h : r j <;> simp [feed,donor,h,Z,Nat.lt_of_lt_of_le j.isLt zpos]
    rw [pred]; exact enough i
  -- Build an alphabet of exactly 3*k distinct labels. All sentinels are
  -- above the *whole* physical reserve, not just the B on their own rows.
  let stock := col B ++ col X
  let G (i : Fin k) := stock.max?.getD 0 + 1 + i.val
  have bound {a : Nat} (h : a ∈ stock) (i) : a < G i := by
    have := List.le_max?_getD_of_mem (k := 0) h; dsimp [G]; omega
  have bstock (i) : B i ∈ stock := List.mem_append_left _ (mem_col B i)
  have xstock (i) : X i ∈ stock := List.mem_append_right _ (mem_col X i)
  have tstock (i) : T i ∈ stock := by
    obtain ⟨j,_,e⟩ := List.mem_map.mp (sortT.mem_iff.mpr (mem_col T i))
    rw [← e]; cases h : r j <;> simp [bstock,xstock]
  have dstock (i) : D i ∈ stock := by
    obtain ⟨j,_,e⟩ := List.mem_map.mp (sortD.mem_iff.mpr (mem_col D i))
    change feed j = D i at e
    rw [← e,feed_eq]; cases a : r j <;> cases h : high j <;> simp [h,other,xstock,tstock,bstock]
  have incG (i j : Fin k) (hlt : i < j) : G i < G j := Nat.add_lt_add_left hlt _
  let alphabet := stock ++ col G
  have physical : alphabet.Nodup := List.nodup_append.mpr ⟨bxnd,col_nd (inj incG),by
    intro a ha b hb eq; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
    exact Nat.ne_of_lt (bound ha i) eq⟩
  have len : alphabet.length = 3*k := by simp [alphabet,stock,col]; omega
  obtain ⟨rank,cmp,part⟩ := Rank.standardize physical len (by omega)
  have stk {a : Nat} (h : a ∈ stock) : a ∈ alphabet := List.mem_append_left _ h
  have gmem (i) : G i ∈ alphabet := List.mem_append_right _ (mem_col G i)
  have zmem (i) : Z i ∈ alphabet := by
    apply stk; cases h : high i <;> simp [Z,target,h,bstock,tstock]
  have zrank (i) : target high (rank ∘ B) (rank ∘ T) i = rank (Z i) := by
    cases h : high i <;> simp [Z,target,h]
  apply pinned high r (rank ∘ B) (rank ∘ G) (rank ∘ X) (rank ∘ T) (rank ∘ D)
  · have switch : alphabet.Perm (col B ++ (col G ++ col X)) := by
      dsimp [alphabet,stock]; rw [List.append_assoc]; exact List.perm_append_comm.append_left _
    simpa only [List.map_append,col,List.map_map] using part.symm.trans (switch.map rank)
  · exact fun i j lt => (cmp _ (stk (bstock i)) _ (stk (bstock j))).mpr (hB i j lt)
  · exact fun i j lt => (cmp _ (gmem i) _ (gmem j)).mpr (incG i j lt)
  · exact fun i j lt => (cmp _ (stk (tstock i)) _ (stk (tstock j))).mpr (hT i j lt)
  · exact fun i j lt => (cmp _ (stk (dstock i)) _ (stk (dstock j))).mpr (incD i j lt)
  · exact fun i => (cmp _ (stk (bstock i)) _ (gmem i)).mpr (bound (bstock i) i)
  · exact fun i => (cmp _ (stk (tstock i)) _ (gmem i)).mpr (bound (tstock i) i)
  · exact early
  · simpa only [Cert.Rebatch,col,List.map_map,Function.comp_def,apply_ite rank] using sortT.map rank
  · have eqn : (rank ∘ feed) = fun i => if r i then (rank ∘ X) i else
        other high (rank ∘ B) (rank ∘ T) i := by
      funext i; cases a : r i <;> cases h : high i <;> simp [feed_eq,other,a,h]
    simpa only [Cert.Rebatch,Rank.col,List.map_map,eqn] using sortD.map rank
  · intro i; rw [zrank]; exact (cmp _ (stk (dstock i)) _ (zmem i)).mpr (below i)
  · intro i j; rw [zrank,zrank,cmp _ (zmem i) _ (zmem j)]; exact order i j

/-- Realizability of the target order by the constructed certificate. -/
theorem realizable {k : Nat} (hk : 0 < k) (p : Fin k → Fin k)
    (B T : Fin k → Nat) (high r : Fin k → Bool)
    (hB : ∀ i j, i < j → B i < B j) (hT : ∀ i j, i < j → T i < T j)
    (floorB : ∀ i, k ≤ B i) (floorT : ∀ i, k ≤ T i)
    (cross : ∀ i, (∃ j, B i = T j) ↔ r i = true)
    (early : ∀ i, r i = true → high i = false)
    (enough : ∀ i : Fin k, i.val < (List.finRange k).countP
      (fun j => r j || decide (other high B T j < target high B T i)))
    (order : ∀ i j, target high B T i < target high B T j ↔ p i < p j) : Realizable p :=
  (certificate hk p B T high r hB hT floorB floorT cross early enough order).realizable hk

end StarFiring.Padding.Pin
