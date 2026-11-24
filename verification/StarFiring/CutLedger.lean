import StarFiring.ArmEvents
import StarFiring.RawCut

/-! Accounting by label immediately after the nth delivery, retaining only
actual (not commuted) returns in the prefix. All indicators count physical
labels, even when the same label occurs in several successive batches. -/
namespace StarFiring

def chipsOf (f : Batch k) : List (Chip k) := (List.finRange k).map f

/-- The first inward return is available before T exactly on physically early
arms. Some late comparisons can be commuted earlier, but that is not assumed. -/
def earlyReturns (p : Row k → ArmTemplate k) : List (Chip k) :=
  (List.finRange k).flatMap fun i => if (p i).early then [(p i).r1] else []

/-- Multiset accounting just after the center dispatches B,T,D,E,F. -/
structure CutLedger (p : Row k → ArmTemplate k) : Prop where
  hB : ∀ x, (0 : Int) ≤ 1 - (chipsOf (fun i => (p i).A)).count x - (chipsOf (fun i => (p i).B)).count x
  hT : ∀ x, (0 : Int) ≤ 1 - (chipsOf (fun i => (p i).A)).count x - (chipsOf (fun i => (p i).B)).count x - (chipsOf (fun i => (p i).T)).count x + (earlyReturns p).count x
  hD : ∀ x, (0 : Int) = 1 - (chipsOf (fun i => (p i).A)).count x - (chipsOf (fun i => (p i).B)).count x - (chipsOf (fun i => (p i).T)).count x - (chipsOf (fun i => (p i).D)).count x + (chipsOf (fun i => (p i).r1)).count x
  hE : Cert.Rebatch (fun i => (p i).r2) (fun i => (p i).E)
  hF : Cert.Rebatch (fun i => (p i).r3) (fun i => (p i).F)

namespace CutLedger
private def bag (f : Batch k) (x : Chip k) : Int := (chipsOf f).count x

private theorem count_sum (l : List (Chip k)) :
    ((List.finRange (3*k)).map (fun x => (l.count x : Int))).sum = l.length := by
  induction l with
  | nil => simp [List.map_const']
  | cons a l ih =>
    have e (x : Chip k) : ((a::l).count x : Int) = ind (a = x) + (l.count x : Int) := by
      by_cases h : a=x <;> simp [h,ind,Int.add_comm]
    simp [e, sumMap_add, sum_ind_eq, ih, Int.add_comm]

private theorem sum_bag (f : Batch k) :
    ((List.finRange (3*k)).map (bag f)).sum = (k : Int) := by
  change ((List.finRange (3*k)).map (fun x => ((chipsOf f).count x : Int))).sum = _
  simpa [chipsOf] using count_sum (chipsOf f)

private theorem sumSub (xs : List α) (f g : α → Int) :
    (xs.map (fun x => f x - g x)).sum = (xs.map f).sum - (xs.map g).sum := by
  induction xs <;> simp_all <;> omega

private theorem all_zero {f : Chip k → Int} (h : ∀ x, 0 ≤ f x)
    (s : ((List.finRange (3*k)).map f).sum = 0) (x : Chip k) : f x = 0 := by
  have aux (l : List (Chip k)) : 0 ≤ (l.map f).sum ∧ (x ∈ l → f x ≤ (l.map f).sum) := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons,List.sum_cons,List.mem_cons]
      have := h a
      constructor
      · omega
      · rintro (rfl|hm)
        · omega
        · have := ih.2 hm; omega
  have := (aux (List.finRange (3*k))).2 (List.mem_finRange x)
  have := h x
  omega

private theorem sub_total (f g : Row k → Int) :
    rowsTotal (fun i => f i - g i) = rowsTotal f - rowsTotal g := sumSub _ _ _
private theorem add_total (f g : Row k → Int) :
    rowsTotal (fun i => f i + g i) = rowsTotal f + rowsTotal g := sumMap_add _ _ _
private theorem neg_total (f : Row k → Int) :
    rowsTotal (fun i => -f i) = -rowsTotal f := by
  unfold rowsTotal; generalize List.finRange k = l; induction l <;> simp_all <;> omega
private theorem bag_total (f : Batch k) (x : Chip k) : rowsTotal (fun i => ind (f i=x)) = bag f x := by
  unfold rowsTotal bag chipsOf
  generalize List.finRange k = l
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : f a=x <;> simp [ind,h,ih,Int.add_comm] at *
private theorem early_total (p : Row k → ArmTemplate k) (x : Chip k) :
    rowsTotal (fun i => if (p i).early then ind ((p i).r1 = x) else 0) = (earlyReturns p).count x := by
  unfold rowsTotal earlyReturns
  generalize List.finRange k = l
  induction l with
  | nil => rfl
  | cons a l ih => cases e : (p a).early <;> by_cases h : (p a).r1=x <;> simp [ind,e,h,ih,Int.add_comm] at *

private theorem t2 (p : ArmTemplate k) (x : Chip k) :
    traceCut 2 p.events x = -ind (p.A=x) - ind (p.B=x) := by
  cases e : p.early <;> simp [ArmTemplate.events,ArmTemplate.startEvents,e,traceCut] <;> omega
private theorem t3 (p : ArmTemplate k) (x : Chip k) :
    traceCut 3 p.events x = traceCut 2 p.events x - ind (p.T=x) + (if p.early then ind (p.r1=x) else 0) := by
  cases e : p.early <;> simp [ArmTemplate.events,ArmTemplate.startEvents,e,traceCut,ind] <;> omega
private theorem t4 (p : ArmTemplate k) (x : Chip k) :
    traceCut 4 p.events x = traceCut 2 p.events x - ind (p.T=x) - ind (p.D=x) + ind (p.r1=x) := by
  cases e : p.early <;> simp [ArmTemplate.events,ArmTemplate.startEvents,ArmTemplate.endEvents,e,traceCut,ind] <;> omega
private theorem t5 (p : ArmTemplate k) (x : Chip k) :
    traceCut 5 p.events x = traceCut 4 p.events x - ind (p.E=x) + ind (p.r2=x) := by
  cases e : p.early <;> cases z : p.outEarly <;> simp [ArmTemplate.events,ArmTemplate.startEvents,ArmTemplate.endEvents,e,z,traceCut,ind] <;> omega
private theorem t6 (p : ArmTemplate k) (x : Chip k) :
    traceCut 6 p.events x = traceCut 5 p.events x - ind (p.F=x) + ind (p.r3=x) := by
  cases e : p.early <;> cases z : p.outEarly <;> simp [ArmTemplate.events,ArmTemplate.startEvents,ArmTemplate.endEvents,e,z,traceCut,ind] <;> omega

/-- The cut inequalities suffice: at and after D the total remaining center
inventory is zero, so the nonnegative balance of *each label* vanishes. -/
theorem of_nonneg (p : Row k → ArmTemplate k)
    (h : ∀ n x, 0 ≤ 1 + rowsTotal (fun i => traceCut n (p i).events x)) : CutLedger p := by
  have h2 (x) := h 2 x
  have h3 (x) := h 3 x
  simp only [t2, sub_total, neg_total, bag_total] at h2
  simp only [t3, t2, add_total, sub_total, neg_total, bag_total, early_total] at h3
  let a := fun x => 1 - bag (fun i => (p i).A) x - bag (fun i => (p i).B) x -
      bag (fun i => (p i).T) x - bag (fun i => (p i).D) x + bag (fun i => (p i).r1) x
  have h4 (x) : 1 + rowsTotal (fun i => traceCut 4 (p i).events x) = a x := by
    dsimp [a]; simp only [t4,t2,add_total,sub_total,neg_total,bag_total]; omega
  have z4 (x) : a x = 0 := by
    apply all_zero (fun y => h4 y ▸ h 4 y) _ x
    simp only [a, sumMap_add, sumSub, sum_bag, List.map_const', List.length_finRange]
    simp; omega
  have next {n j : Nat} {f g : Batch k}
      (hn : ∀ x, 1 + rowsTotal (fun i => traceCut n (p i).events x) = 0)
      (step : ∀ i x, traceCut j (p i).events x = traceCut n (p i).events x - ind (g i=x) + ind (f i=x)) :
      (∀ x, 1 + rowsTotal (fun i => traceCut j (p i).events x) = 0) ∧ Cert.Rebatch f g := by
    have hj (x) : 1 + rowsTotal (fun i => traceCut j (p i).events x) = bag f x - bag g x := by
      simp only [step,add_total,sub_total,bag_total]; have := hn x; omega
    have zz (x) : bag f x - bag g x = 0 := by
      apply all_zero (f := fun x => bag f x - bag g x) (fun x => hj x ▸ h j x) _ x
      rw [sumSub, sum_bag, sum_bag]; omega
    refine ⟨fun x => (hj x).trans (zz x), List.perm_iff_count.mpr ?_⟩
    intro x
    have := zz x; unfold bag chipsOf at this; omega
  have h5 := next (fun x => (h4 x).trans (z4 x)) (fun i x => t5 (p i) x)
  have h6 := next h5.1 (fun i x => t6 (p i) x)
  refine ⟨?_, ?_, ?_, h5.2, h6.2⟩
  · intro x; have := h2 x; unfold bag at this; omega
  · intro x; have := h3 x; unfold bag at this; omega
  · intro x; exact (z4 x).symm

end CutLedger

theorem cutLedger_of_templates (p : Row k → ArmTemplate k)
    (h : ∀ n x, 0 ≤ 1 + rowsTotal (fun i => traceCut n (p i).events x)) : CutLedger p :=
  CutLedger.of_nonneg p h

end StarFiring
