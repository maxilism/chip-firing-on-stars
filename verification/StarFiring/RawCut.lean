import StarFiring.Projection
import StarFiring.Replay
import StarFiring.Balance

/-! Net change to a physical label's center inventory up to (and including)
a specified dispatch. Arm projections stutter on precisely the other rows. -/
namespace StarFiring

def rowsTotal (f : Row k → Int) : Int := ((List.finRange k).map f).sum

def traceCut (n : Nat) (es : List (ArmEvent k)) (x : Chip k) : Int := match n, es with
  | 0, _ | _, [] => 0
  | n+1, .deliver a :: tail => -ind (a=x) + traceCut n tail x
  | n+1, .compare d a _ :: tail => ind (d=0) * ind (a=x) + traceCut (n+1) tail x

private theorem total_sum (f g : Row k → Int) : rowsTotal (fun i => f i + g i) = rowsTotal f + rowsTotal g := by
  unfold rowsTotal; generalize List.finRange k = is; induction is <;> simp_all <;> omega

private theorem total_neg (f : Row k → Int) : rowsTotal (fun i => -f i) = -rowsTotal f := by
  unfold rowsTotal; generalize List.finRange k = is; induction is <;> simp_all <;> omega

private theorem mapInd (is : List α) [DecidableEq β] (f : α → β) (x : β) :
    (is.map (fun i => ind (f i = x))).sum = ((is.map f).count x : Int) := by
  induction is with
  | nil => rfl
  | cons j js ih => by_cases h : f j=x <;> simp only [List.map_cons,List.sum_cons,ih] <;> simp [ind,h,Int.add_comm]

private theorem total_batch {b : Batch k} (hi : Increasing b) (x : Chip k) :
    rowsTotal (fun i => ind (b i = x)) = ind (Has b x) := by
  rw [rowsTotal,mapInd]
  have hn : ((rows k).map b).Nodup := (List.nodup_finRange k).map b (fun _ _ ne e => ne (increasing_injective hi e))
  rw [hn.count]; simp [rows,List.mem_map,List.mem_finRange,Has,ind]; split <;> simp_all

private theorem total_single (j : Row k) (v : Int) : rowsTotal (fun i => if i=j then v else 0) = v := by
  have aux (is : List (Row k)) : (is.map (fun i => if i=j then v else 0)).sum = is.count j * v := by
    induction is with
    | nil => simp
    | cons i is ih => by_cases h : i=j <;> simp [h,ih,Int.add_mul,Int.add_comm]
  simp [rowsTotal,aux,(List.nodup_finRange k).count_of_mem (List.mem_finRange j)]

private theorem total_zero : rowsTotal (fun _ : Row k => 0) = 0 := by simp [rowsTotal,List.map_const']

/-- Every dispatch prefix can spend only physically present labels. This
statement applies even when the budget exceeds the length of the run. -/
theorem Run.cut_bound {s t : Config k} {ms : List (Move k)} (h : Run s ms t)
    (hn : ∀ p x, 0 ≤ s p x) (n : Nat) (x : Chip k) :
    0 ≤ s .center x + rowsTotal (fun i => traceCut n (armTrace i ms) x) := by
  induction h generalizing n with
  | nil => cases n <;> simpa [armTrace,traceCut,total_zero] using hn .center x
  | @cons ms t s m hl _ ih =>
    have hn' := nonneg_act hn hl
    cases n with
    | zero => simpa [traceCut,total_zero] using hn .center x
    | succ n =>
      cases m with
      | center b =>
        have hnext := ih hn' n
        simp only [armTrace, List.filterMap_cons, Move.onArm, traceCut, total_sum, total_neg, total_batch hl.1]
        simp only [Move.act,Move.delta,armTrace] at hnext; omega
      | arm j d a b =>
        have hnext := ih hn' (n+1)
        have step (i : Row k) : traceCut (n+1) (armTrace i (.arm j d a b :: ms)) x =
            (if i=j then ind (d=0)*ind (a=x) else 0) + traceCut (n+1) (armTrace i ms) x := by
          by_cases he : i=j <;> simp [armTrace,Move.onArm,he,traceCut]
        simp only [step,total_sum,total_single]; cases d <;> simp [Move.act,Move.delta,inward,ind] at hnext ⊢ <;> omega

theorem Run.cut_nonneg {t : Config k} {ms : List (Move k)} (h : Run (initial k) ms t) (n : Nat) (x : Chip k) :
    0 ≤ 1 + rowsTotal (fun i => traceCut n (armTrace i ms) x) := h.cut_bound initial_nonneg n x

end StarFiring
