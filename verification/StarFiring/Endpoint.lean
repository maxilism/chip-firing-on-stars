import StarFiring.Replay

namespace StarFiring

def endpointTokens (inn mid out : Batch k) (i : Row k) : List (Token k) :=
  [(.arm i 0,inn i),(.arm i 1,mid i),(.arm i 2,out i)]

def endpoint (inn mid out : Batch k) := board ((rows k).flatMap (endpointTokens inn mid out))

private def column {k} (inn mid out : Batch k) (i : Row k) (d : Nat) (x : Chip k) : Int :=
  match d with | 0 => ind (inn i = x) | 1 => ind (mid i = x) | 2 => ind (out i = x) | _ => 0

private theorem board_rows (inn mid out : Batch k) (l : List (Row k)) (hl : l.Nodup) (p : Site k) (x : Chip k) :
    board (l.flatMap (endpointTokens inn mid out)) p x =
    match p with | .center => 0 | .arm i d => if i ∈ l then column inn mid out i d x else 0 := by
  induction l with
  | nil => cases p <;> simp [board]
  | cons j l ih =>
    obtain ⟨hj,hn⟩ := List.nodup_cons.mp hl
    rw [List.flatMap_cons, board_append,ih hn]; unfold endpointTokens
    simp only [board_cons,show ∀ (p : Site k) x, board [] p x = 0 by intros; rfl]
    cases p with
    | center => simp [ind]
    | arm i d =>
      by_cases he : i = j
      · subst i; cases d with
        | zero => simp [ind,column,hj]
        | succ d => cases d with
          | zero => simp [ind,column,hj]
          | succ d => cases d <;> simp [ind,column,hj]
      · simp [ind,he]

theorem endpoint_center (inn mid out : Batch k) (x : Chip k) : endpoint inn mid out .center x = 0 :=
  board_rows inn mid out (rows k) (List.nodup_finRange _) .center x

theorem endpoint_arm (inn mid out : Batch k) (i : Row k) (d x) : endpoint inn mid out (.arm i d) x =
    match d with | 0 => ind (inn i = x) | 1 => ind (mid i = x) | 2 => ind (out i = x) | _ => 0 := by
  unfold endpoint; rw [board_rows _ _ _ _ (List.nodup_finRange _)]; simp [List.mem_finRange,column]

private theorem sumIndicator [DecidableEq α] (a : α) (l : List α) :
    (l.map fun x => ind (a = x)).sum = (l.count a : Int) := by
  induction l with
  | nil => rfl
  | cons x xs ih => by_cases h : a = x <;> simp_all [ind, eq_comm, Int.add_comm]

theorem endpoint_stable {k} (hk : 0 < k) (inn mid out : Batch k) : Stable (endpoint inn mid out) := by
  constructor
  · unfold load; rw [show endpoint inn mid out .center = (fun _ => 0) from funext (endpoint_center inn mid out)]
    simp [List.map_const']; omega
  · intro i d
    unfold load; rw [funext (endpoint_arm inn mid out i d)]
    have hs (a : Chip k) : ((List.finRange (3*k)).map fun x => ind (a = x)).sum = 1 := by
      rw [sumIndicator, (List.nodup_finRange _).count_of_mem (List.mem_finRange _)]; rfl
    cases d with
    | zero => simp [hs]
    | succ d => cases d with
      | zero => simp [hs]
      | succ d => cases d with
        | zero => simp [hs]
        | succ d => simp [List.map_const']

theorem endpoint_middle_iff (inn mid out : Batch k) (p : Row k → Row k) :
    MiddleOrder (endpoint inn mid out) p ↔ ∀ i j, mid i < mid j ↔ p i < p j := by
  constructor
  · rintro ⟨b,hb,hp⟩
    have he : ∀ i, mid i = b i := fun i => by
      have h := hb i; simp only [endpoint_arm,ind] at h; split at h <;> simp_all
    simpa only [he] using hp
  · intro h; exact ⟨mid,fun i => by simp [endpoint_arm,ind],h⟩
end StarFiring
