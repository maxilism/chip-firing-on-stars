import StarFiring.Projection
import StarFiring.ArmTemplate
import StarFiring.Balance
import StarFiring.Physical
import StarFiring.Replay

/-! Accounting by physical label at center cuts.  The row that returns a label
and the row that receives it at a later center firing need not coincide. -/
namespace StarFiring

def centerBatches (ms : List (Move k)) : List (Batch k) := ms.filterMap fun
  | .center b => some b | .arm .. => none

def armReturns (es : List (ArmEvent k)) : List (Chip k) := es.filterMap fun
  | .compare 0 a _ => some a | _ => none

def sent (ms : List (Move k)) := (centerBatches ms).flatMap fun b => (List.finRange k).map b

def returned (ms : List (Move k)) := (List.finRange k).flatMap fun i => armReturns (armTrace i ms)

namespace Center

theorem batchCount {b : Batch k} (hb : Increasing b) (x : Chip k) :
    (((List.finRange k).map b).count x : Int) = ind (Has b x) := by
  have hn : ((List.finRange k).map b).Nodup := (List.nodup_finRange k).map b (fun i j h he => h (increasing_injective hb he))
  rw [hn.count]; simp [List.mem_map,List.mem_finRange,Has,ind]; split <;> simp_all

theorem flatMap_split (xs : List α) (f g : α → List β) :
    (xs.flatMap fun i => f i ++ g i).Perm (xs.flatMap f ++ xs.flatMap g) := by
  induction xs with
  | nil => simp
  | cons i is ih =>
    simp only [List.flatMap_cons,List.append_assoc]
    apply List.Perm.append_left
    refine (ih.append_left _).trans ?_
    simpa only [List.append_assoc] using (List.perm_append_comm (l₁ := g i) (l₂ := is.flatMap f)).append_right (is.flatMap g)

private theorem singletonAt (xs : List (Row k)) (j : Row k) (a : Chip k) :
    (xs.flatMap fun i => if i=j then [a] else []) = List.replicate (xs.count j) a := by
  induction xs with
  | nil => simp
  | cons i is ih => by_cases h : i=j <;> simp [h,ih,List.replicate_succ]

@[simp] theorem returned_center (b : Batch k) (ms : List (Move k)) :
    returned (.center b :: ms) = returned ms := by
  simp [returned,armTrace,armReturns,Move.onArm]

private theorem returned_arm {i : Row k} (d : Nat) (a b : Chip k) (ms : List (Move k)) :
    (returned (.arm i d a b :: ms)).Perm ((if d=0 then [a] else []) ++ returned ms) := by
  have h (j : Row k) : armReturns (armTrace j (.arm i d a b :: ms)) =
      (if j=i then (if d=0 then [a] else []) else []) ++ armReturns (armTrace j ms) := by
    by_cases e : j=i <;> cases d <;> simp [armTrace,armReturns,Move.onArm,e]
  unfold returned
  simp only [h]
  refine (flatMap_split ..).trans (.of_eq ?_)
  cases d with
  | zero => simp [singletonAt, (List.nodup_finRange k).count, List.mem_finRange]
  | succ d => simp

end Center

/-- Exact integer ledger for *every* prefix, not only saturated ones. -/
theorem Run.center_counts {s t : Config k} {ms : List (Move k)} (h : Run s ms t) (x : Chip k) :
    t .center x + ((sent ms).count x : Int) = s .center x + ((returned ms).count x : Int) := by
  induction h with
  | nil =>
    have z : ((List.finRange k).flatMap fun _ => ([] : List (Chip k))) = [] := List.flatMap_eq_nil_iff.mpr (by simp)
    simp [sent,centerBatches,returned,armTrace,armReturns,z]
  | @cons ms t s m hl _ ih =>
    cases m with
    | center b =>
      rw [Center.returned_center]
      have hb := Center.batchCount hl.1 x
      simp only [Move.act,Move.delta] at ih
      simp only [sent,centerBatches,List.filterMap_cons,List.flatMap_cons,List.count_append,Int.natCast_add] at *
      omega
    | arm i d a b =>
      rw [(Center.returned_arm d a b ms).count_eq]
      cases d <;> by_cases e : a=x <;>
        simp [sent,centerBatches,Move.act,Move.delta,ind,inward,e] at * <;> omega

namespace Center
private theorem zero_of_sum_zero {xs : List α} {f : α → Int} (hf : ∀ i ∈ xs, 0 ≤ f i)
    (hs : (xs.map f).sum = 0) : ∀ i ∈ xs, f i = 0 := by
  have nonneg {ys : List α} (hn : ∀ i ∈ ys, 0 ≤ f i) : 0 ≤ (ys.map f).sum := by
    induction ys with
    | nil => simp
    | cons y ys ih => simp only [List.map_cons,List.sum_cons]; have := hn y (by simp); have := ih (fun i h => hn i (by simp [h])); omega
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have h' : ∀ i ∈ ys, 0 ≤ f i := fun i h => hf i (by simp [h])
    have := nonneg h'; have := hf y (by simp); simp at hs
    intro i hi; rcases List.mem_cons.mp hi with rfl|hi
    · omega
    · exact ih h' (by omega) i hi

/-- At a cut of load `k`, a legal center firing takes *all* present labels. -/
theorem exhausted_batch {b : Batch k} {s : Config k} (hl : (Move.center b).Legal s)
    (hn : ∀ x, 0 ≤ s .center x) (hk : load s .center = k) (x : Chip k) :
    s .center x = ind (Has b x) := by
  let f := fun x => s .center x - ind (Has b x)
  have hpos (x) : 0 ≤ f x := by
    by_cases h : Has b x
    · obtain ⟨i,hi⟩ := h; have := hl.2 i; rw [hi] at this
      simp [f,ind,show Has b x from ⟨i,hi⟩]; omega
    · simpa [f,ind,h] using hn x
  have sub (ys : List (Chip k)) : (ys.map f).sum = (ys.map (s .center)).sum - (ys.map fun x => ind (Has b x)).sum := by
    induction ys <;> simp_all [f] <;> omega
  have z := zero_of_sum_zero (xs := List.finRange (3*k)) (f := f) (fun i _ => hpos i)
    (by rw [sub,sum_ind_has b hl.1]; change load s .center - _ = 0; omega) x (List.mem_finRange x)
  dsimp [f] at z; omega

abbrev col (b : Batch k) := (List.finRange k).map b
abbrev lo (a b : Batch k) : Batch k := fun i => min (a i) (b i)
abbrev hi (a b : Batch k) : Batch k := fun i => max (a i) (b i)

private theorem flatMap_perm (rs : List α) {f g : α → List β} (h : ∀ i, (f i).Perm (g i)) :
    (rs.flatMap f).Perm (rs.flatMap g) := by
  induction rs with
  | nil => simp
  | cons i is ih => exact (h i).append ih

@[simp] private theorem flat_single (l : List α) (f : α → β) : (l.flatMap fun i => [f i]) = l.map f := by
  induction l <;> simp_all

private theorem min_ite (a b : Chip k) : min a b = if a ≤ b then a else b := by split <;> apply Fin.ext <;> simp [Fin.le_def] at * <;> omega
private theorem max_ite (a b : Chip k) : max a b = if a ≤ b then b else a := by split <;> apply Fin.ext <;> simp [Fin.le_def] at * <;> omega

theorem pair_split (a b : Batch k) : ((List.finRange k).flatMap fun i => [a i,b i]).Perm (col a ++ col b) := by
  simpa using (flatMap_split (List.finRange k) (fun i => [a i]) (fun i => [b i]))

theorem triple_split (a b c : Batch k) : ((List.finRange k).flatMap fun i => [a i,b i,c i]).Perm (col a ++ (col b ++ col c)) := by
  have aux := flatMap_split (List.finRange k) (fun i => [a i]) (fun i => [b i,c i])
  exact (by simpa using aux : ((List.finRange k).flatMap fun i => [a i,b i,c i]).Perm
    (col a ++ (List.finRange k).flatMap fun i => [b i,c i])).trans ((pair_split b c).append_left _)

theorem sorted_pair_bag (A B : Batch k) : (col A ++ col B).Perm (col (lo A B) ++ col (hi A B)) := by
  apply (pair_split A B).symm.trans; apply List.Perm.trans _ (pair_split ..)
  apply flatMap_perm; intro i
  by_cases h : A i ≤ B i
  · simp [lo,hi,min_ite,max_ite,h]
  · simp [lo,hi,min_ite,max_ite,h,List.Perm.swap]

theorem sorted_pair_inc {A B : Batch k} (ha : Increasing A) (hb : Increasing B) :
    Increasing (lo A B) ∧ Increasing (hi A B) := by
  constructor <;> intro i j h <;> have h₁ := ha i j h <;> have h₂ := hb i j h <;>
    simp only [lo,hi,min_ite,max_ite,Fin.lt_def] at * <;> split <;> split <;>
    simp_all [Fin.le_def] <;> omega

private theorem col_nodup {A : Batch k} (ha : Increasing A) : (col A).Nodup :=
  (List.nodup_finRange k).map A (fun _ _ ne e => ne (increasing_injective ha e))

@[simp] theorem mem_col (a : Batch k) (x : Chip k) : x ∈ col a ↔ Has a x := by
  simp [col,Has,List.mem_finRange]

theorem first_disjoint {A B : Batch k} (h : (Move.center B).Legal ((Move.center A).act (initial k))) :
    ∀ x, Has A x → ¬ Has B x := by
  rintro x hx ⟨i,hi⟩; have hpos := h.2 i; rw [hi] at hpos; simp [Move.act,Move.delta,ind,initial,hx] at hpos

theorem sorted_pair_facts {A B : Batch k} (ha : Increasing A) (hb : Increasing B)
    (hd : ∀ x, Has A x → ¬ Has B x) :
    Increasing (lo A B) ∧ Increasing (hi A B) ∧ (∀ i, lo A B i < hi A B i) ∧
    (∀ x, Has (lo A B) x → ¬ Has (hi A B) x) := by
  obtain ⟨hin,him⟩ := sorted_pair_inc ha hb
  have nd : (col A ++ col B).Nodup := List.nodup_append.mpr ⟨col_nodup ha,col_nodup hb,by rintro a ha b hb rfl; exact hd a ((mem_col ..).mp ha) ((mem_col ..).mp hb)⟩
  have d := (List.nodup_append.mp ((sorted_pair_bag A B).nodup nd)).2.2
  refine ⟨hin,him,?_,fun x hl hh => d x ((mem_col ..).mpr hl) x ((mem_col ..).mpr hh) rfl⟩
  intro i; have hne : A i ≠ B i := fun e => hd _ ⟨i,rfl⟩ ⟨i,e.symm⟩
  have hn : (A i).val ≠ (B i).val := fun e => hne (Fin.ext e)
  simp only [lo,hi,Fin.lt_def,Fin.val_min,Fin.val_max]; omega

/-- Replacing the first two deliveries keeps the *labeled* board, at every site. -/
theorem sorted_pair_board {A B : Batch k} {s : Config k} (ha : Increasing A) (hb : Increasing B) :
    (Move.center (hi A B)).act ((Move.center (lo A B)).act s) = (Move.center B).act ((Move.center A).act s) := by
  funext t x; obtain ⟨hl,hh⟩ := sorted_pair_inc ha hb
  cases t with
  | center =>
    have h := congrArg Int.ofNat ((sorted_pair_bag A B).count x)
    change (((col A ++ col B).count x : Nat) : Int) = (((col (lo A B) ++ col (hi A B)).count x : Nat) : Int) at h
    simp only [List.count_append,Int.natCast_add,batchCount ha,batchCount hb,batchCount hl,batchCount hh] at h
    simp only [Move.act,Move.delta]; omega
  | arm i d =>
    cases d with
    | zero => simp only [Move.act,Move.delta,lo,hi,min_ite,max_ite]; split <;> omega
    | succ d => rfl

theorem sorted_pair_legal {A B : Batch k} (ha : Increasing A) (hb : Increasing B) (hd : ∀ x, Has A x → ¬ Has B x) :
    Run (initial k) [.center (lo A B), .center (hi A B)] ((Move.center B).act ((Move.center A).act (initial k))) := by
  obtain ⟨hl,hh,_,hd'⟩ := sorted_pair_facts ha hb hd
  refine .cons ⟨hl,by simp [initial,ind]⟩ (.cons ⟨hh,?_⟩ ?_)
  · intro i; have hn : ¬ Has (lo A B) (hi A B i) := fun h => hd' _ h ⟨i,rfl⟩
    simp [Move.act,Move.delta,initial,ind,hn]
  · rw [sorted_pair_board ha hb]; exact .nil

/-- `spare` is the complete unused complement of the first two batches. No
sorting of replay *destinations* occurs here: the possibility of a replay is
a membership condition in the list `early` of returns from all source arms. -/
theorem resources {A B T D R : Batch k} {early : List (Chip k)}
    (ha : Increasing A) (hb : Increasing B)
    (hB : ∀ x, 0 ≤ (1:Int) - (col A).count x - (col B).count x)
    (hT : ∀ x, 0 ≤ (1:Int) - (col A).count x - (col B).count x - (col T).count x + early.count x)
    (hD : ∀ x, (0:Int) = 1 - (col A).count x - (col B).count x - (col T).count x - (col D).count x + (col R).count x) :
    (∀ x, Has A x → ¬ Has B x) ∧ ∃ spare : List (Chip k),
    (List.finRange (3*k)).Perm (col (lo A B) ++ (col (hi A B) ++ spare)) ∧
    (∀ x, Has T x → x ∈ spare ∨ x ∈ early) ∧
    (∀ x, (col T).count x + (col D).count x = spare.count x + (col R).count x) := by
  let used := col A ++ col B
  let all := List.finRange (3*k)
  let spare := all.filter fun x => x ∉ used
  have hd : ∀ x, Has A x → ¬ Has B x := by
    intro x hA hB'; have h := hB x
    have h' := List.count_pos_iff.mpr ((mem_col A x).mpr hA)
    have h'' := List.count_pos_iff.mpr ((mem_col B x).mpr hB'); omega
  have nd : used.Nodup := List.nodup_append.mpr ⟨col_nodup ha,col_nodup hb,by
    rintro x xa y yb rfl; exact hd _ ((mem_col ..).mp xa) ((mem_col ..).mp yb)⟩
  have ms (x) : x ∈ spare ↔ x ∉ used := by simp [spare,all,List.mem_finRange]
  have ns : spare.Nodup := (List.nodup_finRange (3*k)).filter _
  have hpart : all.Perm (used ++ spare) := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_finRange _) (List.nodup_append.mpr ⟨nd,ns,?_⟩)).mpr
    · intro x; simp [List.mem_finRange,ms,Classical.em]
    · rintro x hx y hy rfl; exact (ms _).mp hy hx
  refine ⟨hd,spare,?_,?_,?_⟩
  · simpa only [List.append_assoc] using hpart.trans ((sorted_pair_bag A B).append_right spare)
  · intro x ht
    by_cases h : x ∈ used
    · right; apply List.count_pos_iff.mp
      have usedPos := List.count_pos_iff.mpr h
      have tPos := List.count_pos_iff.mpr ((mem_col ..).mpr ht)
      simp only [used,List.count_append] at usedPos; have := hT x; omega
    · exact .inl ((ms _).mpr h)
  · intro x
    have h1 : all.count x = 1 := by simp [all,(List.nodup_finRange _).count,List.mem_finRange]
    have h := hpart.count x
    simp only [used,List.count_append,h1] at h; have := hD x; omega

private theorem four_split (a b c d : Batch k) :
    ((List.finRange k).flatMap fun i => [a i,b i,c i,d i]).Perm (col a ++ (col b ++ (col c ++ col d))) := by
  have aux := flatMap_split (List.finRange k) (fun i => [a i]) (fun i => [b i,c i,d i])
  exact (by simpa using aux : ((List.finRange k).flatMap fun i => [a i,b i,c i,d i]).Perm
    (col a ++ (List.finRange k).flatMap fun i => [b i,c i,d i])).trans ((triple_split b c d).append_left _)

/-- Fourth-batch complement: with `y` and `z` retained on the arms, the fourth
batch contains *exactly* the other physical labels. In particular there are no
duplicate labels among these three columns, including on a replay arm. -/
theorem fourth_partition {c : Cert k} (cv : c.Valid) :
    (List.finRange (3*k)).Perm (col c.D ++ (col c.y ++ col c.z)) := by
  have hrow (i : Row k) : [c.L i,c.H i,c.X i,c.T i].Perm [c.feedT i,c.feedD i,c.y i,c.z i] := by
    cases hm : c.mode i <;> simp only [Cert.feedT,Cert.feedD,Cert.y,Cert.z,hm,min_ite,max_ite] <;>
    try split
    all_goals apply List.perm_iff_count.mpr; intro x; simp [List.count_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  have hp := (four_split c.L c.H c.X c.T).symm.trans ((flatMap_perm (List.finRange k) hrow).trans (four_split ..))
  have hi := cv.partition.trans (triple_split ..)
  apply List.perm_iff_count.mpr; intro x
  have p1 := hp.count x; have p2 := hi.count x; have p3 := cv.sortT.count x; have p4 := cv.sortD.count x
  change (col c.feedT).count x = (col c.T).count x at p3
  change (col c.feedD).count x = (col c.D).count x at p4
  simp only [List.count_append] at *; omega

/-- Count a cut by any predicate on physical labels. Taking a small-label
threshold recovers the fourth prefix without guessing replay destinations. -/
theorem fourth_cut {c : Cert k} (cv : c.Valid) (small : Chip k → Bool) :
    (col c.D).countP small + (col c.y).countP small + (col c.z).countP small =
    (List.finRange (3*k)).countP small := by
  have hh := (fourth_partition cv).countP_eq small
  simp only [List.countP_append] at hh; omega

private theorem count_fin_cut (n s : Nat) (hs : s ≤ n) :
    (List.finRange n).countP (fun x => x.val < s) = s := by
  let f : Fin s → Fin n := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hs⟩
  have hf : Function.Injective f := fun _ _ e => Fin.ext (congrArg (fun q : Fin n => q.val) e)
  have hn : ((List.finRange s).map f).Nodup := (List.nodup_finRange s).map f (fun _ _ ne e => ne (hf e))
  have eqv : ((List.finRange n).filter (fun x => x.val < s)).Perm ((List.finRange s).map f) := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange n).filter _) hn).mpr
    intro i; simp only [List.mem_filter,List.mem_map,List.mem_finRange,true_and,decide_eq_true_eq]
    constructor
    · intro h; exact ⟨⟨i.val,h⟩,rfl⟩
    · rintro ⟨j,rfl⟩; exact j.isLt
  rw [List.countP_eq_length_filter,eqv.length_eq]; simp

/-- For each physical prefix (zero-based ranks), `d = s - ySmall - zSmall`. -/
theorem fourth_prefix {c : Cert k} (cv : c.Valid) (s : Nat) (hs : s ≤ 3*k) :
    (col c.D).countP (fun x => x.val < s) = s - (col c.y).countP (fun x => x.val < s) -
      (col c.z).countP (fun x => x.val < s) := by
  have h := fourth_cut cv (fun x => x.val < s); rw [count_fin_cut _ _ hs] at h; omega

end Center
end StarFiring
