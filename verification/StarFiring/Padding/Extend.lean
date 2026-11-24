import StarFiring.Padding.Layout

/-! Extend the original two streams by identical, increasingly large entries.
Each tail row therefore reuses its own chip and contributes a new tiny spare.
All old labels are shifted above the `n+t` possible spare labels. -/
namespace StarFiring.Padding

private theorem member_le_sum {x : Nat} {l : List Nat} (hx : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at hx
  | cons a as ih => rcases List.mem_cons.mp hx with rfl|h <;> simp <;> first | omega | have := ih h; omega

private def ceiling {w : Row n → Row n} (l : Layout w) :=
  (List.ofFn l.B).sum + (List.ofFn l.T).sum + 1
private theorem below {w : Row n → Row n} (l : Layout w) (i : Fin n) :
    l.B i < ceiling l ∧ l.T i < ceiling l := by
  have b := member_le_sum (List.mem_ofFn.mpr (show ∃ j, l.B j = l.B i from ⟨i,rfl⟩))
  have t := member_le_sum (List.mem_ofFn.mpr (show ∃ j, l.T j = l.T i from ⟨i,rfl⟩))
  unfold ceiling; omega

private def extendCol (f : Row n → Nat) (t c : Nat) : Row (n+t) → Nat :=
  Fin.addCases (fun i => n+t+f i) (fun h => n+t+c+h.val)

private theorem extend_inc {f : Row n → Nat} (t c : Nat) (inc : ∀ i j, i < j → f i < f j) (lt : ∀ i, f i < c) :
    ∀ i j, i < j → extendCol f t c i < extendCol f t c j := by
  intro i j
  induction i using Fin.addCases <;> induction j using Fin.addCases
  all_goals simp only [extendCol,Fin.addCases_left,Fin.addCases_right,Fin.lt_def,Fin.val_castAdd,Fin.val_natAdd]
  · intro h; have := inc _ _ h; omega
  · rename_i i j; have := lt i; omega
  · rename_i i j; have := j.isLt; omega
  · omega

private theorem extend_share {w : Row n → Row n} (l : Layout w) (t : Nat) (i : Row (n+t)) :
    Fin.addCases (motive := fun _ : Row (n+t) => Bool) l.replay (fun _ => true) i = true ↔
      ∃ j, extendCol l.B t (ceiling l) i = extendCol l.T t (ceiling l) j := by
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.addCases_left, l.share]
    constructor
    · rintro ⟨j,h⟩; exact ⟨j.castAdd t,by simp [extendCol,h]⟩
    · rintro ⟨j,h⟩; induction j using Fin.addCases with
      | left j => exact ⟨j,by simpa [extendCol] using h⟩
      | right j => have b := (below l i).1; simp [extendCol] at h; omega
  | right h => simp only [Fin.addCases_right,true_iff]; exact ⟨Fin.natAdd n h,by simp [extendCol]⟩

private theorem keep_left {w : Row n → Row n} (l : Layout w) (t : Nat) (i : Row n) :
    keep (pad w t) (extendCol l.B t (ceiling l)) (extendCol l.T t (ceiling l)) (i.castAdd t) =
    n+t+keep w l.B l.T i := by
  simp only [keep,pad_left,extendCol,Fin.addCases_left]; change (if i < w i then _ else _) = _
  split <;> rfl

private theorem give_left {w : Row n → Row n} (l : Layout w) (t : Nat) (i : Row n) :
    give (pad w t) (extendCol l.B t (ceiling l)) (extendCol l.T t (ceiling l)) (i.castAdd t) =
    n+t+give w l.B l.T i := by
  simp only [give,pad_left,extendCol,Fin.addCases_left]; change (if i < w i then _ else _) = _
  split <;> rfl

private theorem keep_lt {w : Row n → Row n} (l : Layout w) (i) : keep w l.B l.T i < ceiling l := by
  unfold keep; split <;> first | exact (below l i).1 | exact (below l i).2
private theorem give_lt {w : Row n → Row n} (l : Layout w) (i) : give w l.B l.T i < ceiling l := by
  unfold give; split <;> first | exact (below l i).1 | exact (below l i).2

/-- On every padded row the replay source and destination agree. They need not
agree on the original rows. -/
def Layout.extend {w : Row n → Row n} (l : Layout w) (t : Nat) : Layout (pad w t) where
  B := extendCol l.B t (ceiling l)
  T := extendCol l.T t (ceiling l)
  replay := Fin.addCases l.replay (fun _ => true)
  strictB := extend_inc t _ l.strictB (fun i => (below l i).1)
  strictT := extend_inc t _ l.strictT (fun i => (below l i).2)
  share := extend_share l t
  low := by
    intro i; induction i using Fin.addCases with
    | left i => simpa only [pad_left,Fin.addCases_left,Fin.lt_def,Fin.val_castAdd] using l.low i
    | right i => simp [pad]
  ranks := by
    intro i j; induction i using Fin.addCases <;> induction j using Fin.addCases
    all_goals simp only [keep_left,pad_right,pad_left]
    · simpa [Fin.lt_def] using l.ranks _ _
    · rename_i i j; have h := keep_lt l i; have hz := (w i).isLt
      simp [keep,extendCol,Fin.lt_def] at h ⊢; omega
    · rename_i i j; have h := keep_lt l j; have hz := (w j).isLt
      simp [keep,extendCol,Fin.lt_def] at h ⊢; omega
    · simp [keep,extendCol,Fin.lt_def]

theorem Layout.shifted {w : Row n → Row n} (l : Layout w) (t : Nat) (i : Row (n+t)) :
    n+t ≤ (l.extend t).B i ∧ n+t ≤ (l.extend t).T i := by
  induction i using Fin.addCases <;> simp [Layout.extend,extendCol] <;> omega

private theorem rows_split (n t : Nat) : rows (n+t) =
    (rows n).map (Fin.castAdd t) ++ (rows t).map (Fin.natAdd n) := by
  simp only [rows,List.finRange,List.map_ofFn]; exact List.ofFn_add

/-- On original rows, adding `t` arms increases the supply below the pin by
exactly `t`. On a tail row all `n+t` fourth-batch chips are below its pin. -/
theorem Layout.extend_room {w : Row n → Row n} (l : Layout w) (t : Nat)
    (room : ∀ i : Row n, i.val < l.cheap i + t) :
    ∀ i : Row (n+t), i.val < (l.extend t).cheap i := by
  intro i
  let cheap := fun (i j : Row (n+t)) => (l.extend t).replay j || decide
    (give (pad w t) (l.extend t).B (l.extend t).T j < keep (pad w t) (l.extend t).B (l.extend t).T i)
  change i.val < (rows (n+t)).countP (cheap i)
  induction i using Fin.addCases with
  | left i =>
    rw [rows_split,List.countP_append,List.countP_map,List.countP_map]
    have hr : (rows t).countP (cheap (i.castAdd t) ∘ Fin.natAdd n) = t := by
      apply Eq.trans _ (List.length_finRange (n:=t)); apply List.countP_eq_length.mpr
      intro j _; simp [cheap,Layout.extend]
    have hl : (rows n).countP (cheap (i.castAdd t) ∘ Fin.castAdd t) = l.cheap i := by
      apply List.countP_congr; intro j _
      simp only [cheap,Function.comp_apply,Layout.extend,Fin.addCases_left,give_left,keep_left,Nat.add_lt_add_iff_left]
    rw [hl,hr]; exact room i
  | right i =>
    have h : (rows (n+t)).countP (cheap (Fin.natAdd n i)) = n+t := by
      apply Eq.trans _ (List.length_finRange (n:=n+t)); apply List.countP_eq_length.mpr
      intro j _; induction j using Fin.addCases with
      | left j =>
        simp only [cheap,Layout.extend,Fin.addCases_left,give_left,keep,extendCol,Fin.addCases_right,ite_self]
        have := give_lt l j; simp [show give w l.B l.T j < ceiling l + i.val by omega, Nat.add_assoc]
      | right j => simp [cheap,Layout.extend]
    rw [h]; exact (Fin.natAdd n i).isLt

end StarFiring.Padding
