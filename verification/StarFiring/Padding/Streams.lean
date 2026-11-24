import StarFiring.Padding.High

/-! # Realizing a gap match by two increasing columns

Prescribed ranks occupy block boundaries. Every free entry occupies an interior
slot of the block belonging to the last anchor (or block zero before all
anchors). We use disjoint ranges of offsets on the two columns. A matched B
entry is instead placed exactly at the boundary of its matched rank. -/

namespace StarFiring.Padding

/-- A completion of the two original columns; `m i` names the *value* replayed
by original row `i`, not the row to which it is replayed. -/
structure StreamData (w : Row n → Row n) (m : Row n → Option (Row n)) where
  B : Row n → Nat
  T : Row n → Nat
  Z : Row n → Nat
  incB : ∀ i j, i < j → B i < B j
  incT : ∀ i j, i < j → T i < T j
  pinB : ∀ i, High w i → B i = Z i
  pinT : ∀ i, ¬High w i → T i = Z i
  orderZ : ∀ i j, Z i < Z j ↔ w i < w j
  cross : ∀ i j, B i = T j ↔ m i = some (w j)
  coldT : ∀ p i, High w p → p ≤ i → T p < Z i
  coldB : ∀ p i, ¬High w p → m p = none →
    (∀ e, e < p → High w e → w e < w i) → B p < Z i

namespace StreamAux

private def ceilingOn (l : List α) (f : α → Nat) : Nat :=
  (l.map f).foldr max 0

private theorem ceilingOn_le {l : List α} {f : α → Nat} {v : Nat} :
    ceilingOn l f ≤ v ↔ ∀ a ∈ l, f a ≤ v := by
  induction l with
  | nil => simp [ceilingOn]
  | cons a l ih =>
    simp [ceilingOn] at ih ⊢
    simp [Nat.max_le, ih]

/-- Block of the last preceding prescribed rank. The maximum presentation does
not require a separate case for an empty prefix. -/
private def block (w : Row n → Row n) (P : Row n → Prop) [DecidablePred P]
    (i : Row n) : Nat :=
  ceilingOn (List.finRange n) (fun j => if j < i ∧ P j then (w j).val + 1 else 0)

private theorem block_le {w : Row n → Row n} {P : Row n → Prop} [DecidablePred P]
    {i : Row n} {v : Nat} : block w P i ≤ v ↔ ∀ j, j < i → P j → (w j).val + 1 ≤ v := by
  unfold block
  rw [ceilingOn_le]
  constructor
  · intro h j hji hj
    simpa [hji, hj] using h j (List.mem_finRange j)
  · intro h j _; split
    · rename_i hg; exact h j hg.1 hg.2
    · omega

private theorem before_le_block {w : Row n → Row n} {P : Row n → Prop} [DecidablePred P]
    {i j : Row n} (hji : j < i) (hj : P j) : (w j).val + 1 ≤ block w P i :=
  block_le.mp (Nat.le_refl _) j hji hj

private theorem block_mono {w : Row n → Row n} {P : Row n → Prop} [DecidablePred P]
    {i j : Row n} (hij : i < j) : block w P i ≤ block w P j := by
  apply block_le.mpr
  intro h hlt hp
  exact before_le_block (Fin.lt_trans hlt hij) hp

private def width (n : Nat) : Nat := n+n+1
private def enc (n a x : Nat) : Nat := a * width n + x

private theorem enc_lt_block {n a b x y : Nat} (hab : a < b) (hx : x < width n) :
    enc n a x < enc n b y := by
  unfold enc
  have h := Nat.mul_le_mul_right (width n) hab
  change (a+1) * width n ≤ b * width n at h
  rw [Nat.succ_mul] at h
  omega

private theorem enc_slot_lt {n a b x y : Nat} (hab : a ≤ b) (hxy : x < y) :
    enc n a x < enc n b y := by
  unfold enc
  have := Nat.mul_le_mul_right (width n) hab
  omega

private theorem enc_parts {n a b x y : Nat} (hx : x < width n) (hy : y < width n)
    (e : enc n a x = enc n b y) : a = b ∧ x = y := by
  have h : a = b := by
    rcases Nat.lt_trichotomy a b with h|h|h
    · exact False.elim (Nat.ne_of_lt (enc_lt_block h hx) e)
    · exact h
    · exact False.elim (Nat.ne_of_lt (enc_lt_block h hy) e.symm)
  subst b
  exact ⟨rfl, Nat.add_left_cancel e⟩

private def mark (a : Row n) := enc n (a.val + 1) 0
private theorem mark_lt (a b : Row n) : mark a < mark b ↔ a < b := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy a.val b.val with lt|eq|gt
    · exact lt
    · exact False.elim (Nat.ne_of_lt h (congrArg mark (Fin.ext eq)))
    · exact False.elim (Nat.lt_asymm h (enc_lt_block (Nat.succ_lt_succ gt) (by simp [width])))
  · intro h; exact enc_lt_block (Nat.succ_lt_succ h) (by simp [width])

private theorem mark_inj {a b : Row n} (e : mark a = mark b) : a = b := by
  have := (enc_parts (n := n) (x := 0) (y := 0) (by simp [width]) (by simp [width]) e).1
  apply Fin.ext; omega

private def Bfree (w : Row n → Row n) (i : Row n) := enc n (block w (High w) i) (i.val + 1)
private def Tfree (w : Row n → Row n) (i : Row n) :=
  enc n (block w (fun j => ¬High w j) i) (n+i.val+1)
private def bCol (w : Row n → Row n) (m : Row n → Option (Row n)) (i : Row n) :=
  match m i with
  | some t => mark t
  | none => if High w i then mark (w i) else Bfree w i
private def tCol (w : Row n → Row n) (i : Row n) :=
  if High w i then Tfree w i else mark (w i)

private theorem Bfree_lt {w : Row n → Row n} {i a : Row n}
    (h : ∀ j, j < i → High w j → w j < a) : Bfree w i < mark a := by
  apply enc_lt_block
  · exact Nat.lt_succ_of_le (block_le.mpr h)
  · simp only [width]; omega

private theorem Tfree_lt {w : Row n → Row n} {i a : Row n}
    (h : ∀ j, j < i → ¬ High w j → w j < a) : Tfree w i < mark a := by
  apply enc_lt_block
  · exact Nat.lt_succ_of_le (block_le.mpr h)
  · simp only [width]; omega

private theorem mark_lt_Bfree {w : Row n → Row n} {i j : Row n} (hji : j < i)
    (hj : High w j) : mark (w j) < Bfree w i :=
  enc_slot_lt (before_le_block hji hj) (Nat.zero_lt_succ _)

private theorem mark_lt_Tfree {w : Row n → Row n} {i j : Row n} (hji : j < i)
    (hj : ¬ High w j) : mark (w j) < Tfree w i :=
  enc_slot_lt (before_le_block hji hj) (Nat.zero_lt_succ _)

private theorem Bfree_inc (w : Row n → Row n) {i j : Row n} (h : i < j) : Bfree w i < Bfree w j :=
  enc_slot_lt (block_mono h) (Nat.succ_lt_succ h)

private theorem Tfree_inc (w : Row n → Row n) {i j : Row n} (h : i < j) : Tfree w i < Tfree w j :=
  enc_slot_lt (block_mono h) (Nat.succ_lt_succ (Nat.add_lt_add_left h n))

private theorem Bfree_ne_mark (w : Row n → Row n) (i a : Row n) : Bfree w i ≠ mark a := by
  intro h
  have := (enc_parts (x := i.val+1) (y := 0) (by simp only [width]; omega) (by simp [width]) h).2
  omega

private theorem Tfree_ne_mark (w : Row n → Row n) (i a : Row n) : Tfree w i ≠ mark a := by
  intro h
  have := (enc_parts (x := n+i.val+1) (y := 0) (by simp only [width]; omega) (by simp [width]) h).2
  omega

private theorem free_ne (w : Row n → Row n) (i j : Row n) : Bfree w i ≠ Tfree w j := by
  intro h
  have := (enc_parts (x := i.val+1) (y := n+j.val+1) (by simp only [width]; omega)
    (by simp only [width]; omega) h).2
  omega

end StreamAux

open StreamAux in
/-- Realize a match given only its order, separation from the two bounding
highs, and the suffix property within each gap. -/
def makeStreams (w : Row n → Row n) (m : Row n → Option (Row n))
    (inj : Function.Injective w)
    (record : ∀ {i j}, High w i → j < i → w j < w i)
    (lowInc : ∀ {i j}, ¬High w i → ¬High w j → i < j → w i < w j)
    (sourceLow : ∀ {i t}, m i = some t → ¬High w i)
    (targetLow : ∀ {i t b}, m i = some t → w b = t → ¬High w b)
    (afterHigh : ∀ {a t h}, m a = some t → High w h → h < a → w h < t)
    (beforeHigh : ∀ {a t h}, m a = some t → High w h → a < h → t < w h)
    (matchInc : ∀ {a t b u}, m a = some t → m b = some u → a < b → t < u)
    (suffix : ∀ {a t b}, m a = some t → m b = none → a < b → ∃ h, a<h ∧ h≤b ∧ High w h) :
    StreamData w m := by
  have coldT (p i : Row n) (hp : High w p) (hpi : p ≤ i) : Tfree w p < mark (w i) := by
    apply Tfree_lt
    intro j hj hjL
    have hji := Fin.lt_of_lt_of_le hj hpi
    by_cases hi : High w i
    · exact record hi hji
    · exact lowInc hjL hi hji
  refine {
    B := bCol w m, T := tCol w, Z := fun i => mark (w i),
    incB := ?_, incT := ?_, pinB := ?_, pinT := ?_, orderZ := fun i j => mark_lt ..,
    cross := ?_, coldT := ?_, coldB := ?_ }
  · intro i j hij
    cases mi : m i with
    | some t =>
      cases mj : m j with
      | some u => simpa [bCol, mi, mj] using (mark_lt t u).mpr (matchInc mi mj hij)
      | none =>
        by_cases hj : High w j
        · simpa [bCol, mi, mj, hj] using (mark_lt t _).mpr (beforeHigh mi hj hij)
        · obtain ⟨h, hih, hhj, hh⟩ := suffix mi mj hij
          have hne : h ≠ j := by intro e; subst j; exact hj hh
          have hlt : h < j := Nat.lt_of_le_of_ne hhj (fun e => hne (Fin.ext e))
          simpa [bCol, mi, mj, hj] using Nat.lt_trans ((mark_lt t _).mpr (beforeHigh mi hh hih)) (mark_lt_Bfree hlt hh)
    | none =>
      cases mj : m j with
      | some t =>
        by_cases hi : High w i
        · simpa [bCol, mi, mj, hi] using (mark_lt _ t).mpr (afterHigh mj hi hij)
        · simpa [bCol, mi, mj, hi] using Bfree_lt (w := w) (i := i) (a := t)
            (fun x hx hH => afterHigh mj hH (Fin.lt_trans hx hij))
      | none =>
        by_cases hi : High w i <;> by_cases hj : High w j
        · simpa [bCol, mi, mj, hi, hj] using (mark_lt _ _).mpr (record hj hij)
        · simpa [bCol, mi, mj, hi, hj] using mark_lt_Bfree hij hi
        · simpa [bCol, mi, mj, hi, hj] using Bfree_lt (w := w) (i := i) (a := w j)
            (fun z hz _ => record hj (Fin.lt_trans hz hij))
        · simpa [bCol, mi, mj, hi, hj] using Bfree_inc w hij
  · intro i j hij
    by_cases hi : High w i <;> by_cases hj : High w j
    · simpa [tCol, hi, hj] using Tfree_inc w hij
    · simpa [tCol, hi, hj] using coldT i j hi (Fin.le_of_lt hij)
    · simpa [tCol, hi, hj] using mark_lt_Tfree hij hi
    · simpa [tCol, hi, hj] using (mark_lt _ _).mpr (lowInc hi hj hij)
  · intro i hi
    cases mi : m i with
    | none => simp [bCol, mi, hi]
    | some t => exact False.elim (sourceLow mi hi)
  · intro i hi; simp [tCol, hi]
  · intro i j
    cases mi : m i with
    | some t =>
      by_cases hj : High w j
      · have hne : t ≠ w j := fun e => targetLow mi e.symm hj
        simp [bCol, tCol, mi, hj, hne, Ne.symm (Tfree_ne_mark w j t)]
      · simp only [bCol, tCol, mi, hj, ite_false, Option.some.injEq]
        exact ⟨mark_inj, congrArg mark⟩
    | none =>
      by_cases hi : High w i <;> by_cases hj : High w j
      · simp [bCol, tCol, mi, hi, hj, Ne.symm (Tfree_ne_mark w j (w i))]
      · have hne : mark (w i) ≠ mark (w j) := by
          intro e; exact hj (inj (mark_inj e) ▸ hi)
        simp [bCol, tCol, mi, hi, hj, hne]
      · simp [bCol, tCol, mi, hi, hj, free_ne]
      · simp [bCol, tCol, mi, hi, hj, Bfree_ne_mark]
  · intro p i hp hpi
    simpa [tCol, hp] using coldT p i hp hpi
  · intro p i hp mp hb
    simpa [bCol, mp, hp] using Bfree_lt hb

end StarFiring.Padding
