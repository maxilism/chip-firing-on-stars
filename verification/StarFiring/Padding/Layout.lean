import StarFiring.Avoidance
import StarFiring.Replay

/-! Ordered slots before the optional identity tail. `replay` indexes the
*source* of a shared chip; its destination can be on another arm. -/
namespace StarFiring.Padding

/-- The direct sum `w ⊕ id_t`, on precisely `n+t` ordered rows. -/
def pad (w : Row n → Row n) (t : Nat) : Row (n+t) → Row (n+t) :=
  Fin.addCases (fun i => (w i).castAdd t) (Fin.natAdd n)

@[simp] theorem pad_left (w : Row n → Row n) (t) (i : Row n) : pad w t (i.castAdd t) = (w i).castAdd t := by simp [pad]
@[simp] theorem pad_right (w : Row n → Row n) (t) (h : Row t) : pad w t (Fin.natAdd n h) = Fin.natAdd n h := by simp [pad]

theorem avoids_of_pad {w : Row n → Row n} {t} (h : Avoids321 (pad w t)) : Avoids321 w := by
  intro i j k ij jk kj ji
  have := h (i.castAdd t) (j.castAdd t) (k.castAdd t) ij jk
  simp only [pad_left] at this
  exact this kj ji

/-- Target and ordinary return at each row before allocating a spare. -/
def keep (w : Row n → Row n) (B T : Row n → Nat) (i : Row n) := if i < w i then B i else T i
def give (w : Row n → Row n) (B T : Row n → Nat) (i : Row n) := if i < w i then T i else B i

structure Layout (w : Row n → Row n) where
  B : Row n → Nat
  T : Row n → Nat
  replay : Row n → Bool
  strictB : ∀ i j, i < j → B i < B j
  strictT : ∀ i j, i < j → T i < T j
  share : ∀ i, replay i = true ↔ ∃ j, B i = T j
  low : ∀ i, replay i = true → ¬ i < w i
  ranks : ∀ i j, keep w B T i < keep w B T j ↔ w i < w j

/-- How many original fourth-batch inputs are strictly below this target?
Every replay replaces one return by a spare below every target. -/
def Layout.cheap {w : Row n → Row n} (l : Layout w) (i : Row n) : Nat :=
  (rows n).countP fun j => l.replay j || decide (give w l.B l.T j < keep w l.B l.T i)

end StarFiring.Padding
