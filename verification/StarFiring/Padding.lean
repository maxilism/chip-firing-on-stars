import StarFiring.Classification
import StarFiring.Padding.Shortfall
import StarFiring.Padding.GapStreams
import StarFiring.Padding.StreamLayout
import StarFiring.Padding.Pin
import StarFiring.Padding.Extend

namespace StarFiring.Padding

/-- A sufficient test on any pair of completed streams: the cap uses *all*
spares at a label threshold, including returns on later source rows. -/
theorem Layout.certificate {w : Row n → Row n} (l : Layout w) (hn : 0 < n)
    (t : Nat) (room : ∀ i, i.val < l.cheap i + t) :
    Pin.Witness (pad w t) (fun i => decide (i < pad w t i)) (l.extend t).replay := by
  let a := l.extend t
  let p := pad w t
  let high := fun i => decide (i < p i)
  have target (i) : Pin.target high a.B a.T i = keep p a.B a.T i := by simp [Pin.target,keep,high]
  have other (i) : Pin.other high a.B a.T i = give p a.B a.T i := by simp [Pin.other,give,high]
  apply Pin.certificate (by omega) p a.B a.T high a.replay a.strictB a.strictT
    (fun i => (l.shifted t i).1) (fun i => (l.shifted t i).2) (fun i => (a.share i).symm)
  · intro i hi; exact decide_eq_false (a.low i hi)
  · intro i; simp only [other,target]; change i.val < a.cheap i; exact l.extend_room t room i
  · simpa only [target] using a.ranks

/-- At zero padding the target is literally the original permutation. -/
@[simp] theorem pad_zero (w : Row n → Row n) : pad w 0 = w := by
  funext i; exact pad_left w 0 i

/-- Original replays come from the last matched positions in the paper's gaps.
Every appended row replays, supplying one more spare below all targets. -/
def replaySources (w : Row n → Row n) (t : Nat) : Row (n+t) → Bool :=
  Fin.addCases (fun i => (matchValue w i).isSome) (fun _ => true)

/-- A firing certificate for identity padding from excedance gaps. Its fourth,
fifth and sixth deliveries coincide and its retained pins are the middle chips. -/
theorem gap_certificate {w : Row n → Row n} (hn : 0 < n) (hw : Function.Injective w)
    (ha : Avoids321 w) {t : Nat} (ht : U w ≤ t) :
    Pin.Witness (pad w t) (fun i => decide (i < pad w t i)) (replaySources w t) := by
  let s := gapStreams hw ha
  let l := s.layout hw
  apply l.certificate hn t
  intro i
  let cheap := fun j => (matchValue w j).isSome || decide (give w s.B s.T j < keep w s.B s.T i)
  have h := shortfall hw ha ht i cheap (fun _ h₁ h₂ => s.affordable h₁ h₂)
    (fun j hj => by simp [cheap,hj])
  simpa only [Layout.cheap,StreamData.layout,l,Nat.add_comm] using h

/-- Identity padding is realizable for every integer `t≥U(w)`,
with all `3*(n+t)` physical chips at the center initially. -/
theorem realizable_pad_of_gap {w : Row n → Row n} (hn : 0 < n) (hw : Function.Injective w)
    (ha : Avoids321 w) {t : Nat} (ht : U w ≤ t) : Realizable (pad w t) :=
  (gap_certificate hn hw ha ht).realizable (by omega)

/-- The maximum-displacement bound needs no matched-gap arithmetic from the
caller: dropping all the nonnegative suffix credits can only increase the cost. -/
theorem realizable_pad_of_displacement {w : Row n → Row n} (hn : 0 < n)
    (hw : Function.Injective w) (ha : Avoids321 w) {t : Nat}
    (hd : ∀ i, (w i).val ≤ i.val + t) : Realizable (pad w t) :=
  realizable_pad_of_gap hn hw ha (U_le_iff.mpr (fun i _ => by have := hd i; omega))

/-- Allowing identity padding gives exactly the 321-avoiding permutations. -/
theorem avoids321_iff_exists_pad {w : Row n → Row n} (hn : 0 < n) (hw : Function.Injective w) :
    Avoids321 w ↔ ∃ t, Realizable (pad w t) :=
  ⟨fun ha => ⟨U w,realizable_pad_of_gap hn hw ha (Nat.le_refl _)⟩,
   fun ⟨_,hr⟩ => avoids_of_pad hr.avoids321⟩
end StarFiring.Padding
