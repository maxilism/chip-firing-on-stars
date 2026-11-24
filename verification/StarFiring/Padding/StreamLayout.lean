import StarFiring.Padding.Streams
import StarFiring.Padding.Tracks
import StarFiring.Padding.Match
import StarFiring.Padding.Layout
namespace StarFiring.Padding

private theorem onto_of_inj {w : Row n → Row n} (hw : Function.Injective w) : Function.Surjective w := by
  intro i; have hi := (perm_of_injective hw).mem_iff.mpr (List.mem_finRange i)
  obtain ⟨j,_,hj⟩ := List.mem_map.mp hi; exact ⟨j,hj⟩

variable {w : Row n → Row n} (s : StreamData w (matchValue w))

private theorem keep_eq (i) : keep w s.B s.T i = s.Z i := by
  unfold keep; split
  next h => exact s.pinB _ h
  next h => exact s.pinT _ h

/-- No overlap is implicit in this packing: `cross` gives the destination
rank, and surjectivity supplies an actual destination row of that rank. -/
def StreamData.layout (hw : Function.Injective w) : Layout w where
  B := s.B
  T := s.T
  strictB := s.incB
  strictT := s.incT
  replay := fun i => (matchValue w i).isSome
  low := fun _ h => matchValue_isSome_low h
  ranks := by intro i j; rw [keep_eq s,keep_eq s]; exact s.orderZ i j
  share := by
    intro i; constructor
    · intro hm; cases e : matchValue w i with
      | none => simp [e] at hm
      | some v => obtain ⟨j,hj⟩ := onto_of_inj hw v; exact ⟨j,(s.cross ..).mpr (hj ▸ e)⟩
    · rintro ⟨j,hj⟩; simp [(s.cross _ _).mp hj]

/-- Replays always contribute a small spare. An ordinary return costs less
than the target when its most recent opposite-track anchor is smaller. -/
theorem StreamData.affordable {p i : Row n} (hpi : p ≤ i)
    (h : High w p ∨ ∀ e, e < p → High w e → w e < w i) :
    ((matchValue w p).isSome || decide (give w s.B s.T p < keep w s.B s.T i)) = true := by
  rw [keep_eq s]; cases hmatch : matchValue w p with
  | some v => rfl
  | none =>
    simp only [Option.isSome_none,Bool.false_or,decide_eq_true_eq]
    unfold give; split
    next hh => exact s.coldT _ _ hh hpi
    next hh => exact s.coldB _ _ hh hmatch (h.resolve_left hh)

end StarFiring.Padding
