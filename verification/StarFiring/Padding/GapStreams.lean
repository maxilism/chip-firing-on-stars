import StarFiring.Padding.Streams
import StarFiring.Padding.Match
import StarFiring.Padding.Tracks

namespace StarFiring.Padding

/-- The explicit stream layout for the last-to-first gap construction on a
321-avoiding permutation. Only the data fields survive proof erasure. -/
def gapStreams {w : Row n → Row n} (hw : Function.Injective w) (ha : Avoids321 w) :
    StreamData w (matchValue w) := by
  let inc : ∀ i j, High w i → High w j → i < j → w i < w j :=
    fun _ _ hi hj hij => high_inc hw ha hi hj hij
  exact makeStreams w (matchValue w) hw (high_record hw ha) (low_inc hw ha)
    matchValue_source_low (fun ma e => matchValue_target_low inc ma e)
    (fun ma => matchValue_afterHigh inc ma) (fun ma => matchValue_beforeHigh inc ma)
    (fun ma mb => matchValue_inc inc ma mb) (fun ma mb => matchValue_suffix ma mb)

end StarFiring.Padding
