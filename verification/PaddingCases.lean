import StarFiring

/-! Boundary checks for the deterministic padding theorem. Numbers inside the
vectors are zero-based; names and explanatory comments use paper notation. -/
namespace StarFiring.Padding.Cases

private def w21435 (i : Fin 5) := (#v[1,0,3,2,4] : Vector (Fin 5) 5)[i]
private def w2143 (i : Fin 4) := (#v[1,0,3,2] : Vector (Fin 4) 4)[i]
private def w312 (i : Fin 3) := (#v[2,0,1] : Vector (Fin 3) 3)[i]

-- No high rows, hence no terminal gap to process.
example (n) : U (id : Fin n → Fin n) = 0 := U_eq_zero_of_no_high (fun _ => Fin.lt_irrefl _)

-- Both a cross-row reuse and the last (sentinel) gap contribute at t = 0.
example : U w21435 = 0 := by decide +kernel
example : (List.finRange 5).map (fun i => (matchValue w21435 i).map Fin.val) =
    [none,some 2,none,none,some 4] := by decide +kernel
example : Realizable w21435 := by
  rw [← pad_zero w21435]
  apply realizable_pad_of_gap (by decide)
  · unfold Function.Injective; decide +kernel
  · unfold Avoids321; decide +kernel
  · decide +kernel

-- The maximum is over all suffixes, not just the first suffix.
example : U w2143 = 1 := by decide +kernel
-- An entire last position gap need not have any value-gap match.
example : U w312 = 2 := by decide +kernel
example : Realizable (pad w312 2) := by
  apply realizable_pad_of_gap (by decide)
  · unfold Function.Injective; decide +kernel
  · unfold Avoids321; decide +kernel
  · decide +kernel

-- The bound is sufficient, not necessary. The classification project's
-- 14-arm raw witness reaches this order already with no padding.
theorem sufficient_not_minimal : U StarFiring.Witness.perm14 = 1 ∧
    Realizable (pad StarFiring.Witness.perm14 0) :=
  ⟨by decide +kernel, by simpa using StarFiring.Witness.realizable14⟩

end StarFiring.Padding.Cases
