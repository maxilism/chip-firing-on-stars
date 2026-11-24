import StarFiring.Cert
import StarFiring.Witness

/-! Static fourteen-arm witness for the same middle labels as the raw 62-move
trace. No property of that trace is used here; only its target labels/ranks. -/
namespace StarFiring.Witness

private def col (v : Vector Nat 14) : Batch 14 := fun i => Fin.ofNat 42 (v[i] - 1)

open Mode in
def cert14 : Cert 14 where
  mode := fun i => (#v[e,h,h,h,h,e,h,e,e,h,r,h,r,r] : Vector Mode 14)[i]
  L := col #v[1,2,3,4,5,6,7,8,9,28,29,30,31,32]
  H := col #v[20,21,22,23,24,25,26,27,37,38,39,40,41,42]
  X := col #v[13,14,15,16,17,18,19,33,34,35,10,36,11,12]
  T := col #v[13,14,15,16,17,18,19,29,31,32,33,34,35,36]
  D := col #v[1,6,8,9,10,11,12,14,15,16,17,19,32,34]
  E := col #v[1,2,3,4,5,7,11,14,15,16,17,19,32,34]
  F := col #v[1,2,3,4,5,7,11,14,15,16,17,19,32,34]

-- Permutation is checked by extensional equality of all 42 label counts.
private theorem permCheck {xs ys : List (Chip 14)} (h : ∀ x, xs.count x = ys.count x) : xs.Perm ys :=
  List.perm_iff_count.mpr h

set_option maxRecDepth 10000 in
theorem validCert14 : cert14.Valid := by
  constructor <;> first | apply permCheck; decide +kernel | decide +kernel

theorem cert14_middle : cert14.middle = middle14 := by
  funext i; exact (by decide +kernel : ∀ j, cert14.middle j = middle14 j) i

theorem cert14_realizable : Realizable perm14 := by
  apply Cert.realizable validCert14 (by decide)
  rw [cert14_middle]; decide +kernel

end StarFiring.Witness
