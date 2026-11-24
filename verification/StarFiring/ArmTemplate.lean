import StarFiring.CertData

/-! Data at one row before any relabeling or rescheduling. `early` and `outEarly`
record the actual placement of the first outward transfer and depth-two comparison. -/
namespace StarFiring
structure ArmTemplate (k : Nat) where
  A : Chip k
  B : Chip k
  T : Chip k
  D : Chip k
  E : Chip k
  F : Chip k
  r1 : Chip k
  u1 : Chip k
  r2 : Chip k
  u2 : Chip k
  q : Chip k
  o : Chip k
  r3 : Chip k
  m : Chip k
  early : Bool
  outEarly : Bool

namespace ArmTemplate
variable (p : ArmTemplate k)
def L := min p.A p.B
def H := max p.A p.B

def small (c : Mode) := match c with
  | .e | .r => p.L | .l => min p.L p.T | .h => min p.H p.T
def large (c : Mode) := match c with
  | .e | .r => p.H | .l => max p.L p.T | .h => max p.H p.T
def rest (c : Mode) := match c with
  | .e | .r => p.T | .l => p.H | .h => p.L

/-- Local transfer identities. The `.r`/`.e` distinction comes from the center:
we return a preliminary classification with `.e` for both, recording `early` separately. -/
structure Reads (c : Mode) : Prop where
  pre : p.early = true → c = .e ∨ c = .r
  firstSmall : p.r1 = p.small c
  firstLarge : p.u1 = p.large c
  secondSmall : p.r2 = min (p.rest c) p.D
  secondLarge : p.u2 = max (p.rest c) p.D
  inward : p.q = min p.u1 p.u2
  outward : p.o = max p.u1 p.u2
  lastSmall : p.r3 = min p.E p.q
  lastLarge : p.m = max p.E p.q

theorem reads_e_iff_r : p.Reads .e ↔ p.Reads .r := by
  constructor <;> intro h <;> cases h <;> constructor <;> first | assumption | simp
end ArmTemplate
end StarFiring
