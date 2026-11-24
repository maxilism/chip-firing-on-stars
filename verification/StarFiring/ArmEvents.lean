import StarFiring.ArmTemplate
import StarFiring.Projection
namespace StarFiring
namespace ArmTemplate
variable (p : ArmTemplate k)
open ArmEvent

def startEvents : List (ArmEvent k) :=
  [.deliver p.A, .deliver p.B] ++
  (if p.early then [.compare 0 p.r1 p.u1, .deliver p.T]
   else [.deliver p.T, .compare 0 p.r1 p.u1])

def endEvents : List (ArmEvent k) :=
  [.deliver p.D, .compare 0 p.r2 p.u2] ++
  (if p.outEarly then [.compare 1 p.q p.o, .deliver p.E]
   else [.deliver p.E, .compare 1 p.q p.o]) ++
  [.compare 0 p.r3 p.m, .deliver p.F]

def events : List (ArmEvent k) := p.startEvents ++ p.endEvents
end ArmTemplate
end StarFiring
