import Std

/-! The unreduced game. Labels and arms are zero-based; `.arm i 0` is level 1.
Configurations are incidence ledgers. Only positive entries can supply a firing;
from `initial` each physical label occurs at exactly one site (see `Physical`). -/
namespace StarFiring
abbrev Chip (k : Nat) := Fin (3*k)
abbrev Row (k : Nat) := Fin k
abbrev Batch (k : Nat) := Row k → Chip k
inductive Site (k : Nat)
  | center | arm (i : Row k) (d : Nat)
  deriving DecidableEq, Repr
abbrev Config (k : Nat) := Site k → Chip k → Int

def ind (p : Prop) [Decidable p] : Int := if p then 1 else 0

def inward (i : Row k) : Nat → Site k
  | 0 => .center
  | d+1 => .arm i d

def initial (k : Nat) : Config k := fun s _ => ind (s = .center)

def Increasing (b : Batch k) := ∀ i j, i < j → b i < b j
instance (b : Batch k) : Decidable (Increasing b) := inferInstanceAs (Decidable (∀ i j, i < j → b i < b j))

def Has (b : Batch k) (x : Chip k) := ∃ i, b i = x
instance (b : Batch k) (x : Chip k) : Decidable (Has b x) := inferInstanceAs (Decidable (∃ i, b i = x))

inductive Move (k : Nat)
  | center (b : Batch k)
  | arm (i : Row k) (d : Nat) (a b : Chip k)

def Move.Legal (m : Move k) (s : Config k) : Prop := match m with
  | .center b => Increasing b ∧ ∀ i, 0 < s .center (b i)
  | .arm i d a b => a < b ∧ 0 < s (.arm i d) a ∧ 0 < s (.arm i d) b
instance (m : Move k) (s : Config k) : Decidable (m.Legal s) := by cases m <;> unfold Move.Legal <;> infer_instance

def Move.delta (m : Move k) (t : Site k) (x : Chip k) : Int := match m with
  | .center b => match t with
    | .center => -ind (Has b x)
    | .arm i 0 => ind (b i = x)
    | .arm _ (_+1) => 0
  | .arm i d a b => (ind (t = inward i d) * ind (a = x) +
    ind (t = .arm i (d+1)) * ind (b = x)) -
    ind (t = .arm i d) * (ind (a = x) + ind (b = x))

def Move.act (m : Move k) (s : Config k) : Config k := fun t x => s t x + m.delta t x

inductive Run {k : Nat} : Config k → List (Move k) → Config k → Prop
  | nil : Run s [] s
  | cons : m.Legal s → Run (m.act s) ms t → Run s (m :: ms) t

def Reachable (s t : Config k) := ∃ ms, Run s ms t

def load (s : Config k) (p : Site k) : Int := ((List.finRange (3*k)).map (s p)).sum

def Stable (s : Config k) := load s .center < k ∧ ∀ i d, load s (.arm i d) ≤ 1

/-- `p` gives the relative ranks in arm order (in `Fin k`). -/
def MiddleOrder (s : Config k) (p : Row k → Row k) : Prop :=
  ∃ mid : Batch k, (∀ i, 0 < s (.arm i 1) (mid i)) ∧
    (∀ i j, mid i < mid j ↔ p i < p j)

def Realizable (p : Row k → Row k) := ∃ s, Reachable (initial k) s ∧ Stable s ∧ MiddleOrder s p

end StarFiring
