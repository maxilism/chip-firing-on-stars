import StarFiring.Core

/-! Restricting a (possibly arbitrarily interleaved) raw run to one arm preserves
legality and the entire label ledger on that arm. A center firing is a delivery;
a firing on another arm is a stutter. No stabilization hypothesis is used. -/
namespace StarFiring

abbrev ArmConfig (k : Nat) := Nat → Chip k → Int

def armState (i : Row k) (s : Config k) : ArmConfig k := fun d => s (.arm i d)

inductive ArmEvent (k : Nat)
  | deliver (x : Chip k)
  | compare (d : Nat) (a b : Chip k)
  deriving Repr, DecidableEq

def Move.onArm (i : Row k) : Move k → Option (ArmEvent k)
  | .center b => some (.deliver (b i))
  | .arm j d a b => if i = j then some (.compare d a b) else none

def armTrace (i : Row k) (ms : List (Move k)) := ms.filterMap (Move.onArm i)

def ArmEvent.Legal (e : ArmEvent k) (s : ArmConfig k) : Prop := match e with
  | .deliver _ => True
  | .compare d a b => a < b ∧ 0 < s d a ∧ 0 < s d b

def ArmEvent.delta (e : ArmEvent k) (n : Nat) (x : Chip k) : Int := match e with
  | .deliver a => ind (n = 0) * ind (a = x)
  | .compare d a b => (ind (d = n+1) * ind (a = x) + ind (n = d+1) * ind (b = x)) -
      ind (n = d) * (ind (a = x) + ind (b = x))

def ArmEvent.act (e : ArmEvent k) (s : ArmConfig k) : ArmConfig k := fun n x => s n x + e.delta n x

inductive ArmRun {k : Nat} : ArmConfig k → List (ArmEvent k) → ArmConfig k → Prop
  | nil : ArmRun s [] s
  | cons : e.Legal s → ArmRun (e.act s) es t → ArmRun s (e :: es) t

@[simp] theorem armState_initial (i : Row k) : armState i (initial k) = fun _ _ => 0 := by
  funext n x; simp [armState, initial, ind]

private theorem eq_inward_iff (i j : Row k) (n d : Nat) :
    Site.arm i n = inward j d ↔ i = j ∧ d = n+1 := by
  cases d <;> simp [inward, eq_comm]

theorem armState_center (i : Row k) (s : Config k) (b : Batch k) :
    armState i ((Move.center b).act s) = (ArmEvent.deliver (b i)).act (armState i s) := by
  funext n x; cases n <;> simp [armState, Move.act, Move.delta, ArmEvent.act, ArmEvent.delta, ind]

theorem armState_compare (i : Row k) (s : Config k) (d : Nat) (a b : Chip k) :
    armState i ((Move.arm i d a b).act s) = (ArmEvent.compare d a b).act (armState i s) := by
  funext n x; simp [armState, Move.act, Move.delta, ArmEvent.act, ArmEvent.delta, eq_inward_iff]

theorem armState_stutter (i j : Row k) (hne : i ≠ j) (s : Config k) (d : Nat) (a b : Chip k) :
    armState i ((Move.arm j d a b).act s) = armState i s := by
  funext n x; simp [armState, Move.act, Move.delta, eq_inward_iff, hne, ind]

/-- Erasure of the other arms' moves is a simulation for every legal raw run. -/
theorem Run.armProject {s t : Config k} {ms : List (Move k)} (h : Run s ms t) (i : Row k) : ArmRun (armState i s) (armTrace i ms) (armState i t) := by
  induction h with
  | nil => exact ArmRun.nil
  | @cons ms t s m hl _ ih =>
    cases m with
    | center b =>
      simp only [armTrace, List.filterMap_cons, Move.onArm] at *
      rw [armState_center] at ih
      exact ArmRun.cons trivial ih
    | arm j d a b =>
      by_cases he : i = j
      · subst j
        simp only [armTrace, List.filterMap_cons, Move.onArm] at *
        rw [armState_compare] at ih
        exact ArmRun.cons hl ih
      · simpa only [armTrace, List.filterMap_cons, Move.onArm, ite_eq_right he, armState_stutter i j he] using ih

theorem armTrace_append (i : Row k) (ms ns : List (Move k)) :
    armTrace i (ms ++ ns) = armTrace i ms ++ armTrace i ns := List.filterMap_append ..

end StarFiring
