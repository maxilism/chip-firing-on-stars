import StarFiring.Core

/-! Static normal-form certificate. One spare label `X i` is assigned to each row;
those on `r` rows form W, and the others form U. Their internal ordering does not
matter. Sorted batches are specified by strict increase and permutation, not by
an assumed legal schedule. -/
namespace StarFiring

inductive Mode | e | r | l | h deriving Repr, DecidableEq

structure Cert (k : Nat) where
  mode : Row k → Mode
  L : Batch k
  H : Batch k
  X : Batch k
  T : Batch k
  D : Batch k
  E : Batch k
  F : Batch k

namespace Cert
variable (c : Cert k)

def feedT (i : Row k) := match c.mode i with
  | .r => c.L i | _ => c.X i

def feedD (i : Row k) := match c.mode i with
  | .e => c.L i | .r => c.X i
  | .l => min (c.L i) (c.T i) | .h => min (c.H i) (c.T i)

def y (i : Row k) := match c.mode i with
  | .e | .r => c.H i
  | .l => max (c.L i) (c.T i) | .h => max (c.H i) (c.T i)

def z (i : Row k) := match c.mode i with
  | .e | .r => c.T i | .l => c.H i | .h => c.L i

def feedE (i : Row k) := min (c.z i) (c.D i)
def V (i : Row k) := max (c.z i) (c.D i)
def Q (i : Row k) := min (c.y i) (c.V i)
def outer (i : Row k) := max (c.y i) (c.V i)
def feedF (i : Row k) := min (c.E i) (c.Q i)
def middle (i : Row k) := max (c.E i) (c.Q i)

/-- Equality as bags of labels; together with increase on `dst` this specifies
exactly sorting, including the assignment to ordered arms. -/
def Rebatch (src dst : Batch k) := ((List.finRange k).map src).Perm ((List.finRange k).map dst)

structure Valid : Prop where
  partition : (List.finRange (3*k)).Perm
    ((List.finRange k).flatMap fun i => [c.L i,c.H i,c.X i])
  incL : Increasing c.L
  incH : Increasing c.H
  incT : Increasing c.T
  incD : Increasing c.D
  incE : Increasing c.E
  incF : Increasing c.F
  lh : ∀ i, c.L i < c.H i
  sortT : Rebatch c.feedT c.T
  sortD : Rebatch c.feedD c.D
  sortE : Rebatch c.feedE c.E
  sortF : Rebatch c.feedF c.F

end Cert
end StarFiring
