import StarFiring.CertData
import StarFiring.Endpoint

/-! Soundness of all four-mode certificates. Stages operate on lists of actual
(site, label) pairs. A staged transfer is proved by replay on the unreduced
`Run`, not by a parallel firing rule. Permutations merely reorder the private
representation of the *same* board. Carrying conservation through the stages
lets us derive strictness of every local comparison from the initial partition. -/
namespace StarFiring
namespace CertReplay

abbrev labels (s : List (Token k)) := s.map Prod.snd
structure Transfer (s t : List (Token k)) : Prop where
  conserve : (labels s).Perm (labels t)
  run : (labels s).Nodup → Reachable (board s) (board t)

namespace Transfer

theorem shuffle {s t : List (Token k)} (h : s.Perm t) : Transfer s t :=
  ⟨h.map _, fun _ => by rw [board_perm h]; apply Reachable.refl⟩

theorem refl (s : List (Token k)) : Transfer s s := shuffle (.refl _)

theorem trans {s t u : List (Token k)} (h : Transfer s t) (g : Transfer t u) : Transfer s u :=
  ⟨h.conserve.trans g.conserve, fun nd => (h.run nd).trans (g.run (h.conserve.nodup nd))⟩

theorem frame {s t : List (Token k)} (h : Transfer s t) (ctx : List (Token k)) :
    Transfer (s ++ ctx) (t ++ ctx) := by
  constructor
  · simpa only [labels, List.map_append] using h.conserve.append_right (labels ctx)
  · intro nd
    have hn := List.nodup_append.mp (List.map_append ▸ nd : (labels s ++ labels ctx).Nodup)
    exact (h.run hn.1).frame ctx

theorem beside {a b c d : List (Token k)} (h : Transfer a b) (g : Transfer c d) :
    Transfer (a++c) (b++d) := (h.frame c).trans <| (shuffle List.perm_append_comm).trans <|
    (g.frame b).trans (shuffle List.perm_append_comm)

theorem rowswise (rs : List (Row k)) {f g : Row k → List (Token k)}
    (h : ∀ i, Transfer (f i) (g i)) : Transfer (rs.flatMap f) (rs.flatMap g) := by
  induction rs with
  | nil => exact refl _
  | cons i _ ih => exact (h i).beside ih

theorem center {b : Batch k} (h : Increasing b) : Transfer (centerTokens b) (deliveryTokens b) := by
  constructor
  · simp [labels, centerTokens, deliveryTokens,List.map_map, Function.comp_def]
  · intro _; simpa using fireCenter h []

theorem minL {a b : Chip k} (h : a ≤ b) : min a b = a := Fin.ext (Nat.min_eq_left h)
theorem maxR {a b : Chip k} (h : a ≤ b) : max a b = b := Fin.ext (Nat.max_eq_right h)
theorem minR {a b : Chip k} (h : b ≤ a) : min a b = b := Fin.ext (Nat.min_eq_right h)
theorem maxL {a b : Chip k} (h : b ≤ a) : max a b = a := Fin.ext (Nat.max_eq_left h)

theorem arm (i : Row k) (d : Nat) (a b : Chip k) :
    Transfer [(.arm i d,a),(.arm i d,b)] [(inward i d,min a b),(.arm i (d+1),max a b)] := by
  by_cases h : a ≤ b
  · rw [minL h, maxR h]
    refine ⟨.refl _,fun hn => ?_⟩
    have ne : a ≠ b := by simpa [labels] using hn
    have hv : a.val ≠ b.val := fun e => ne (Fin.ext e)
    exact fireArm (show a < b from Nat.lt_of_le_of_ne h hv) []
  · have lt : b < a := Fin.not_le.mp h
    rw [minR (Fin.le_of_lt lt), maxL (Fin.le_of_lt lt)]
    refine (shuffle (.swap _ _ [])).trans ⟨.refl _,fun _ => fireArm lt []⟩

end Transfer

/-- Pull one token from each row, exposing exactly a center batch. -/
theorem collect {α β : Type} (rs : List α) (f : α → β) (g : α → List β) :
    (rs.flatMap fun i => f i :: g i).Perm (rs.map f ++ rs.flatMap g) := by
  induction rs with
  | nil => exact .refl _
  | cons i _ ih =>
    simp only [List.flatMap_cons,List.map_cons,List.cons_append]
    exact ((ih.append_left _).trans (List.perm_append_comm_assoc _ _ _)).cons _

abbrev C (a : Chip k) : Token k := (.center,a)
abbrev A (i : Row k) (d : Nat) (a : Chip k) : Token k := (.arm i d,a)
abbrev rowBoard (f : Row k → List (Token k)) := (rows k).flatMap f

/-- Rebatch by label permutation, using just a single legal center firing. -/
theorem deliver {src dst : Batch k} (p : Cert.Rebatch src dst) (h : Increasing dst)
    (g : Row k → List (Token k)) :
    Transfer (rowBoard fun i => C (src i) :: g i) (rowBoard fun i => A i 0 (dst i) :: g i) := by
  refine (Transfer.shuffle (collect _ _ _)).trans ?_
  have hp : ((rows k).map fun i => C (src i)).Perm (centerTokens dst) := by
    simpa only [List.map_map,Function.comp_def,centerTokens,rows,C] using p.map C
  exact ((Transfer.shuffle hp).frame _).trans <|
    ((Transfer.center h).frame _).trans (Transfer.shuffle (collect _ _ _).symm)

/-- A local comparison in any ordering of its two inputs and its frame. -/
theorem hit (i : Row k) (d : Nat) (a b : Chip k) (rest : List (Token k))
    {s t : List (Token k)} (hs : s.Perm (A i d a :: A i d b :: rest))
    (ht : ((inward i d, min a b) :: A i (d+1) (max a b) :: rest).Perm t) : Transfer s t :=
  (Transfer.shuffle hs).trans (((Transfer.arm i d a b).frame rest).trans (Transfer.shuffle ht))

end CertReplay
namespace Cert
open CertReplay

-- Small permutations of explicit token lists, proved without any inequalities
-- or distinctness assumptions: counts agree by commutativity of addition.
local macro "rebag" : tactic => `(tactic|
  first | exact List.Perm.refl _ | (apply List.perm_iff_count.mpr; intro x; simp only [List.count_cons,List.count_nil,C,A,inward,Nat.reduceAdd,Cert.V,Cert.Q,Cert.outer,Cert.feedE,Cert.feedF,Cert.middle]; omega))

private def restT (c : Cert k) (i : Row k) : List (Token k) := match c.mode i with
  | .e => [C (c.L i), A i 1 (c.H i)]
  | .r => [C (c.X i), A i 1 (c.H i)]
  | .l | .h => [A i 0 (c.L i), A i 0 (c.H i)]

/-- Carry out exactly the early comparisons. `r` reuses the return `L` in T,
whereas `e` uses the reserved `X` in T and retains `L` for D. -/
private theorem early {c : Cert k} (v : c.Valid) (i : Row k) :
    Transfer [A i 0 (c.H i), A i 0 (c.L i), C (c.X i)] (C (c.feedT i) :: c.restT i) := by
  have h := Fin.le_of_lt (v.lh i)
  cases hm : c.mode i <;> simp only [feedT, restT, hm]
  case e =>
    apply hit i 0 (c.L i) (c.H i) [C (c.X i)]
    · rebag
    · rw [Transfer.minL h,Transfer.maxR h]; rebag
  case r =>
    apply hit i 0 (c.L i) (c.H i) [C (c.X i)]
    · rebag
    · rw [Transfer.minL h,Transfer.maxR h]; rebag
  case l => apply Transfer.shuffle; rebag
  case h => apply Transfer.shuffle; rebag

/-- Carry out the late comparisons, leaving a D input, one chip at level 1,
and one at level 2 on every row. -/
private theorem late (c : Cert k) (i : Row k) :
    Transfer (A i 0 (c.T i) :: c.restT i) [C (c.feedD i), A i 0 (c.z i), A i 1 (c.y i)] := by
  cases hm : c.mode i <;> simp only [restT, feedD, z, y, hm]
  case e => apply Transfer.shuffle; rebag
  case r => apply Transfer.shuffle; rebag
  case l => apply hit i 0 (c.L i) (c.T i) [A i 0 (c.H i)] <;> rebag
  case h => apply hit i 0 (c.H i) (c.T i) [A i 0 (c.L i)] <;> rebag

/-- The complete six-round comparator network evaluated on *chips*, not ranks.
Only strict batch and partition/sort conditions enter; no firing constraints
on unobserved intermediate configurations are premises. -/
theorem staged {c : Cert k} (v : c.Valid) :
    Transfer (rowBoard fun i => [C (c.L i),C (c.H i),C (c.X i)])
      (rowBoard fun i => [A i 0 (c.F i), A i 1 (c.middle i), A i 2 (c.outer i)]) := by
  apply (deliver (.refl _) v.incL (fun i => [C (c.H i), C (c.X i)])).trans
  have switchH (i : Row k) : Transfer [A i 0 (c.L i),C (c.H i),C (c.X i)]
      [C (c.H i),A i 0 (c.L i),C (c.X i)] := Transfer.shuffle (.swap _ _ _)
  apply (Transfer.rowswise _ switchH).trans
  apply (deliver (.refl _) v.incH (fun i => [A i 0 (c.L i), C (c.X i)])).trans
  apply (Transfer.rowswise _ (early v)).trans
  apply (deliver v.sortT v.incT c.restT).trans
  apply (Transfer.rowswise _ c.late).trans
  apply (deliver v.sortD v.incD (fun i => [A i 0 (c.z i), A i 1 (c.y i)])).trans
  have second (i : Row k) : Transfer [A i 0 (c.D i), A i 0 (c.z i), A i 1 (c.y i)]
      [C (c.feedE i), A i 1 (c.y i), A i 1 (c.V i)] := by
    apply hit i 0 (c.z i) (c.D i) [A i 1 (c.y i)] <;> rebag
  apply (Transfer.rowswise _ second).trans
  have deep (i : Row k) : Transfer [C (c.feedE i), A i 1 (c.y i), A i 1 (c.V i)]
      [C (c.feedE i), A i 0 (c.Q i), A i 2 (c.outer i)] := by
    apply hit i 1 (c.y i) (c.V i) [C (c.feedE i)] <;> rebag
  apply (Transfer.rowswise _ deep).trans
  apply (deliver v.sortE v.incE (fun i => [A i 0 (c.Q i), A i 2 (c.outer i)])).trans
  have third (i : Row k) : Transfer [A i 0 (c.E i), A i 0 (c.Q i), A i 2 (c.outer i)]
      [C (c.feedF i), A i 1 (c.middle i), A i 2 (c.outer i)] := by
    apply hit i 0 (c.E i) (c.Q i) [A i 2 (c.outer i)] <;> rebag
  apply (Transfer.rowswise _ third).trans
  exact deliver v.sortF v.incF (fun i => [A i 1 (c.middle i), A i 2 (c.outer i)])

/-- Soundness: the certificate's exact three labelled columns occur after a
sequence of elementary legal firings starting with all `3*k` chips at center. -/
theorem sound {c : Cert k} (v : c.Valid) :
    Reachable (initial k) (endpoint c.F c.middle c.outer) := by
  let s := rowBoard fun i => [C (c.L i), C (c.H i), C (c.X i)]
  have hp : ((List.finRange (3*k)).map C).Perm s := by
    simpa only [s, rowBoard, rows, List.map_flatMap, List.map_cons, List.map_nil] using v.partition.map C
  have hs : board s = initial k := (board_perm hp).symm.trans board_initial
  have nd : (labels s).Nodup := (hp.map Prod.snd).nodup (by
    simpa [labels,List.map_map,C,Function.comp_def] using List.nodup_finRange (3*k))
  rw [← hs]; exact (staged v).run nd

/-- Project the exact reachable endpoint to its relative middle ranks. -/
theorem realizable {c : Cert k} (v : c.Valid) (hk : 0 < k) {p : Row k → Row k}
    (hp : ∀ i j, c.middle i < c.middle j ↔ p i < p j) : Realizable p :=
  ⟨_, sound v, endpoint_stable hk .., (endpoint_middle_iff ..).2 hp⟩

end Cert
end StarFiring
