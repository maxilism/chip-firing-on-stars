import StarFiring.CertData

/-! # Two increasing streams for the middle chips

Group the first four arrivals as `(L,H)` and `(T,D)`. Discard the smaller of
the pair minima and the larger of the pair maxima. What remain are
`max L (min T D)` and `min H (max T D)`: the two middle occurrences, not
necessarily in that order. Every pairing mode yields one of these two values
for `Q`, even when a returned label reappears among the four arrivals. -/
namespace StarFiring

/-- No three increasing positions carry strictly decreasing values. -/
def Avoids321 {n : Nat} (f : Row k → Fin n) : Prop :=
  ∀ i j h, i < j → j < h → f h < f j → ¬ f j < f i

private theorem inc_max {f g : Batch k} (hf : Increasing f) (hg : Increasing g) :
    Increasing (fun i => max (f i) (g i)) := by
  intro i j hij
  have := hf i j hij
  have := hg i j hij
  simp only [Fin.lt_def, Fin.val_max] at *
  omega

private theorem inc_min {f g : Batch k} (hf : Increasing f) (hg : Increasing g) :
    Increasing (fun i => min (f i) (g i)) := by
  intro i j hij
  have := hf i j hij
  have := hg i j hij
  simp only [Fin.lt_def, Fin.val_min] at *
  omega

namespace Cert

private def maxOfMins (c : Cert k) (i : Row k) := max (c.L i) (min (c.T i) (c.D i))
private def minOfMaxes (c : Cert k) (i : Row k) := min (c.H i) (max (c.T i) (c.D i))

private theorem min_swap (a b : Fin n) : min a b = min b a := Fin.ext (Nat.min_comm ..)
private theorem max_swap (a b : Fin n) : max a b = max b a := Fin.ext (Nat.max_comm ..)

private theorem cross_choice (a b x y : Fin n) (h : a < b) :
    min (max a x) (max b y) = max a (min x y) ∨
    min (max a x) (max b y) = min b (max x y) := by
  simp only [Fin.ext_iff, Fin.lt_def, Fin.val_min, Fin.val_max] at *
  omega

/-- The middle occurrence selected by `Q` on this row can depend on the mode,
but the two candidate *streams* do not. -/
private theorem q_choice {c : Cert k} (hc : c.Valid) (i : Row k) :
    c.Q i = maxOfMins c i ∨ c.Q i = minOfMaxes c i := by
  cases h : c.mode i with
  | e | r => right; simp [Q, V, y, z, minOfMaxes, h]
  | l => simpa only [Q, V, y, z, maxOfMins, minOfMaxes, h] using
      cross_choice (c.L i) (c.H i) (c.T i) (c.D i) (hc.lh i)
  | h =>
    simpa only [Q, V, y, z, maxOfMins, minOfMaxes, h, min_swap (max (c.H i) (c.T i)),
      min_swap (c.T i), max_swap (c.T i)] using
      cross_choice (c.L i) (c.H i) (c.D i) (c.T i) (hc.lh i)

theorem Valid.two_tracks {c : Cert k} (hc : c.Valid) :
    ∃ f g : Batch k, Increasing f ∧ Increasing g ∧
      ∀ i, c.middle i = f i ∨ c.middle i = g i := by
  refine ⟨(fun i => max (c.E i) (maxOfMins c i)),
    (fun i => max (c.E i) (minOfMaxes c i)),
    inc_max hc.incE (inc_max hc.incL (inc_min hc.incT hc.incD)),
    inc_max hc.incE (inc_min hc.incH (inc_max hc.incT hc.incD)), ?_⟩
  intro i
  exact (q_choice hc i).imp (congrArg (max (c.E i))) (congrArg (max (c.E i)))

/-- In a decreasing triple two positions would have to use the same track. -/
theorem Valid.middle_avoids321 {c : Cert k} (hc : c.Valid) : Avoids321 c.middle := by
  obtain ⟨f, g, hf, hg, hfg⟩ := hc.two_tracks
  intro i j h hij hjh hhj hji
  have hih := Fin.lt_trans hij hjh
  have bad (u : Batch k) (hu : Increasing u) :
      ¬ (c.middle i = u i ∧ c.middle j = u j) ∧
      ¬ (c.middle j = u j ∧ c.middle h = u h) ∧
      ¬ (c.middle i = u i ∧ c.middle h = u h) := by
    have := hu i j hij
    have := hu j h hjh
    have := hu i h hih
    simp only [Fin.lt_def, Fin.ext_iff] at *
    omega
  obtain ⟨bf₁, bf₂, bf₃⟩ := bad f hf
  obtain ⟨bg₁, bg₂, bg₃⟩ := bad g hg
  rcases hfg i with hi | hi <;> rcases hfg j with hj | hj <;> rcases hfg h with he | he <;>
    first | exact bf₁ ⟨hi,hj⟩ | exact bf₂ ⟨hj,he⟩ | exact bf₃ ⟨hi,he⟩
          | exact bg₁ ⟨hi,hj⟩ | exact bg₂ ⟨hj,he⟩ | exact bg₃ ⟨hi,he⟩

/-- Transfer to any choice of relative ranks that reflects the label order. -/
theorem Valid.ranks_avoid321 {c : Cert k} (hc : c.Valid) {p : Row k → Row k}
    (h : ∀ i j, c.middle i < c.middle j ↔ p i < p j) : Avoids321 p :=
  fun i j l hij hjl hlj hji =>
    hc.middle_avoids321 i j l hij hjl ((h _ _).mpr hlj) ((h _ _).mpr hji)

end Cert
end StarFiring
