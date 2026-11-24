import StarFiring.Core

/-! Relating the incidence ledgers to individual chips and enabled firings. -/
namespace StarFiring

/-- For each label its column is exactly the incidence function of one site. -/
def Physical (s : Config k) := ∀ x, ∃ p : Site k, ∀ q, s q x = ind (q = p)

theorem initial_physical (k : Nat) : Physical (initial k) :=
  fun _ => ⟨.center, fun _ => rfl⟩

private theorem Increasing.inj {b : Batch k} (hb : Increasing b) {i j} (h : b i = b j) : i = j := by
  apply Fin.ext
  by_cases hlt : i < j
  · exact False.elim ((Fin.ne_of_lt (hb _ _ hlt)) h)
  by_cases hgt : j < i
  · exact False.elim ((Fin.ne_of_lt (hb _ _ hgt)) h.symm)
  simp [Fin.lt_def] at hlt hgt
  omega

private theorem eq_site_of_pos {s : Config k} {q p : Site k} {x : Chip k}
    (hp : ∀ t, s t x = ind (t = p)) (hq : 0 < s q x) : q = p := by
  by_cases h : q = p
  · exact h
  simp [hp, ind, h] at hq

/-- A legal move changes just the site of each selected label. -/
theorem Move.physical_act {s : Config k} {m : Move k} (hm : m.Legal s) (hs : Physical s) :
    Physical (m.act s) := by
  intro x
  obtain ⟨p, hp⟩ := hs x
  cases m with
  | center b =>
    obtain ⟨hb, hpos⟩ := hm
    by_cases hx : Has b x
    · obtain ⟨i, hi⟩ := hx
      subst x
      have hc := eq_site_of_pos hp (hpos i)
      subst p
      have mem : Has b (b i) := ⟨i, rfl⟩
      refine ⟨.arm i 0, ?_⟩
      intro t
      cases t with
      | center => simp [Move.act, Move.delta, hp, ind, mem]
      | arm j d =>
        cases d with
        | succ e => simp [Move.act, Move.delta, hp, ind]
        | zero =>
          have hij : b j = b i ↔ j = i := ⟨hb.inj, fun h => congrArg b h⟩
          simp [Move.act, Move.delta, hp, ind, hij]
    · refine ⟨p, ?_⟩
      have hbi (i : Row k) : b i ≠ x := fun h => hx ⟨i, h⟩
      intro t
      cases t with
      | center => simp [Move.act, Move.delta, hp, ind, hx]
      | arm j d => cases d <;> simp [Move.act, Move.delta, hp, ind, hbi]
  | arm i d a b =>
    obtain ⟨hab, hpa, hpb⟩ := hm
    have hne := Fin.ne_of_lt hab
    by_cases ha : a = x
    · subst x
      have hc := eq_site_of_pos hp hpa
      subst p
      refine ⟨inward i d, ?_⟩
      intro t
      simp [Move.act, Move.delta, hp, ind, Ne.symm hne] <;> omega
    · by_cases hb : b = x
      · subst x
        have hc := eq_site_of_pos hp hpb
        subst p
        refine ⟨.arm i (d+1), ?_⟩
        intro t
        simp [Move.act, Move.delta, hp, ind, ha] <;> omega
      · exact ⟨p, fun t => by simp [Move.act, Move.delta, ind, hp, ha, hb]⟩

theorem Run.physical {s t : Config k} {ms : List (Move k)} (r : Run s ms t)
    (hs : Physical s) : Physical t := by
  induction r with
  | nil => exact hs
  | cons hm _ ih => exact ih (Move.physical_act hm hs)

theorem reachable_physical {s : Config k} (h : Reachable (initial k) s) : Physical s := by
  obtain ⟨_, r⟩ := h
  exact r.physical (initial_physical k)

theorem Physical.zero_or_one {s : Config k} (h : Physical s) (p : Site k) (x : Chip k) :
    s p x = 0 ∨ s p x = 1 := by
  obtain ⟨q, hq⟩ := h x
  simp only [hq, ind]
  split <;> simp

/-- Explicit per-label uniqueness, without making a global choice of locations. -/
theorem Physical.unique_site {s : Config k} (h : Physical s) (x : Chip k) :
    ∃ p, s p x = 1 ∧ ∀ q, 0 < s q x → q = p := by
  obtain ⟨p, hp⟩ := h x
  exact ⟨p, by simp [hp, ind], fun _ => eq_site_of_pos hp⟩

theorem reachable_nonneg {k : Nat} {s : Config k} (h : Reachable (initial k) s) (p : Site k)
    (x : Chip k) : 0 ≤ s p x := by
  have := (reachable_physical h).zero_or_one p x
  omega

/-- Sorted list of the labels actually present at a site. -/
def occupants (s : Config k) (p : Site k) : List (Chip k) :=
  (List.finRange (3*k)).filter (fun x => decide (0 < s p x))

@[simp] theorem mem_occupants {s : Config k} {p : Site k} {x : Chip k} :
    x ∈ occupants s p ↔ 0 < s p x := by
  simp [occupants, List.mem_finRange]

private theorem occupants_increasing (s : Config k) (p : Site k) :
    (occupants s p).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange _).filter _

theorem Physical.load_eq_length {s : Config k} (hs : Physical s) (p : Site k) :
    load s p = ((occupants s p).length : Int) := by
  let f := fun (l : List (Chip k)) => l.filter (fun x => decide (0 < s p x))
  have count (l : List (Chip k)) : (l.map (s p)).sum = ((f l).length : Int) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rcases hs.zero_or_one p a with ha | ha <;>
        simp [f, ha] at * <;> omega
  exact count _

/-- The center admission rule is precisely the threshold on the occupancy list.
In the reverse direction take its first `k` entries, already in the required order. -/
theorem exists_center_legal_iff {s : Config k} :
    (∃ b, (Move.center b).Legal s) ↔ k ≤ (occupants s .center).length := by
  constructor
  · rintro ⟨b, inc, pos⟩
    have nd : ((List.finRange k).map b).Nodup := by
      apply List.pairwise_map.mpr
      exact (List.pairwise_lt_finRange k).imp (fun h => Fin.ne_of_lt (inc _ _ h))
    have hsub : (List.finRange k).map b ⊆ occupants s .center := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact mem_occupants.mpr (pos i)
    simpa using nd.length_le_of_subset hsub
  · intro h
    let l := occupants s .center
    let b : Batch k := fun i => l[i.val]'(Nat.lt_of_lt_of_le i.isLt h)
    refine ⟨b, ?_, ?_⟩
    · intro i j hij
      exact List.pairwise_iff_getElem.mp (occupants_increasing s .center) i.val j.val _ _ hij
    · intro i
      exact mem_occupants.mp (List.getElem_mem (l := l) (Nat.lt_of_lt_of_le i.isLt h))

/-- Two distinct chips suffice and are necessary for an arm firing. -/
theorem exists_arm_legal_iff {s : Config k} (i : Row k) (d : Nat) :
    (∃ a b, (Move.arm i d a b).Legal s) ↔ 2 ≤ (occupants s (.arm i d)).length := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have nd : [a,b].Nodup := by simp [Fin.ne_of_lt hab]
    have hsub : [a,b] ⊆ occupants s (.arm i d) := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact mem_occupants.mpr ha
      · exact mem_occupants.mpr hb
    exact nd.length_le_of_subset hsub
  · intro h
    let l := occupants s (.arm i d)
    have h₀ : 0 < l.length := by dsimp [l]; omega
    have h₁ : 1 < l.length := h
    refine ⟨l[0], l[1], ?_, ?_, ?_⟩
    · exact List.pairwise_iff_getElem.mp (occupants_increasing s (.arm i d)) 0 1 h₀ h₁ (by decide)
    · exact mem_occupants.mp (List.getElem_mem h₀)
    · exact mem_occupants.mp (List.getElem_mem h₁)

/-- On a physical board, `Stable` means exactly that there is no legal next step.
This includes the degenerate case `k = 0`, when the empty center batch is legal. -/
theorem Physical.stable_iff {s : Config k} (hs : Physical s) :
    Stable s ↔ ∀ m : Move k, ¬ m.Legal s := by
  constructor
  · rintro ⟨hc, ha⟩ m hm
    cases m with
    | center b =>
      have := exists_center_legal_iff.mp ⟨b, hm⟩
      rw [hs.load_eq_length] at hc
      omega
    | arm i d a b =>
      have := (exists_arm_legal_iff i d).mp ⟨a, b, hm⟩
      have h := ha i d
      rw [hs.load_eq_length] at h
      omega
  · intro hn
    constructor
    · rw [hs.load_eq_length]
      have not_ge : ¬k ≤ (occupants s .center).length := by
        intro h
        obtain ⟨b, hm⟩ := exists_center_legal_iff.mpr h
        exact hn _ hm
      omega
    · intro i d
      rw [hs.load_eq_length]
      have not_ge : ¬2 ≤ (occupants s (.arm i d)).length := by
        intro h
        obtain ⟨a, b, hm⟩ := (exists_arm_legal_iff i d).mpr h
        exact hn _ hm
      omega

theorem reachable_stable_iff {s : Config k} (hr : Reachable (initial k) s) :
    Stable s ↔ ∀ m : Move k, ¬ m.Legal s :=
  (reachable_physical hr).stable_iff

end StarFiring
