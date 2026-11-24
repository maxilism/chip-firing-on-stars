import StarFiring.Normal
import StarFiring.TemplateBridge
import StarFiring.Endpoint

/-! Whole-run reading of the actual arm labels, before packaging the spares in
`Cert.X`. This joins the order-free counting argument to the labeled local
comparison analysis. -/
namespace StarFiring

/-- A stable reachable board is exactly empty at the center, label by label. -/
theorem Run.center_empty {ms : List (Move k)} {s} (r : Run (initial k) ms s) (st : Stable s) :
    ∀ x, s .center x = 0 := by
  have hs := r.physical (initial_physical _)
  have hl := (Counts.stable_shape r st).1
  rw [hs.load_eq_length] at hl
  have he : occupants s .center = [] := List.length_eq_zero_iff.mp (by omega)
  intro x
  rcases hs.zero_or_one .center x with hz|ho
  · exact hz
  · have hx : x ∈ occupants s .center := mem_occupants.mpr (by omega)
    simp [he] at hx

/-- The three extracted entries of each row fill the *exact* target board. -/
theorem Run.read_templates {ms : List (Move k)} {s} (r : Run (initial k) ms s) (st : Stable s)
    {P : Row k → ArmTemplate k} (ht : ∀ i, armTrace i ms = (P i).events) :
    (∃ c : Row k → Mode, ∀ i, c i ≠ .r ∧ (P i).Reads (c i)) ∧
    s = endpoint (fun i => (P i).F) (fun i => (P i).m) (fun i => (P i).o) := by
  classical
  have read (i : Row k) := ArmTemplate.extract (P i) (by simpa only [armState_initial, ht i] using r.armProject i)
  refine ⟨⟨fun i => Classical.choose (read i).1, fun i => Classical.choose_spec (read i).1⟩,?_⟩
  funext site x
  cases site with
  | center => rw [endpoint_center, r.center_empty st x]
  | arm i n =>
    have he := congrFun (congrFun (read i).2 n) x
    rw [endpoint_arm]
    have one (y : Chip k) : ([y].count x : Int) = ind (y=x) := by
      by_cases h : y=x <;> simp [ind,h]
    match n with
    | 0 | 1 | 2 | _+3 => simpa [armState,ArmTemplate.bag,one] using he

/-- A relative rank comparison read directly from the selected local templates. -/
theorem Run.raw_middle_iff {ms : List (Move k)} {s} (r : Run (initial k) ms s) (st : Stable s)
    {P : Row k → ArmTemplate k} (ht : ∀ i, armTrace i ms = (P i).events) (p : Row k → Row k) :
    MiddleOrder s p ↔ ∀ i j, (P i).m < (P j).m ↔ p i < p j := by
  rw [(r.read_templates st ht).2]; apply endpoint_middle_iff

/-- Normalize a completely arbitrary stable trace of elementary firings. This
recovers the six actual increasing batches, with all local minor/major transfers. -/
theorem Run.row_normal {ms : List (Move k)} {s} (r : Run (initial k) ms s) (st : Stable s) :
    ∃ (P : Row k → ArmTemplate k) (c : Row k → Mode),
      (∀ i, armTrace i ms = (P i).events) ∧
      TemplateBridge.dispatches ms = TemplateBridge.columns P ∧
      (∀ b ∈ TemplateBridge.columns P, Increasing b) ∧
      (∀ i, c i ≠ .r ∧ (P i).Reads (c i)) ∧
      s = endpoint (fun i => (P i).F) (fun i => (P i).m) (fun i => (P i).o) := by
  obtain ⟨P,ht,hd,hi⟩ := TemplateBridge.extract r st
  obtain ⟨⟨c,hc⟩,he⟩ := r.read_templates st ht
  exact ⟨P,c,ht,hd,hi,hc,he⟩
end StarFiring
