import StarFiring.RawNormal
import StarFiring.FullPack
import StarFiring.Order
import StarFiring.Avoidance

/-! The unrestricted classification. There is no normal-schedule hypothesis on
`Run.normalize`: project the actual chronological history, read its pairings,
and recombine *source* returns globally for the increasing center batches. -/
namespace StarFiring

/-- Completeness at full labeled-board strength, not just up to relative order. -/
theorem Run.normalize {ms : List (Move k)} {s : Config k}
    (r : Run (initial k) ms s) (st : Stable s) :
    ∃ c : Cert k, c.Valid ∧ s = endpoint c.F c.middle c.outer := by
  obtain ⟨P,raw,tr,_,inc,reads,boardEq⟩ := r.row_normal st
  have ledger := cutLedger_of_templates P (fun n x => by
    simpa only [tr] using r.cut_nonneg n x)
  obtain ⟨c,hv,hM,hO,hF⟩ := ledger.pack inc reads
  exact ⟨c,hv,by simpa only [hF,hM,hO] using boardEq⟩

/-- Exact fixed-size description of all reachable **stable configurations**. -/
theorem stable_reachable_iff {k : Nat} (hk : 0 < k) (s : Config k) :
    Reachable (initial k) s ∧ Stable s ↔
    ∃ c : Cert k, c.Valid ∧ s = endpoint c.F c.middle c.outer := by
  constructor
  · rintro ⟨⟨ms,r⟩,st⟩; exact r.normalize st
  · rintro ⟨c,hv,rfl⟩; exact ⟨Cert.sound hv, endpoint_stable hk ..⟩

/-- A relative middle permutation is attained by some genuine firing sequence
if and only if it has a four-mode normal-form certificate. No other hypotheses. -/
theorem realizable_iff_certified {k : Nat} (hk : 0 < k) (p : Row k → Row k) :
    Realizable p ↔ Certified p := by
  refine ⟨?_,fun h => h.realizable hk⟩
  rintro ⟨s,hr,hs,hm⟩
  obtain ⟨c,hv,rfl⟩ := (stable_reachable_iff hk s).mp ⟨hr,hs⟩
  exact ⟨c,hv,(endpoint_middle_iff ..).mp hm⟩

theorem Realizable.avoids321 {p : Row k → Row k} (h : Realizable p) : Avoids321 p := by
  obtain ⟨s,⟨ms,r⟩,hs,hm⟩ := h
  obtain ⟨c,hv,rfl⟩ := r.normalize hs
  exact hv.ranks_avoid321 ((endpoint_middle_iff ..).mp hm)

end StarFiring
