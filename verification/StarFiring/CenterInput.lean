import StarFiring.Center
import StarFiring.CutLedger

/-! Convert the actual cut account into static resources.  The fourth dispatch is
precisely the unused reserve together with first returns, less the third batch,
all counted with multiplicity. -/
namespace StarFiring

theorem CutLedger.resources {p : Row k → ArmTemplate k} (ledger : CutLedger p)
    (ha : Increasing (fun i => (p i).A)) (hb : Increasing (fun i => (p i).B)) :
    (∀ x, Has (fun i => (p i).A) x → ¬ Has (fun i => (p i).B) x) ∧ ∃ spare : List (Chip k),
    (List.finRange (3*k)).Perm (Center.col (fun i => (p i).L) ++ (Center.col (fun i => (p i).H) ++ spare)) ∧
    (∀ x, Has (fun i => (p i).T) x → x ∈ spare ∨ ∃ i, (p i).early = true ∧ (p i).r1 = x) ∧
    (∀ x, (Center.col (fun i => (p i).T)).count x + (Center.col (fun i => (p i).D)).count x =
      spare.count x + (Center.col (fun i => (p i).r1)).count x) := by
  obtain ⟨disj,spare,hpart,ht,hd⟩ := Center.resources ha hb ledger.hB ledger.hT ledger.hD
  refine ⟨disj,spare,hpart,?_,hd⟩
  intro x hx; rcases ht x hx with unused | replay
  · exact .inl unused
  · right; obtain ⟨i,_,h⟩ := List.mem_flatMap.mp replay
    cases he : (p i).early
    · simp [he] at h
    · refine ⟨i,he,?_⟩; simpa [he,eq_comm] using h

end StarFiring
