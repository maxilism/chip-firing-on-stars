import StarFiring.Pack
import StarFiring.TemplateBridge

namespace StarFiring

/-- The rows and cuts read off one unrestricted run determine a static valid
certificate whose *whole labeled endpoint* agrees with that run. -/
theorem CutLedger.pack {P : Row k → ArmTemplate k} (led : CutLedger P) {m : Row k → Mode}
    (hi : ∀ b ∈ TemplateBridge.columns P, Increasing b)
    (hr : ∀ i, m i ≠ .r ∧ (P i).Reads (m i)) :
    ∃ c : Cert k, c.Valid ∧ c.middle = (fun i => (P i).m) ∧ c.outer = (fun i => (P i).o) ∧ c.F = (fun i => (P i).F) := by
  obtain ⟨c,cv,hf,hm,ho⟩ := Pack.certificate P m (fun i => (hr i).2) led
    (hi _ (by simp [TemplateBridge.columns])) (hi _ (by simp [TemplateBridge.columns]))
    (hi _ (by simp [TemplateBridge.columns])) (hi _ (by simp [TemplateBridge.columns]))
    (hi _ (by simp [TemplateBridge.columns])) (hi _ (by simp [TemplateBridge.columns]))
  exact ⟨c,cv,hm,ho,hf⟩

end StarFiring
