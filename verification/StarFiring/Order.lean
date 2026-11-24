import StarFiring.Cert
import StarFiring.Physical

namespace StarFiring

/-- Pure, finite normal-form predicate: a certificate gives the requested ranks. -/
def Certified (p : Row k → Row k) : Prop :=
  ∃ c : Cert k, c.Valid ∧ ∀ i j, c.middle i < c.middle j ↔ p i < p j

/-- No permutation hypothesis is hidden in `Realizable`: ties cannot occur,
and the returned rank map uses exactly `Fin k`. -/
theorem Realizable.permutation {p : Row k → Row k} (h : Realizable p) :
    ((rows k).map p).Perm (rows k) := by
  obtain ⟨s,hs,_,mid,hm,ho⟩ := h
  have phys := reachable_physical hs
  have distinct {i j : Row k} (e : mid i = mid j) : i = j := by
    obtain ⟨q,_,un⟩ := phys.unique_site (mid i)
    exact (Site.arm.inj ((un _ (hm i)).trans (un _ (e ▸ hm j)).symm)).1
  have inj : Function.Injective p := by
    intro i j ep; apply distinct; apply Fin.ext
    have a : ¬ mid i < mid j := fun lt => Fin.ne_of_lt ((ho ..).mp lt) ep
    have b : ¬ mid j < mid i := fun lt => Fin.ne_of_lt ((ho ..).mp lt) ep.symm
    simp only [Fin.lt_def] at a b; omega
  have hn : ((rows k).map p).Nodup := (List.nodup_finRange k).map p (fun _ _ h e => h (inj e))
  apply (List.perm_ext_iff_of_nodup hn (List.nodup_finRange k)).mpr
  intro i; simp only [rows,List.mem_finRange,iff_true]
  apply Classical.byContradiction; intro hmissing
  have bigger : (i :: (rows k).map p).Nodup := List.nodup_cons.mpr ⟨hmissing,hn⟩
  have := bigger.length_le_of_subset (l₂ := rows k) (fun a _ => List.mem_finRange a)
  simp [rows] at this; omega

theorem Certified.realizable {p : Row k → Row k} (h : Certified p) (hk : 0 < k) : Realizable p := by
  obtain ⟨c,hv,hr⟩ := h; exact Cert.realizable hv hk hr

end StarFiring
