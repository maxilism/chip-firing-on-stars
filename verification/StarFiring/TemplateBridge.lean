import StarFiring.TemplateWord
import StarFiring.Saturation
import StarFiring.Replay

/-! Every stable run of the unreduced game has the four local arm-event orders
encoded by `ArmTemplate`. The proof accumulates the projected word one real
move at a time, using physical load bounds for comparisons and saturation at
center cuts; it does not assume synchronous play. -/
namespace StarFiring
namespace TemplateBridge
open Counts TemplateWord

def localWord (i : Row k) (ms : List (Move k)) := (armTrace i ms).map kind

def symbolSite (i : Row k) : Nat → Site k
  | 0 => .center | n+1 => .arm i n

theorem local_count (i : Row k) (ms : List (Move k)) (n : Nat) :
    (localWord i ms).count n = fires ms (symbolSite i n) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    unfold localWord armTrace at ih ⊢
    unfold fires at ih ⊢
    cases m with
    | center b =>
      cases n <;> simp [Move.onArm,kind,symbolSite,Move.source, ih]
    | arm j d a b =>
      by_cases hij : i = j
      · subst j; cases n <;> simp [Move.onArm,kind,List.count_cons,List.countP_cons,symbolSite,Move.source,ih]
      · cases n <;> simp [Move.onArm,symbolSite,Move.source,hij,Ne.symm hij,ih]

theorem local_append (i : Row k) (xs ys : List (Move k)) :
    localWord i (xs ++ ys) = localWord i xs ++ localWord i ys := by simp [localWord,armTrace_append]

private theorem next {ms : List (Move k)} {s : Config k} {m : Move k} (i : Row k)
    (r : Run (initial k) ms s) (h : m.Legal s) (prior : localWord i ms ∈ prefixes) :
    localWord i (ms ++ [m]) ∈ prefixes := by
  have hk : 0 < k := Nat.zero_lt_of_lt i.isLt
  have bound := prefix_bound hk (r.append (Run.cons h Run.nil)) m.source
  rw [local_append]
  cases m with
  | center b =>
    change localWord i ms ++ [0] ∈ prefixes
    apply close _ prior 0 (by decide)
    simp only [allowed,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,local_count,symbolSite]
    simp [quota,Move.source] at bound
    by_cases h3 : fires ms .center = 3
    · have hq := ((Saturation.before_four hk r h h3).2 i).1; omega
    by_cases h4 : fires ms .center = 4
    · have hq := ((Saturation.before_five hk r h h4).2 i).1; omega
    by_cases h5 : fires ms .center = 5
    · have hq := ((Saturation.before_six hk r h h5).2 i).1; omega
    omega
  | arm j d a b =>
    by_cases he : i = j
    · subst j
      have hl := legal_arm_load_ge (r.nonneg initial_nonneg) h
      rw [balance r] at hl
      cases d with
      | zero =>
        have hs : localWord i [Move.arm i 0 a b] = [1] := by simp [localWord,armTrace,Move.onArm,kind]
        rw [hs]; apply close _ prior 1 (by decide)
        simp only [allowed,decide_eq_true_eq,local_count,symbolSite]
        simp only [predicted] at hl; omega
      | succ d => cases d with
        | zero =>
          have hs : localWord i [Move.arm i 1 a b] = [2] := by simp [localWord,armTrace,Move.onArm,kind]
          rw [hs]; apply close _ prior 2 (by decide)
          simp only [allowed,decide_eq_true_eq,local_count,symbolSite]
          have hz := prefix_bound hk r (.arm i 2)
          simp [quota] at hz
          simp [predicted,hz] at hl; omega
        | succ d => simp [quota,Move.source] at bound
    · simpa [localWord,armTrace,Move.onArm,he] using prior

theorem legalPrefix {ms : List (Move k)} {s} (r : Run (initial k) ms s) (i : Row k) :
    localWord i ms ∈ prefixes := by
  apply Counts.forward (P := fun xs _ => localWord i xs ∈ prefixes) _ (fun pre hl hp => next i pre hl hp) r
  exact (by decide : ([] : List Nat) ∈ prefixes)

theorem template {ms : List (Move k)} {s} (r : Run (initial k) ms s) (st : Stable s) (i : Row k) :
    ∃ p : ArmTemplate k, armTrace i ms = p.events := by
  apply decode
  apply finished _ (legalPrefix r i)
  change (localWord i ms).count 0 = 6; rw [local_count]; exact stable_counts r st .center

/-- Center batches in chronological order. Definitionally equal to
`StarFiring.centerBatches`, without an import dependency on center algebra. -/
abbrev dispatches (ms : List (Move k)) := ms.filterMap fun
  | .center b => some b | .arm .. => none

def deliveries (es : List (ArmEvent k)) := es.filterMap fun
  | .deliver a => some a | .compare .. => none

theorem actual_deliveries (ms : List (Move k)) (i : Row k) :
    (dispatches ms).map (fun b => b i) = deliveries (armTrace i ms) := by
  induction ms with
  | nil => rfl
  | cons m ms ih => cases m with
    | center b => simpa [dispatches,deliveries,armTrace,Move.onArm] using congrArg (b i :: ·) ih
    | arm j d a b => by_cases e : i = j <;> simpa [dispatches,deliveries,armTrace,Move.onArm,e] using ih

theorem template_deliveries (p : ArmTemplate k) :
    deliveries p.events = [p.A,p.B,p.T,p.D,p.E,p.F] := by
  cases e : p.early <;> cases o : p.outEarly <;>
    simp [deliveries, ArmTemplate.events, ArmTemplate.startEvents, ArmTemplate.endEvents,e,o]

theorem increasing_dispatches {s t : Config k} {ms : List (Move k)} (r : Run s ms t) :
    ∀ b ∈ dispatches ms, Increasing b := by
  induction r with
  | nil => simp [dispatches]
  | @cons ms s t m hl _ ih =>
    cases m with
    | center b => simp only [dispatches,List.filterMap_cons,List.mem_cons]; exact fun _ h => h.elim (fun e => e ▸ hl.1) (ih _)
    | arm i d a b => exact ih

/-- The six actual center columns in arm order. -/
def columns (P : Row k → ArmTemplate k) : List (Batch k) :=
  [fun i => (P i).A, fun i => (P i).B, fun i => (P i).T, fun i => (P i).D, fun i => (P i).E, fun i => (P i).F]

private theorem eq_of_row_maps (hk : 0 < k) {vs ws : List (Batch k)}
    (h : ∀ i : Row k, vs.map (· i) = ws.map (· i)) : vs = ws := by
  have i0 : Row k := ⟨0,hk⟩
  induction vs generalizing ws with
  | nil => cases ws with
    | nil => rfl
    | cons b bs => have := h i0; contradiction
  | cons a as ih => cases ws with
    | nil => have := h i0; contradiction
    | cons b bs =>
      simp only [List.map_cons,List.cons.injEq] at h
      rw [show a = b from funext fun i => (h i).1,ih (fun i => (h i).2)]

theorem column_eq {s : Config k} {ms : List (Move k)} (r : Run (initial k) ms s)
    (st : Stable s) {P : Row k → ArmTemplate k} (h : ∀ i, armTrace i ms = (P i).events) :
    dispatches ms = columns P := by
  have h0 := (stable_shape r st).1; have hc := st.1
  apply eq_of_row_maps (by omega)
  intro i; rw [actual_deliveries, h i, template_deliveries]; rfl

/-- Simultaneously recover the local labels and the increasing columns from the
actual unreduced chronological run. `Increasing` is on the literal six batches,
not on six lists chosen independently by different rows. -/
theorem extract {s : Config k} {ms : List (Move k)} (r : Run (initial k) ms s) (st : Stable s) :
    ∃ P : Row k → ArmTemplate k, (∀ i, armTrace i ms = (P i).events) ∧
      dispatches ms = columns P ∧ (∀ b ∈ columns P, Increasing b) := by
  classical
  let P := fun i => Classical.choose (template r st i)
  have he : ∀ i, armTrace i ms = (P i).events := fun i => Classical.choose_spec (template r st i)
  have hc := column_eq r st he
  exact ⟨P,he,hc,hc ▸ increasing_dispatches r⟩

end TemplateBridge
end StarFiring
