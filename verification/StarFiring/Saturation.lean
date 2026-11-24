import StarFiring.Counts

/-! Counts at intermediate center firings. All statements concern legal prefixes;
they do not assume that the trace ends in a stable state or follows a prescribed
order of firings on the arms. -/
namespace StarFiring.Saturation

open Counts
variable {k : Nat} {s : Config k} {ms : List (Move k)} {b : Batch k}

/-- A comparison odometer truncated at the first two depths. -/
private def cap (n a b : Nat) : Tally k
  | .center => n | .arm _ 0 => a | .arm _ 1 => b | .arm _ (_+2) => 0

private theorem cap_bound (hk : 0 < k) (r : Run (initial k) ms s)
    {n a b : Nat} (hn : fires ms .center ≤ n)
    (h₁ : (n : Int) - 2 * a + b < 2) (h₂ : (a : Int) - 2*b < 2) (h₃ : b < 2) :
    ∀ v, fires ms v ≤ cap n a b v := by
  apply partial_bound hk r _ _ hn
  intro i d
  cases d with
  | zero => exact h₁
  | succ d => cases d with
    | zero => simpa [predicted, cap] using h₂
    | succ d => cases d <;> simp [predicted, cap] <;> omega

/-- No arm can fire with at most one delivery. -/
theorem before_two (hk : 0 < k) (r : Run (initial k) ms s)
    (hn : fires ms .center ≤ 1) (i : Row k) (d : Nat) : fires ms (.arm i d) = 0 := by
  have h := cap_bound hk r (a:=0) (b:=0) hn (by decide) (by decide) (by decide) (.arm i d)
  cases d <;> (try rename_i d; cases d) <;> simpa [cap] using h

/-- With at most three deliveries, the only possible arm firing is a
single level-1 comparison. In particular a level-2 return cannot help to
pay for a second comparison. -/
theorem before_four_bound (hk : 0 < k) (r : Run (initial k) ms s)
    (hn : fires ms .center ≤ 3) (i : Row k) : fires ms (.arm i 0) ≤ 1 ∧
    ∀ d, fires ms (.arm i (d+1)) = 0 := by
  have h := cap_bound hk r (a:=1) (b:=0) hn (by decide) (by decide) (by decide)
  refine ⟨h _, fun d => ?_⟩
  have := h (.arm i (d+1)); cases d <;> simpa [cap] using this

private theorem sum_rigid (xs : List α) (f g : α → Int) (hb : ∀ x, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum ∧
      ((xs.map g).sum ≤ (xs.map f).sum → ∀ x ∈ xs, f x = g x) := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨hle, heq⟩ := ih
    have hy := hb y
    simp only [List.map_cons,List.sum_cons, List.mem_cons]
    exact ⟨by omega, fun h x hx => hx.elim (fun e => e ▸ (by omega : f y = g y))
      (heq (by omega) x)⟩

/-- If every arm has at most `a` returns and the next batch requires their
sum to be at least `a*k`, all quotas are met and that batch exhausts the center. -/
private theorem saturated (r : Run (initial k) ms s) (h : (Move.center b).Legal s)
    (a : Nat) (hn : fires ms .center = a+2) (hr : ∀ i, fires ms (.arm i 0) ≤ a) :
    load s .center = k ∧ ∀ i, fires ms (.arm i 0) = a := by
  let f : Row k → Int := fun i => fires ms (.arm i 0)
  have hle : ∀ i, f i ≤ (a : Int) := fun i => Int.ofNat_le.mpr (hr i)
  have ht := rowSum_le hle
  rw [rowSum_const] at ht
  have hc := balance r .center
  simp only [predicted, hn, Int.natCast_add, Int.add_mul] at hc
  change load s .center = 3 * (k:Int) - ((a:Int) * k + (2 : Nat) * (k:Int)) + rowSum f at hc
  rw [Int.mul_comm (a:Int) (k:Int)] at hc
  have hl := legal_center_load_ge (r.nonneg initial_nonneg) h
  have hsum : (k:Int)*a ≤ rowSum f := by omega
  refine ⟨by omega, fun i => ?_⟩
  rw [← rowSum_const] at hsum
  have heq := (sum_rigid (List.finRange k) f (fun _ => (a:Int)) hle).2 hsum i (List.mem_finRange i)
  exact Int.ofNat_inj.mp heq

theorem before_four (hk : 0 < k) (r : Run (initial k) ms s) (h : (Move.center b).Legal s)
    (hn : fires ms .center = 3) : load s .center = k ∧
    ∀ i, fires ms (.arm i 0) = 1 ∧ ∀ d, fires ms (.arm i (d+1)) = 0 := by
  have hp := before_four_bound hk r (Nat.le_of_eq hn)
  obtain ⟨hc, he⟩ := saturated r h 1 hn fun i => (hp i).1
  exact ⟨hc, fun i => ⟨he i, (hp i).2⟩⟩

theorem before_five (hk : 0 < k) (r : Run (initial k) ms s) (h : (Move.center b).Legal s)
    (hn : fires ms .center = 4) : load s .center = k ∧
    ∀ i, fires ms (.arm i 0) = 2 ∧ fires ms (.arm i 1) ≤ 1 ∧
      ∀ d, fires ms (.arm i (d+2)) = 0 := by
  have hp := cap_bound hk r (a:=2) (b:=1) (Nat.le_of_eq hn) (by decide) (by decide) (by decide)
  obtain ⟨hc, he⟩ := saturated r h 2 hn fun i => hp (.arm i 0)
  exact ⟨hc, fun i => ⟨he i, hp _, fun d => Nat.eq_zero_of_le_zero (hp (.arm i (d+2)))⟩⟩

theorem before_six (hk : 0 < k) (r : Run (initial k) ms s) (h : (Move.center b).Legal s)
    (hn : fires ms .center = 5) : load s .center = k ∧
    ∀ i, fires ms (.arm i 0) = 3 ∧ fires ms (.arm i 1) = 1 ∧
      ∀ d, fires ms (.arm i (d+2)) = 0 := by
  have hp := cap_bound hk r (a:=3) (b:=1) (Nat.le_of_eq hn) (by decide) (by decide) (by decide)
  obtain ⟨hc, he⟩ := saturated r h 3 hn fun i => hp (.arm i 0)
  refine ⟨hc, fun i => ⟨he i, ?_, fun d => Nat.eq_zero_of_le_zero (hp (.arm i (d+2)))⟩⟩
  have hb : fires ms (.arm i 1) ≤ 1 := hp _
  have hl := load_nonneg (r.nonneg initial_nonneg) (.arm i 0)
  rw [balance r, predicted, hn, he i] at hl
  omega

end StarFiring.Saturation
