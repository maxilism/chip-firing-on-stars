import StarFiring.Core

/-! A multiset interface for staging legal transfers. Frames can contain
arbitrary untouched tokens; they do not restrict the choice of moved chips. -/
namespace StarFiring
abbrev Token (k : Nat) := Site k × Chip k
def board (ts : List (Token k)) : Config k := fun p x => (ts.count (p,x) : Int)
abbrev rows (k : Nat) := List.finRange k
def centerTokens (b : Batch k) : List (Token k) := (rows k).map fun i => (.center,b i)
def deliveryTokens (b : Batch k) : List (Token k) := (rows k).map fun i => (.arm i 0,b i)

theorem board_perm {xs ys : List (Token k)} (h : xs.Perm ys) : board xs = board ys := by
  funext p x; simp only [board, h.count_eq]

theorem board_append (xs ys : List (Token k)) (t x) : board (xs++ys) t x = board xs t x + board ys t x := by
  simp [board, List.count_append]

theorem board_cons (p : Site k) (a : Chip k) (xs : List (Token k)) (t x) :
    board ((p,a)::xs) t x = board xs t x + ind (t=p) * ind (a=x) := by
  by_cases ht : t=p <;> by_cases hx : a=x <;> simp_all [board,ind, Prod.ext_iff, eq_comm]

private theorem count_image {n} (f : Fin n → α) [DecidableEq α] (hf : Function.Injective f) (v : α) :
    (((List.finRange n).map f).count v : Int) = ind (∃ i, f i = v) := by
  have hn : ((List.finRange n).map f).Nodup := List.pairwise_map.mpr
    ((List.nodup_finRange n).imp (fun hab h => hab (hf h)))
  rw [hn.count]; simp [List.mem_map, List.mem_finRange, ind]; split <;> rfl

theorem increasing_injective {b : Batch k} (h : Increasing b) : Function.Injective b := by
  intro i j e
  apply Fin.ext; apply Classical.byContradiction; intro hij
  have hij' : i.val < j.val ∨ j.val < i.val := by omega
  rcases hij' with h'|h'
  · exact Fin.ne_of_lt (h i j h') e
  · exact Fin.ne_of_lt (h j i h') e.symm

theorem board_initial : board ((List.finRange (3*k)).map fun x => (Site.center,x)) = initial k := by
  funext p x; unfold board; rw [count_image _ (fun _ _ e => congrArg Prod.snd e)]
  cases p <;> simp [initial,ind]

theorem board_centerTokens {b : Batch k} (hb : Increasing b) (t x) :
    board (centerTokens b) t x = ind (t=.center) * ind (Has b x) := by
  unfold board centerTokens
  rw [count_image _ (fun _ _ e => increasing_injective hb (congrArg Prod.snd e))]
  cases t <;> simp [ind,Has] <;> rfl

theorem board_deliveryTokens (b : Batch k) (t x) : board (deliveryTokens b) t x =
    match t with | .arm i 0 => ind (b i = x) | _ => 0 := by
  unfold board deliveryTokens
  rw [count_image _ (fun _ _ h => by have e := congrArg Prod.fst h; exact Site.arm.inj e |>.1)]
  cases t with
  | center => simp [ind]
  | arm i d => cases d <;> simp [ind]

theorem Run.append (h : Run s xs t) (g : Run t ys u) : Run s (xs++ys) u := by
  induction h with
  | nil => exact g
  | cons hl _ ih => exact .cons hl (ih g)

theorem Reachable.refl (s : Config k) : Reachable s s := ⟨[], .nil⟩
theorem Reachable.trans (h : Reachable s t) (g : Reachable t u) : Reachable s u := by
  obtain ⟨xs,h⟩ := h; obtain ⟨ys,g⟩ := g; exact ⟨_,h.append g⟩

theorem Run.frame {s t : Config k} (h : Run s ms t) (f : Config k) (hf : ∀ p x, 0 ≤ f p x) :
    Run (fun p x => s p x + f p x) ms (fun p x => t p x + f p x) := by
  induction h with
  | nil => exact .nil
  | @cons xs t s m hl _ ih =>
    apply Run.cons
    · cases m with
      | center b => exact ⟨hl.1, fun i => by have := hl.2 i; have := hf .center (b i); dsimp; omega⟩
      | arm i d a b => exact ⟨hl.1, by have := hl.2.1; have := hf (.arm i d) a; dsimp; omega,
          by have := hl.2.2; have := hf (.arm i d) b; dsimp; omega⟩
    · have ex : m.act (fun p x => s p x + f p x) = (fun p x => m.act s p x + f p x) := by
        funext p x; simp only [Move.act]; omega
      rw [ex]; exact ih

theorem Reachable.frame {xs ys : List (Token k)} (h : Reachable (board xs) (board ys)) (ctx : List (Token k)) :
    Reachable (board (xs++ctx)) (board (ys++ctx)) := by
  obtain ⟨ms, hh⟩ := h
  have eqn (l : List (Token k)) : board (l++ctx) = (fun p x => board l p x + board ctx p x) := by
    funext p x; exact board_append ..
  rw [eqn,eqn]; exact ⟨ms, hh.frame (board ctx) (by intros; simp [board])⟩

theorem fireCenter {b : Batch k} (hb : Increasing b) (ctx : List (Token k)) :
    Reachable (board (centerTokens b ++ ctx)) (board (deliveryTokens b ++ ctx)) := by
  apply Reachable.frame
  refine ⟨[.center b], .cons ⟨hb, ?_⟩ ?_⟩
  · intro i; simp [board_centerTokens hb, ind, show Has b (b i) from ⟨i,rfl⟩]
  · have h : (Move.center b).act (board (centerTokens b)) = board (deliveryTokens b) := by
      funext t x; rw [Move.act,board_centerTokens hb,board_deliveryTokens]
      cases t with
      | center => simp [Move.delta,ind]; split <;> decide
      | arm i d => cases d <;> simp [Move.delta,ind]
    rw [h]; exact .nil

theorem fireArm {i : Row k} {d : Nat} {a b : Chip k} (hab : a < b) (ctx : List (Token k)) :
    Reachable (board ((Site.arm i d,a)::(.arm i d,b)::ctx))
      (board ((inward i d,a)::(.arm i (d+1),b)::ctx)) := by
  refine ⟨[.arm i d a b], .cons ⟨hab, ?_, ?_⟩ ?_⟩
  · simp only [board_cons];
    simp [ind, Ne.symm (Fin.ne_of_lt hab),board]
  · simp only [board_cons];
    simp [ind,Fin.ne_of_lt hab,board]
  · have h : (Move.arm i d a b).act (board ((Site.arm i d,a)::(.arm i d,b)::ctx)) =
        board ((inward i d,a)::(.arm i (d+1),b)::ctx) := by
      funext t x; simp only [board_cons,Move.act,Move.delta,Int.mul_add]; omega
    rw [h]; exact .nil
end StarFiring
