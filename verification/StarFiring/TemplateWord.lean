import StarFiring.ArmEvents

/-! A small explicit language over *unlabeled* local operations: symbol 0 is a
center delivery and symbol d+1 is a comparison at raw depth d. Membership in
one of its four complete words restores a labeled `ArmTemplate` without any
reordering. -/
namespace StarFiring.TemplateWord

def kind : ArmEvent k → Nat
  | .deliver _ => 0
  | .compare d _ _ => d+1

def words : List (List Nat) := [
  [0,0,1,0,0,1,2,0,1,0], [0,0,1,0,0,1,0,2,1,0],
  [0,0,0,1,0,1,2,0,1,0], [0,0,0,1,0,1,0,2,1,0]]

def prefixes := words.flatMap (fun w => (List.range (w.length+1)).map (fun n => w.take n))

/-- The constraints used at the next event: a center firing must be supplied by
sufficient prior returns at the synchronization cuts; positive-depth firing
requires two chips at its source. -/
def allowed (w : List Nat) (n : Nat) : Bool :=
  let c := w.count 0; let z := w.count 1; let o := w.count 2
  match n with
  | 0 => c < 3 || (c == 3 && 1 ≤ z) || (c == 4 && 2 ≤ z) || (c == 5 && 3 ≤ z)
  | 1 => 2*z+2 ≤ c+o
  | 2 => 2*o+2 ≤ z
  | _+3 => false

/-- Finite language closure. This checks only four fixed words of length ten,
independent of the number of arms and the chip labels. -/
theorem close : ∀ w ∈ prefixes, ∀ n ∈ [0,1,2], allowed w n = true → w ++ [n] ∈ prefixes := by decide

theorem finished : ∀ w ∈ prefixes, w.count 0 = 6 → w ∈ words := by decide

private theorem popDelivery {es : List (ArmEvent k)} {ds : List Nat}
    (h : es.map kind = 0 :: ds) : ∃ a ts, es = .deliver a :: ts ∧ ts.map kind = ds := by
  obtain ⟨e,ts,rfl,he,ht⟩ := List.map_eq_cons_iff.mp h
  cases e with
  | deliver x => exact ⟨x,ts,rfl,ht⟩
  | compare d a b => contradiction

private theorem popCompare {es : List (ArmEvent k)} {ds : List Nat} {d : Nat}
    (h : es.map kind = (d+1) :: ds) : ∃ a b ts, es = .compare d a b :: ts ∧ ts.map kind = ds := by
  obtain ⟨e,ts,rfl,he,ht⟩ := List.map_eq_cons_iff.mp h
  cases e with
  | deliver x => contradiction
  | compare n a b =>
    have := Nat.succ.inj he; subst n; exact ⟨a,b,ts,rfl,ht⟩

theorem decode {es : List (ArmEvent k)} (h : es.map kind ∈ words) :
    ∃ p : ArmTemplate k, es = p.events := by
  simp only [words, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h
  all_goals
    -- Each encoded word has exactly ten symbols. Unwrap one actual event per
    -- symbol, preserving the chip labels while the two parsers inspect its kind.
    iterate 10
      first | obtain ⟨_,_,rfl,ht⟩ := popDelivery h
            | obtain ⟨_,_,_,rfl,ht⟩ := popCompare h
      revert ht; clear h; intro h
    obtain rfl := List.map_eq_nil_iff.mp h
  -- The four words above are in (early, outEarly) order. Once these two
  -- timing bits are supplied, equality of events determines all fourteen labels.
  · exact ⟨⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,true,true⟩,rfl⟩
  · exact ⟨⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,true,false⟩,rfl⟩
  · exact ⟨⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,false,true⟩,rfl⟩
  · exact ⟨⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,false,false⟩,rfl⟩

end StarFiring.TemplateWord
