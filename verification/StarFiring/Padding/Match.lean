import StarFiring.Padding.Gap

/-! # Last-to-first gap matching

Within the gap following a high anchor `h`, a matched row is in the last
`gapR w h` positions. Its rank is taken in the same order from the first
`gapR w h` ranks strictly above `w h`.
-/
namespace StarFiring.Padding

variable {n : Nat} {w : Fin n → Fin n}

/-- The anchor `h` owns row `a` among the last `r` slots before its successor. -/
def InMatch (w : Fin n → Fin n) (h a : Fin n) : Prop :=
  High w h ∧ nextPos w h - gapR w h ≤ a.val ∧ a.val < nextPos w h

instance (w : Fin n → Fin n) (h a : Fin n) : Decidable (InMatch w h a) := by
  unfold InMatch High; infer_instance

private theorem r_le_pos (w : Fin n → Fin n) (h : Fin n) :
    gapR w h ≤ nextPos w h - h.val - 1 := Nat.min_le_left ..

private theorem r_le_val (w : Fin n → Fin n) (h : Fin n) :
    gapR w h ≤ nextVal w h - (w h).val - 1 := Nat.min_le_right ..

theorem InMatch.lt {a h : Fin n} (m : InMatch w h a) : h < a := by
  obtain ⟨_,lo,_⟩ := m; have := r_le_pos w h; have := lt_nextPos w h
  show h.val < a.val; omega

theorem InMatch.unique {a h g : Fin n} (m : InMatch w h a) (k : InMatch w g a) : h = g := by
  have := m.lt; have := k.lt
  have ha := m.2.2; have ga := k.2.2
  by_cases hh : h < g
  · have := nextPos_le_of_high hh k.1; simp only [Fin.lt_def] at *; omega
  · by_cases hg : g < h
    · have := nextPos_le_of_high hg m.1; simp only [Fin.lt_def] at *; omega
    · apply Fin.ext; simp only [Fin.lt_def] at *; omega

/-- Integer rank prescribed at row `a` of anchor `h`'s suffix. -/
def matchRank (w : Fin n → Fin n) (h a : Fin n) : Nat :=
  (w h).val + 1 + (a.val - (nextPos w h - gapR w h))

private theorem rank_bounds {h a : Fin n} (m : InMatch w h a) :
    (w h).val < matchRank w h a ∧ matchRank w h a < nextVal w h := by
  obtain ⟨_,lo,hi⟩ := m
  have := r_le_pos w h; have := r_le_val w h
  unfold matchRank; omega

/-- Search for the unique matching anchor; no search across labels is needed. -/
def matchValue (w : Fin n → Fin n) (a : Fin n) : Option (Fin n) :=
  match m : (List.finRange n).find? (fun h => decide (InMatch w h a)) with
  | none => none
  | some h => some ⟨matchRank w h a, by
      have hh : InMatch w h a := by simpa using (List.find?_some m)
      have := (rank_bounds hh).2; have := nextVal_le_n w h; omega⟩

theorem matchValue_spec {a v : Fin n} : matchValue w a = some v ↔
    ∃ h, InMatch w h a ∧ v.val = matchRank w h a := by
  unfold matchValue
  split
  next m =>
    constructor
    · intro bad; contradiction
    · rintro ⟨h,hh,_⟩; exact False.elim ((List.find?_eq_none.mp m h (List.mem_finRange h)) (decide_eq_true hh))
  next g m =>
    have hg : InMatch w g a := by simpa using (List.find?_some m)
    constructor
    · intro hv; cases hv; exact ⟨g,hg,rfl⟩
    · rintro ⟨h,hh,hv⟩; cases hh.unique hg; exact congrArg some (Fin.ext hv.symm)

private theorem InMatch.some {a h : Fin n} (m : InMatch w h a) :
    ∃ v, matchValue w a = some v := by
  have b := (rank_bounds m).2; have := nextVal_le_n w h
  exact ⟨⟨matchRank w h a,by omega⟩,matchValue_spec.mpr ⟨h,m,rfl⟩⟩

theorem matchValue_source_low {a v : Fin n} (ma : matchValue w a = some v) : ¬High w a := by
  intro ha; obtain ⟨h,m,_⟩ := matchValue_spec.mp ma
  have := nextPos_le_of_high m.lt ha; have := m.2.2; omega

theorem matchValue_isSome_low {a : Fin n} (h : (matchValue w a).isSome = true) : ¬High w a := by
  cases ma : matchValue w a with
  | none => simp [ma] at h
  | some t => exact matchValue_source_low ma

theorem matchValue_beforeHigh (inc : ∀ i j, High w i → High w j → i < j → w i < w j)
    {a v h : Fin n} (ma : matchValue w a = some v) (hh : High w h) (hlt : a < h) : v < w h := by
  obtain ⟨g,m,hv⟩ := matchValue_spec.mp ma
  have := nextVal_le_of_high (Fin.lt_trans m.lt hlt) hh (fun i j ij hi hj => inc i j hi hj ij)
  have := (rank_bounds m).2; show v.val < (w h).val; omega

theorem matchValue_afterHigh (inc : ∀ i j, High w i → High w j → i < j → w i < w j)
    {a v h : Fin n} (ma : matchValue w a = some v) (hh : High w h) (hlt : h < a) : w h < v := by
  obtain ⟨g,m,hv⟩ := matchValue_spec.mp ma
  have lt : ¬ g < h := by intro gh; have := nextPos_le_of_high gh hh; have := m.2.2; simp only [Fin.lt_def] at hlt; omega
  have := (rank_bounds m).1
  by_cases he : h = g
  · cases he; show (w h).val < v.val; omega
  · have hg : h < g := by simp only [Fin.lt_def, Fin.ext_iff] at *; omega
    have lt' := inc h g hh m.1 hg
    simp only [Fin.lt_def] at lt' ⊢; omega

theorem matchValue_target_low (inc : ∀ i j, High w i → High w j → i < j → w i < w j)
    {a b t : Fin n} (ma : matchValue w a = some t) (e : w b = t) : ¬High w b := by
  intro hb; by_cases eq : b = a
  · subst b; exact matchValue_source_low ma hb
  · by_cases ba : b < a
    · have := matchValue_afterHigh inc ma hb ba; rw [e] at this; exact (Fin.lt_irrefl t) this
    · have ab : a < b := by simp only [Fin.lt_def,Fin.ext_iff] at *; omega
      have := matchValue_beforeHigh inc ma hb ab; rw [e] at this; exact (Fin.lt_irrefl t) this

theorem matchValue_inc (inc : ∀ i j, High w i → High w j → i < j → w i < w j)
    {a b t u : Fin n} (ma : matchValue w a = some t) (mb : matchValue w b = some u)
    (hlt : a < b) : t < u := by
  obtain ⟨h,m,ht⟩ := matchValue_spec.mp ma; obtain ⟨g,k,hu⟩ := matchValue_spec.mp mb
  by_cases eq : h = g
  · subst g; have := m.2.1; have := k.2.1
    simp only [matchRank] at *; simp only [Fin.lt_def] at hlt ⊢; omega
  · have ag : a < g := by
      by_cases hg : h < g
      · have := nextPos_le_of_high hg k.1; have := m.2.2; show a.val < g.val; omega
      · have gh : g < h := by simp only [Fin.lt_def,Fin.ext_iff] at *; omega
        have := nextPos_le_of_high gh m.1; have := k.2.2; have := m.lt
        simp only [Fin.lt_def] at *; omega
    exact Fin.lt_trans (matchValue_beforeHigh inc ma k.1 ag) (matchValue_afterHigh inc mb k.1 k.lt)

theorem matchValue_suffix {a b t : Fin n} (ma : matchValue w a = some t)
    (mb : matchValue w b = none) (hlt : a < b) : ∃ h, a < h ∧ h ≤ b ∧ High w h := by
  obtain ⟨h,m,_⟩ := matchValue_spec.mp ma
  have ab : a.val < b.val := hlt
  have bound : nextPos w h ≤ b.val := by
    apply Nat.le_of_not_gt; intro hb
    have mo : InMatch w h b := ⟨m.1, Nat.le_trans m.2.1 (Nat.le_of_lt ab),hb⟩
    obtain ⟨v,hv⟩ := mo.some; rw [mb] at hv; contradiction
  have hn : nextPos w h < n := by omega
  exact ⟨⟨_,hn⟩,m.2.2,bound,high_nextPos hn⟩

/-- A high threshold `e` separates entire gaps: no row strictly beyond `e`
can have its matching gap start before `e`. -/
private theorem suffix_match_iff {a e : Fin n} (he : High w e) :
    (e < a ∧ (matchValue w a).isSome = true) ↔ ∃ h, e ≤ h ∧ InMatch w h a := by
  constructor
  · rintro ⟨ea,hm⟩; cases ma : matchValue w a with
    | none => simp [ma] at hm
    | some v =>
      obtain ⟨h,m,_⟩ := matchValue_spec.mp ma
      refine ⟨h,?_,m⟩
      by_cases eh : e ≤ h
      · exact eh
      · have lt : h < e := by simp only [Fin.le_def,Fin.lt_def] at *; omega
        have := nextPos_le_of_high lt he; have := m.2.2; simp only [Fin.lt_def] at *; omega
  · rintro ⟨h,eh,m⟩; obtain ⟨v,hv⟩ := m.some
    exact ⟨Nat.lt_of_le_of_lt eh m.lt, by simp [hv]⟩

/-- All matches strictly past a high row come from its own gap or a later
one. The disjoint suffixes contribute exactly their `gapR` counts, including
an empty gap and a gap ending at the terminal sentinel. -/
theorem matchValue_suffix_count {e : Fin n} (he : High w e) :
    suffixR w e = (List.finRange n).countP (fun p => decide (e < p) && (matchValue w p).isSome) := by
  let R (h a : Fin n) := decide (e ≤ h ∧ InMatch w h a)
  have unique (a h j : Fin n) (hh : R h a = true) (hj : R j a = true) : h = j :=
    (of_decide_eq_true hh).2.unique (of_decide_eq_true hj).2
  have count (h : Fin n) :
      (if e ≤ h ∧ High w h then gapR w h else 0) = (List.finRange n).countP (R h) := by
    by_cases z : e ≤ h ∧ High w h
    · simp only [ite_eq_left z]; symm
      have rb := r_le_pos w h
      have cr := countFinRightBlock (r := gapR w h) (q := nextPos w h)
        (by omega) (nextPos_le_n w h)
      rw [← cr]; apply List.countP_congr; intro a _; simp [R,InMatch,z.1,z.2]
    · simp only [ite_eq_right z]; symm; apply List.countP_eq_zero.mpr
      intro a _ ha; exact z ⟨(of_decide_eq_true ha).1,(of_decide_eq_true ha).2.1⟩
  unfold suffixR
  rw [List.map_congr_left (fun h _ => count h),sum_countP_fibers _ _ unique]
  apply List.countP_congr; intro a _
  simpa only [R,decide_eq_true_eq,Bool.and_eq_true] using (suffix_match_iff (a := a) he).symm

end StarFiring.Padding
