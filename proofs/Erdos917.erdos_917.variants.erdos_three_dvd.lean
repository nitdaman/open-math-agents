import FormalConjectures.ErdosProblems.«917»

-- Problem: Erdős Problem 917 — erdos three dvd
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/917.lean:195 (declaration Erdos917.erdos_917.variants.erdos_three_dvd)
-- Credit: @NoahPuckett-IO (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
The witness is the join of `t = k / 3` disjoint copies of the odd cycle `C_m`, on the vertex set
`Fin (m * t)`: vertex `x` lies in block `x / m` at position `x % m`. Two vertices are adjacent if
they are in different blocks, or in the same block at neighbouring positions of the cycle.

* It is `3t`-colourable (three colours per block), and not `(3t - 1)`-colourable, since each
  block needs three colours and different blocks share none.
* Deleting a vertex or a cycle edge leaves a path in its block, which needs only two colours.
  Deleting an edge `uw` between two blocks lets `u` and `w` share a colour, each being the only
  vertex of its block with that colour.
* Every vertex has degree `m (t - 1) + 2`, which gives the edge count.
-/

namespace OMA.E917

open Finset SimpleGraph

/-- The block of a vertex. -/
def blk (m : ℕ) {n : ℕ} (x : Fin n) : ℕ := x.val / m

/-- The position of a vertex in its block. -/
def pos (m : ℕ) {n : ℕ} (x : Fin n) : ℕ := x.val % m

/-- Neighbouring positions on the cycle of length `m`. -/
def cyc (m p q : ℕ) : Prop := q = p + 1 ∨ p = q + 1 ∨ (p = 0 ∧ q + 1 = m) ∨ (q = 0 ∧ p + 1 = m)

instance (m p q : ℕ) : Decidable (cyc m p q) := by unfold cyc; infer_instance

lemma pos_lt {m n : ℕ} (hm : 0 < m) (x : Fin n) : pos m x < m := Nat.mod_lt _ hm

lemma blk_lt {m t : ℕ} (x : Fin (m * t)) : blk m x < t := Nat.div_lt_of_lt_mul x.isLt

lemma ext' {m n : ℕ} (x y : Fin n) (h1 : blk m x = blk m y) (h2 : pos m x = pos m y) : x = y := by
  have hx := Nat.div_add_mod x.val m
  have hy := Nat.div_add_mod y.val m
  unfold blk at h1
  unfold pos at h2
  rw [h1, h2] at hx
  exact Fin.ext (hx.symm.trans hy)

/-- The vertex at position `j` of block `i`. -/
def mk (m t i j : ℕ) (hi : i < t) (hj : j < m) : Fin (m * t) :=
  ⟨m * i + j, by
    calc m * i + j < m * i + m := by omega
      _ = m * (i + 1) := by ring
      _ ≤ m * t := Nat.mul_le_mul_left m hi⟩

lemma blk_mk {m t i j : ℕ} (hi : i < t) (hj : j < m) : blk m (mk m t i j hi hj) = i := by
  have hm : 0 < m := by omega
  simp only [blk, mk]
  rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hj, add_zero]

lemma pos_mk {m t i j : ℕ} (hi : i < t) (hj : j < m) : pos m (mk m t i j hi hj) = j := by
  simp only [pos, mk]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-- The join of `t` copies of the cycle `C_m`. -/
def G (m t : ℕ) (hm : 3 ≤ m) : SimpleGraph (Fin (m * t)) where
  Adj x y := blk m x ≠ blk m y ∨ (blk m x = blk m y ∧ cyc m (pos m x) (pos m y))
  symm := ⟨fun x y h => by
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (Ne.symm h)
    · exact Or.inr ⟨h1.symm, by unfold cyc at h2 ⊢; omega⟩⟩
  loopless := ⟨fun x h => by
    rcases h with h | ⟨_, h2⟩
    · exact h rfl
    · unfold cyc at h2; omega⟩

instance (m t : ℕ) (hm : 3 ≤ m) : DecidableRel (G m t hm).Adj := fun x y =>
  decidable_of_iff (blk m x ≠ blk m y ∨ (blk m x = blk m y ∧ cyc m (pos m x) (pos m y))) Iff.rfl

lemma adj_iff {m t : ℕ} {hm : 3 ≤ m} {x y : Fin (m * t)} :
    (G m t hm).Adj x y ↔ blk m x ≠ blk m y ∨ (blk m x = blk m y ∧ cyc m (pos m x) (pos m y)) :=
  Iff.rfl

lemma adj_mk {m t : ℕ} {hm : 3 ≤ m} {i p q : ℕ} (hi : i < t) (hp : p < m) (hq : q < m)
    (h : cyc m p q) : (G m t hm).Adj (mk m t i p hi hp) (mk m t i q hi hq) :=
  Or.inr ⟨by rw [blk_mk, blk_mk], by rw [pos_mk, pos_mk]; exact h⟩

/-! ### Local colourings of one block -/

/-- A proper 3-colouring of the odd cycle. -/
def col3 (m p : ℕ) : ℕ := if p + 1 = m then 2 else p % 2

/-- The distance along the cycle from `s` to `p`. -/
def rel (m s p : ℕ) : ℕ := if s ≤ p then p - s else p + m - s

/-- A 2-colouring of the path obtained by cutting the cycle just before `s`. -/
def brk (m s p : ℕ) : ℕ := rel m s p % 2

/-- A 3-colouring in which `u` is the only vertex of colour `2`. -/
def spc (m u p : ℕ) : ℕ := if p = u then 2 else rel m u p % 2

lemma col3_le (m p : ℕ) : col3 m p ≤ 2 := by
  unfold col3; split_ifs <;> omega

lemma col3_cyc {m p q : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) (hp : p < m) (hq : q < m) (h : cyc m p q) :
    col3 m p ≠ col3 m q := by
  unfold col3 cyc at *; split_ifs <;> omega

lemma brk_le (m s p : ℕ) : brk m s p ≤ 1 := by
  unfold brk; omega

lemma brk_cyc {m s j p q : ℕ} (hm : 3 ≤ m) (hp : p < m) (hq : q < m) (hs : s < m)
    (hjs : s = j + 1 ∨ (s = 0 ∧ j + 1 = m)) (h : cyc m p q)
    (hnot : ¬ ((p = j ∧ q = s) ∨ (p = s ∧ q = j))) : brk m s p ≠ brk m s q := by
  unfold brk rel cyc at *; split_ifs <;> omega

lemma spc_le (m u p : ℕ) : spc m u p ≤ 2 := by
  unfold spc; split_ifs <;> omega

lemma spc_two {m u p : ℕ} (h : spc m u p = 2) : p = u := by
  unfold spc at h; split_ifs at h with h1
  · exact h1
  · omega

lemma spc_cyc {m u p q : ℕ} (hm : 3 ≤ m) (hp : p < m) (hq : q < m) (hu : u < m) (h : cyc m p q) :
    spc m u p ≠ spc m u q := by
  unfold spc rel cyc at *; split_ifs <;> omega

/-! ### Global colourings -/

lemma colorable_of {V : Type*} (H : SimpleGraph V) (K : ℕ) (col : V → ℕ)
    (hb : ∀ x, col x < K) (hp : ∀ x y, H.Adj x y → col x ≠ col y) : H.Colorable K :=
  ⟨Coloring.mk (fun x => ⟨col x, hb x⟩) (fun {x y} h heq => hp x y h (congrArg Fin.val heq))⟩

/-- The standard `3t`-colouring. -/
def colStd (m : ℕ) {n : ℕ} (x : Fin n) : ℕ := 3 * blk m x + col3 m (pos m x)

lemma colStd_proper {m t : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) (x y : Fin (m * t))
    (h : (G m t hm).Adj x y) : colStd m x ≠ colStd m y := by
  have hx := pos_lt (by omega : 0 < m) x
  have hy := pos_lt (by omega : 0 < m) y
  have c1 := col3_le m (pos m x)
  have c2 := col3_le m (pos m y)
  unfold colStd
  rcases adj_iff.1 h with h | ⟨h1, h2⟩
  · omega
  · have := col3_cyc hm hodd hx hy h2
    omega

/-- A `(3t - 1)`-colouring that is proper except on the edge between positions `j` and `s` of
block `i0`. -/
def colB (m i0 s : ℕ) {n : ℕ} (x : Fin n) : ℕ :=
  if blk m x < i0 then 3 * blk m x + col3 m (pos m x)
  else if blk m x = i0 then 3 * i0 + brk m s (pos m x)
  else 3 * blk m x - 1 + col3 m (pos m x)

lemma colB_lt {m t i0 s : ℕ} (hi0 : i0 < t) (x : Fin (m * t)) : colB m i0 s x < 3 * t - 1 := by
  have := blk_lt x
  have := col3_le m (pos m x)
  have := brk_le m s (pos m x)
  unfold colB; split_ifs <;> omega

lemma colB_proper {m t i0 j s : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) (hs : s < m)
    (hjs : s = j + 1 ∨ (s = 0 ∧ j + 1 = m)) (x y : Fin (m * t)) (h : (G m t hm).Adj x y)
    (heq : colB m i0 s x = colB m i0 s y) :
    blk m x = i0 ∧ blk m y = i0 ∧
      ((pos m x = j ∧ pos m y = s) ∨ (pos m x = s ∧ pos m y = j)) := by
  have hx := pos_lt (by omega : 0 < m) x
  have hy := pos_lt (by omega : 0 < m) y
  have c1 := col3_le m (pos m x)
  have c2 := col3_le m (pos m y)
  have b1 := brk_le m s (pos m x)
  have b2 := brk_le m s (pos m y)
  rcases adj_iff.1 h with h | ⟨h1, h2⟩
  · exfalso
    unfold colB at heq
    split_ifs at heq <;> omega
  · by_cases hb : blk m x = i0
    · refine ⟨hb, h1 ▸ hb, ?_⟩
      by_contra hn
      have := brk_cyc hm hx hy hs hjs h2 hn
      unfold colB at heq
      rw [← h1] at heq
      simp only [hb, lt_irrefl, if_false, if_true] at heq
      omega
    · exfalso
      have := col3_cyc hm hodd hx hy h2
      unfold colB at heq
      rw [← h1] at heq
      split_ifs at heq <;> omega

/-- The local colours used for an edge `uw` between blocks `i1 < i2`. -/
def loc (m i1 i2 pu pw : ℕ) {n : ℕ} (x : Fin n) : ℕ :=
  if blk m x = i1 then spc m pu (pos m x)
  else if blk m x = i2 then spc m pw (pos m x)
  else col3 m (pos m x)

lemma loc_le (m i1 i2 pu pw : ℕ) {n : ℕ} (x : Fin n) : loc m i1 i2 pu pw x ≤ 2 := by
  unfold loc
  split_ifs
  · exact spc_le _ _ _
  · exact spc_le _ _ _
  · exact col3_le _ _

lemma loc_two {m i1 i2 pu pw n : ℕ} (x : Fin n) (h : loc m i1 i2 pu pw x = 2) :
    (blk m x = i1 → pos m x = pu) ∧ (blk m x = i2 → i1 ≠ i2 → pos m x = pw) := by
  unfold loc at h
  split_ifs at h with h1 h2
  · exact ⟨fun _ => spc_two h, fun h' hne => absurd (h1.symm.trans h') hne⟩
  · exact ⟨fun h' => absurd h' h1, fun _ _ => spc_two h⟩
  · exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩

lemma loc_cyc {m t i1 i2 pu pw : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) (hpu : pu < m)
    (hpw : pw < m) (x y : Fin (m * t)) (h1 : blk m x = blk m y)
    (h2 : cyc m (pos m x) (pos m y)) : loc m i1 i2 pu pw x ≠ loc m i1 i2 pu pw y := by
  have hx := pos_lt (by omega : 0 < m) x
  have hy := pos_lt (by omega : 0 < m) y
  unfold loc
  rw [← h1]
  split_ifs
  · exact spc_cyc hm hx hy hpu h2
  · exact spc_cyc hm hx hy hpw h2
  · exact col3_cyc hm hodd hx hy h2

/-- The palette for an edge between blocks `i1 < i2`: colour `2` of block `i2` is merged with
colour `2` of block `i1`. -/
def pal (i1 i2 i c : ℕ) : ℕ :=
  if i < i2 then 3 * i + c
  else if i = i2 then (if c = 2 then 3 * i1 + 2 else 3 * i2 + c)
  else 3 * i - 1 + c

lemma pal_lt {t i1 i2 i c : ℕ} (h12 : i1 < i2) (hi2 : i2 < t) (hi : i < t) (hc : c ≤ 2) :
    pal i1 i2 i c < 3 * t - 1 := by
  unfold pal; split_ifs <;> omega

lemma pal_eq {i1 i2 i i' c c' : ℕ} (h12 : i1 < i2) (hc : c ≤ 2) (hc' : c' ≤ 2)
    (h : pal i1 i2 i c = pal i1 i2 i' c') :
    (i = i' ∧ c = c') ∨ (i = i1 ∧ c = 2 ∧ i' = i2 ∧ c' = 2) ∨
      (i = i2 ∧ c = 2 ∧ i' = i1 ∧ c' = 2) := by
  unfold pal at h; split_ifs at h <;> omega

/-- A `(3t - 1)`-colouring that is proper except on the edge `uw`. -/
def colS (m i1 i2 pu pw : ℕ) {n : ℕ} (x : Fin n) : ℕ :=
  pal i1 i2 (blk m x) (loc m i1 i2 pu pw x)

lemma colS_lt {m t i1 i2 pu pw : ℕ} (h12 : i1 < i2) (hi2 : i2 < t) (x : Fin (m * t)) :
    colS m i1 i2 pu pw x < 3 * t - 1 :=
  pal_lt h12 hi2 (blk_lt x) (loc_le m i1 i2 pu pw x)

lemma colS_proper {m t i1 i2 pu pw : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) (h12 : i1 < i2)
    (hpu : pu < m) (hpw : pw < m) (x y : Fin (m * t)) (h : (G m t hm).Adj x y)
    (heq : colS m i1 i2 pu pw x = colS m i1 i2 pu pw y) :
    (blk m x = i1 ∧ pos m x = pu ∧ blk m y = i2 ∧ pos m y = pw) ∨
      (blk m x = i2 ∧ pos m x = pw ∧ blk m y = i1 ∧ pos m y = pu) := by
  have hne : i1 ≠ i2 := by omega
  rcases pal_eq h12 (loc_le m i1 i2 pu pw x) (loc_le m i1 i2 pu pw y) heq with
    ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exfalso
    rcases adj_iff.1 h with h' | ⟨_, h''⟩
    · exact h' h1
    · exact loc_cyc hm hodd hpu hpw x y h1 h'' h2
  · left
    exact ⟨h1, (loc_two x h2).1 h1, h3, (loc_two y h4).2 h3 hne⟩
  · right
    exact ⟨h1, (loc_two x h2).2 h1 hne, h3, (loc_two y h4).1 h3⟩

/-! ### The chromatic number -/

lemma no_coloring {m t : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) (ht : 1 ≤ t)
    (c : Fin (m * t) → ℕ) (hb : ∀ x, c x < 3 * t - 1)
    (hp : ∀ x y, (G m t hm).Adj x y → c x ≠ c y) : False := by
  have hm0 : 0 < m := by omega
  let S : ℕ → Finset ℕ := fun i => (univ.filter (fun x : Fin (m * t) => blk m x = i)).image c
  have hS3 : ∀ i, i < t → 3 ≤ (S i).card := by
    intro i hi
    by_contra hlt
    push Not at hlt
    have h0 : 0 < m := hm0
    have h1 : 1 < m := by omega
    set a := c (mk m t i 0 hi h0) with ha
    set b := c (mk m t i 1 hi h1) with hb'
    have hab : a ≠ b := hp _ _ (adj_mk hi h0 h1 (Or.inl rfl))
    have hmem : ∀ j (hj : j < m), c (mk m t i j hi hj) ∈ S i := by
      intro j hj
      exact mem_image.2 ⟨mk m t i j hi hj, by simp [blk_mk], rfl⟩
    have hsub : ({a, b} : Finset ℕ) ⊆ S i := by
      intro z hz
      rw [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hmem 0 h0
      · exact hmem 1 h1
    have hEq : ({a, b} : Finset ℕ) = S i :=
      eq_of_subset_of_card_le hsub (by rw [card_pair hab]; omega)
    have hall : ∀ j (hj : j < m), c (mk m t i j hi hj) = a ∨ c (mk m t i j hi hj) = b := by
      intro j hj
      have := hmem j hj
      rw [← hEq, mem_insert, mem_singleton] at this
      exact this
    have claim : ∀ j (hj : j < m), c (mk m t i j hi hj) = if j % 2 = 0 then a else b := by
      intro j
      induction j with
      | zero => intro hj; simp [ha]
      | succ j ih =>
        intro hj1
        have hj : j < m := by omega
        have hne := hp _ _ (adj_mk hi hj hj1 (Or.inl rfl))
        rw [ih hj] at hne
        by_cases hj2 : j % 2 = 0
        · have h' : ¬ ((j + 1) % 2 = 0) := by omega
          simp only [hj2, h', if_true, if_false] at hne ⊢
          rcases hall (j + 1) hj1 with h1' | h1'
          · exact absurd h1'.symm hne
          · exact h1'
        · have h' : (j + 1) % 2 = 0 := by omega
          simp only [hj2, h', if_true, if_false] at hne ⊢
          rcases hall (j + 1) hj1 with h1' | h1'
          · exact h1'
          · exact absurd h1'.symm hne
    have hlast : m - 1 < m := by omega
    have e1 := claim (m - 1) hlast
    have heven : (m - 1) % 2 = 0 := by omega
    rw [if_pos heven] at e1
    have hadj := hp _ _ (adj_mk hi hlast h0 (Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩))))
    exact hadj (e1.trans ha)
  have hdisj : ((range t : Finset ℕ) : Set ℕ).PairwiseDisjoint S := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hz1
    obtain ⟨y, hy, hxy⟩ := mem_image.1 hz2
    rw [mem_filter] at hx hy
    exact hp x y (Or.inl (by rw [hx.2, hy.2]; exact hij)) hxy.symm
  have hU : (range t).biUnion S ⊆ range (3 * t - 1) := by
    intro z hz
    obtain ⟨i, _, hz⟩ := mem_biUnion.1 hz
    obtain ⟨x, _, rfl⟩ := mem_image.1 hz
    exact mem_range.2 (hb x)
  have hcard := card_le_card hU
  rw [card_biUnion hdisj, card_range] at hcard
  have hsum : (range t).card • 3 ≤ ∑ i ∈ range t, (S i).card :=
    card_nsmul_le_sum _ _ _ (fun i hi => hS3 i (mem_range.1 hi))
  rw [card_range, smul_eq_mul] at hsum
  omega

lemma not_colorable {m t : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) (ht : 1 ≤ t) :
    ¬ (G m t hm).Colorable (3 * t - 1) := by
  rintro ⟨C⟩
  exact no_coloring hm hodd ht (fun x => (C x).val) (fun x => (C x).isLt)
    (fun x y h heq => C.valid h (Fin.ext heq))

lemma le_chi {m t : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) (ht : 1 ≤ t) :
    ((3 * t : ℕ) : ℕ∞) ≤ (G m t hm).chromaticNumber := by
  rw [le_chromaticNumber_iff_not_colorable (by omega)]
  exact not_colorable hm hodd ht

lemma chi_eq {m t : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) (ht : 1 ≤ t) :
    (G m t hm).chromaticNumber = ((3 * t : ℕ) : ℕ∞) := by
  refine le_antisymm ?_ (le_chi hm hodd ht)
  apply Colorable.chromaticNumber_le
  refine colorable_of _ _ (colStd m) (fun x => ?_) (colStd_proper hm hodd)
  have := blk_lt x
  have := col3_le m (pos m x)
  unfold colStd
  omega

lemma lt_aux {t : ℕ} (ht : 1 ≤ t) {a b : ℕ∞} (ha : a ≤ ((3 * t - 1 : ℕ) : ℕ∞))
    (hb : ((3 * t : ℕ) : ℕ∞) ≤ b) : a < b := by
  refine lt_of_le_of_lt ha (lt_of_lt_of_le ?_ hb)
  exact_mod_cast (by omega : 3 * t - 1 < 3 * t)

/-! ### Criticality -/

/-- The position after `p` on the cycle. -/
def nxt (m p : ℕ) : ℕ := if p + 1 = m then 0 else p + 1

lemma vertex_critical {m t : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) (ht : 1 ≤ t)
    (v : Fin (m * t)) : (⊤ : (G m t hm).Subgraph).IsCriticalVertex v := by
  have hm0 : 0 < m := by omega
  have hv := pos_lt hm0 v
  unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts
  apply lt_aux ht
  · apply Colorable.chromaticNumber_le
    refine colorable_of _ _ (fun a => colB m (blk m v) (nxt m (pos m v)) a.val)
      (fun a => colB_lt (blk_lt v) a.val) ?_
    intro a b hab heq
    rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at hab
    obtain ⟨_, ha, _, hb, hab⟩ := hab
    rw [Subgraph.top_adj] at hab
    have hs : nxt m (pos m v) < m := by unfold nxt; split_ifs <;> omega
    have hjs : nxt m (pos m v) = pos m v + 1 ∨ (nxt m (pos m v) = 0 ∧ pos m v + 1 = m) := by
      unfold nxt; split_ifs <;> omega
    obtain ⟨h1, h2, h3⟩ := colB_proper hm hodd hs hjs a.val b.val hab heq
    rcases h3 with ⟨h3, _⟩ | ⟨_, h3⟩
    · exact ha (Set.mem_singleton_iff.2 (ext' _ _ h1 h3))
    · exact hb (Set.mem_singleton_iff.2 (ext' _ _ h2 h3))
  · rw [le_chromaticNumber_iff_not_colorable (by omega)]
    rintro ⟨C⟩
    exact no_coloring hm hodd ht (fun x => (C ⟨x, by simp⟩).val) (fun x => (C _).isLt)
      (fun x y h heq => C.valid (by simpa using h) (Fin.ext heq))

lemma edge_critical {m t : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) (ht : 1 ≤ t)
    (e : Sym2 (Fin (m * t))) (he : e ∈ (G m t hm).edgeSet) : (G m t hm).IsCriticalEdge e := by
  have hm0 : 0 < m := by omega
  unfold IsCriticalEdge IsCriticalEdges
  refine lt_aux ht ?_ (le_chi hm hodd ht)
  apply Colorable.chromaticNumber_le
  revert he
  refine Sym2.ind (fun x y => ?_) e
  intro hxy
  rw [mem_edgeSet] at hxy
  have hx := pos_lt hm0 x
  have hy := pos_lt hm0 y
  rcases adj_iff.1 hxy with hb | ⟨hb, hc⟩
  · -- an edge between two blocks
    rcases Nat.lt_or_gt_of_ne hb with hlt | hlt
    · refine colorable_of _ _ (colS m (blk m x) (blk m y) (pos m x) (pos m y))
        (colS_lt hlt (blk_lt y)) ?_
      intro a b hab heq
      rw [deleteEdges_adj] at hab
      obtain ⟨hab, hne⟩ := hab
      apply hne
      rcases colS_proper hm hodd hlt hx hy a b hab heq with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · rw [ext' a x h1 h2, ext' b y h3 h4]; exact Set.mem_singleton _
      · rw [ext' a y h1 h2, ext' b x h3 h4, Sym2.eq_swap]; exact Set.mem_singleton _
    · refine colorable_of _ _ (colS m (blk m y) (blk m x) (pos m y) (pos m x))
        (colS_lt hlt (blk_lt x)) ?_
      intro a b hab heq
      rw [deleteEdges_adj] at hab
      obtain ⟨hab, hne⟩ := hab
      apply hne
      rcases colS_proper hm hodd hlt hy hx a b hab heq with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · rw [ext' a y h1 h2, ext' b x h3 h4, Sym2.eq_swap]; exact Set.mem_singleton _
      · rw [ext' a x h1 h2, ext' b y h3 h4]; exact Set.mem_singleton _
  · -- an edge of a cycle
    by_cases hdir : pos m y = nxt m (pos m x)
    · have hjs : pos m y = pos m x + 1 ∨ (pos m y = 0 ∧ pos m x + 1 = m) := by
        unfold nxt at hdir; split_ifs at hdir <;> omega
      refine colorable_of _ _ (colB m (blk m x) (pos m y)) (colB_lt (blk_lt x)) ?_
      intro a b hab heq
      rw [deleteEdges_adj] at hab
      obtain ⟨hab, hne⟩ := hab
      apply hne
      obtain ⟨h1, h2, h3⟩ := colB_proper hm hodd hy hjs a b hab heq
      rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [ext' a x h1 h3, ext' b y (h2.trans hb) h4]; exact Set.mem_singleton _
      · rw [ext' a y (h1.trans hb) h3, ext' b x h2 h4, Sym2.eq_swap]; exact Set.mem_singleton _
    · have hjs : pos m x = pos m y + 1 ∨ (pos m x = 0 ∧ pos m y + 1 = m) := by
        unfold nxt at hdir
        unfold cyc at hc
        split_ifs at hdir <;> omega
      refine colorable_of _ _ (colB m (blk m x) (pos m x)) (colB_lt (blk_lt x)) ?_
      intro a b hab heq
      rw [deleteEdges_adj] at hab
      obtain ⟨hab, hne⟩ := hab
      apply hne
      obtain ⟨h1, h2, h3⟩ := colB_proper hm hodd hx hjs a b hab heq
      rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [ext' a y (h1.trans hb) h3, ext' b x h2 h4, Sym2.eq_swap]; exact Set.mem_singleton _
      · rw [ext' a x h1 h3, ext' b y (h2.trans hb) h4]; exact Set.mem_singleton _

/-! ### Counting edges -/

lemma card_block {m t : ℕ} (hm0 : 0 < m) (i : ℕ) (hi : i < t) :
    (univ.filter (fun y : Fin (m * t) => blk m y = i)).card = m := by
  refine (card_bij (t := range m) (fun y _ => pos m y) (fun y _ => mem_range.2 (pos_lt hm0 y))
    ?_ ?_).trans (card_range m)
  · intro a ha b hb h
    rw [mem_filter] at ha hb
    exact ext' a b (ha.2.trans hb.2.symm) h
  · intro j hj
    rw [mem_range] at hj
    exact ⟨mk m t i j hi hj, by simp [blk_mk], pos_mk hi hj⟩

lemma degree_eq {m t : ℕ} (hm : 3 ≤ m) (x : Fin (m * t)) :
    (G m t hm).degree x = 2 + (m * t - m) := by
  have hm0 : 0 < m := by omega
  have hx := pos_lt hm0 x
  have hbx := blk_lt x
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  rw [← card_filter_add_card_filter_not (s := univ.filter (fun y => (G m t hm).Adj x y))
    (fun y => blk m y = blk m x)]
  congr 1
  · -- neighbours in the same block
    have : (univ.filter (fun y => (G m t hm).Adj x y)).filter (fun y => blk m y = blk m x) =
        univ.filter (fun y => blk m y = blk m x ∧ cyc m (pos m x) (pos m y)) := by
      ext y
      simp only [mem_filter, mem_univ, true_and, adj_iff]
      constructor
      · rintro ⟨h | ⟨_, h⟩, h2⟩
        · exact absurd h2.symm h
        · exact ⟨h2, h⟩
      · rintro ⟨h1, h2⟩
        exact ⟨Or.inr ⟨h1.symm, h2⟩, h1⟩
    rw [this]
    have h2 : ((range m).filter (fun q => cyc m (pos m x) q)).card = 2 := by
      have : (range m).filter (fun q => cyc m (pos m x) q) =
          {nxt m (pos m x), if pos m x = 0 then m - 1 else pos m x - 1} := by
        ext q
        simp only [mem_filter, mem_range, mem_insert, mem_singleton]
        unfold cyc nxt
        split_ifs <;> constructor <;> intro h <;> omega
      rw [this, card_pair (by unfold nxt; split_ifs <;> omega)]
    rw [← h2]
    refine card_bij (fun y _ => pos m y) ?_ ?_ ?_
    · intro y hy
      rw [mem_filter] at hy ⊢
      exact ⟨mem_range.2 (pos_lt hm0 y), hy.2.2⟩
    · intro a ha b hb h
      rw [mem_filter] at ha hb
      exact ext' a b (ha.2.1.trans hb.2.1.symm) h
    · intro q hq
      rw [mem_filter, mem_range] at hq
      refine ⟨mk m t (blk m x) q hbx hq.1, ?_, pos_mk hbx hq.1⟩
      rw [mem_filter, blk_mk, pos_mk]
      exact ⟨mem_univ _, rfl, hq.2⟩
  · -- neighbours in other blocks
    have : (univ.filter (fun y => (G m t hm).Adj x y)).filter (fun y => ¬ blk m y = blk m x) =
        univ.filter (fun y : Fin (m * t) => ¬ blk m y = blk m x) := by
      ext y
      simp only [mem_filter, mem_univ, true_and, adj_iff]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨Or.inl (Ne.symm h), h⟩
    rw [this]
    have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin (m * t))))
      (fun y => blk m y = blk m x)
    rw [card_block hm0 _ hbx, card_univ, Fintype.card_fin] at hsplit
    omega

lemma card_edges {m t : ℕ} (hm : 3 ≤ m) :
    2 * (G m t hm).edgeSet.ncard = (m * t) * (2 + (m * t - m)) := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset, ← sum_degrees_eq_twice_card_edges]
  simp only [degree_eq hm, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

end OMA.E917

open OMA.E917 in
theorem OMA.solution : type_of% @Erdos917.erdos_917.variants.erdos_three_dvd := by
  intro k hk h3 m hm hm3
  have hodd : m % 2 = 1 := Nat.odd_iff.1 hm
  set t := k / 3 with htdef
  have ht : 1 ≤ t := by omega
  have hk3 : k = 3 * t := (Nat.mul_div_cancel' h3).symm
  have hcrit : Erdos917.IsKCritical (G m t hm3) k := by
    refine ⟨⟨?_, vertex_critical hm3 hodd ht⟩, fun e he => edge_critical hm3 hodd ht e he⟩
    rw [chi_eq hm3 hodd ht, hk3]
  have hle := Erdos917.edgeSet_ncard_le_f hcrit
  have hE := card_edges (t := t) hm3
  have hmt : m ≤ m * t := Nat.le_mul_of_pos_right m ht
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmt
  have hE2 : 2 * (G m t hm3).edgeSet.ncard = (m + d) * (2 + d) := by
    rw [hE, hd, Nat.add_sub_cancel_left]
  have hE2R : (2 : ℝ) * ((G m t hm3).edgeSet.ncard : ℝ) = ((m : ℝ) + d) * (2 + d) := by
    exact_mod_cast hE2
  have hdR : (m : ℝ) * t = m + d := by exact_mod_cast hd
  have hval : Erdos917.conjecturedValue k (m * t) + ((m * t : ℕ) : ℝ) =
      ((G m t hm3).edgeSet.ncard : ℝ) := by
    unfold Erdos917.conjecturedValue
    rw [← htdef]
    have htr0 : (t : ℝ) ≠ 0 := by
      have : (0 : ℝ) < t := by exact_mod_cast ht
      exact this.ne'
    have key : (1 : ℝ) / 2 * (1 - 1 / (t : ℝ)) * ((m : ℝ) * t) ^ 2 =
        ((m : ℝ) * t) * ((m : ℝ) * t - m) / 2 := by
      first | (field_simp; ring) | field_simp
    push_cast
    rw [key, hdR]
    linear_combination (-1 / 2 : ℝ) * hE2R
  rw [hval]
  exact_mod_cast hle
