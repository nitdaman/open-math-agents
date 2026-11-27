import FormalConjectures.ErdosProblems.«1034»
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
A cyclic version of Ma and Tang's construction for the K₄-free variant of Erdős 1034.
See https://www.erdosproblems.com/forum/thread/1034.
-/

open Filter Finset SimpleGraph
open scoped BigOperators

namespace TriangleK4Free

private abbrev Vertex (a m : ℕ) := Fin a ⊕ (Fin m ⊕ Fin m)

private def left {a m : ℕ} (x : Fin m) : Vertex a m := Sum.inr (Sum.inl x)

private def right {a m : ℕ} (y : Fin m) : Vertex a m := Sum.inr (Sum.inr y)

/-- Join an independent set to the union of the first d cyclic matchings in K_{m,m}. -/
private def graph (a m d : ℕ) : SimpleGraph (Vertex a m) where
  Adj u v := match u, v with
    | .inl _, .inr _ | .inr _, .inl _ => True
    | .inr (.inl x), .inr (.inr y) => (y - x).val < d
    | .inr (.inr y), .inr (.inl x) => (y - x).val < d
    | _, _ => False
  symm := ⟨by rintro (u | (u | u)) (v | (v | v)) <;> exact id⟩
  loopless := ⟨by rintro (u | (u | u)) <;> exact id⟩

private instance (a m d : ℕ) : DecidableRel (graph a m d).Adj := by
  rintro (u | (u | u)) (v | (v | v)) <;> dsimp [graph] <;> infer_instance

private def centerEmbedding (a m : ℕ) : Fin a ↪ Vertex a m :=
  ⟨Sum.inl, Sum.inl_injective⟩

private def bodyEmbedding (a m : ℕ) : (Fin m ⊕ Fin m) ↪ Vertex a m :=
  ⟨Sum.inr, Sum.inr_injective⟩

private def center (a m : ℕ) : Finset (Vertex a m) := univ.map (centerEmbedding a m)

private def body (a m : ℕ) : Finset (Vertex a m) := univ.map (bodyEmbedding a m)

private lemma mem_center {a m : ℕ} {v : Vertex a m} :
    v ∈ center a m ↔ ∃ x : Fin a, v = Sum.inl x := by
  constructor
  · intro hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.1 hv
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact Finset.mem_map.2 ⟨x, Finset.mem_univ _, rfl⟩

private lemma mem_body {a m : ℕ} {v : Vertex a m} :
    v ∈ body a m ↔ ∃ x : Fin m ⊕ Fin m, v = Sum.inr x := by
  constructor
  · intro hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.1 hv
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact Finset.mem_map.2 ⟨x, Finset.mem_univ _, rfl⟩

private def leftEmbedding (a m d : ℕ) [NeZero m] (hd : d ≤ m) (y : Fin m) :
    Fin d ↪ Vertex a m :=
  ⟨fun j => left (y - j.castLE hd), by
    intro i j h
    have h' : y - i.castLE hd = y - j.castLE hd := Sum.inl.inj (Sum.inr.inj h)
    have h'' : i.castLE hd = j.castLE hd := by
      simpa using congrArg (fun z : Fin m => y - z) h'
    exact (Fin.castLEEmb hd).injective h''⟩

private def rightEmbedding (a m d : ℕ) [NeZero m] (hd : d ≤ m) (x : Fin m) :
    Fin d ↪ Vertex a m :=
  ⟨fun j => right (x + j.castLE hd), by
    intro i j h
    have h' : x + i.castLE hd = x + j.castLE hd := Sum.inr.inj (Sum.inr.inj h)
    exact (Fin.castLEEmb hd).injective (add_left_cancel h')⟩

private def leftChoices (a m d : ℕ) [NeZero m] (hd : d ≤ m) (y : Fin m) :
    Finset (Vertex a m) :=
  univ.map (leftEmbedding a m d hd y)

private def rightChoices (a m d : ℕ) [NeZero m] (hd : d ≤ m) (x : Fin m) :
    Finset (Vertex a m) :=
  univ.map (rightEmbedding a m d hd x)

private lemma mem_leftChoices {a m d : ℕ} [NeZero m] {hd : d ≤ m} {y : Fin m}
    {v : Vertex a m} :
    v ∈ leftChoices a m d hd y ↔ ∃ x : Fin m, v = left x ∧ (y - x).val < d := by
  constructor
  · intro hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hv
    refine ⟨y - j.castLE hd, rfl, ?_⟩
    simp
  · rintro ⟨x, rfl, hx⟩
    refine Finset.mem_map.2 ⟨⟨(y - x).val, hx⟩, Finset.mem_univ _, ?_⟩
    change left (y - (⟨(y - x).val, hx⟩ : Fin d).castLE hd) = left x
    rw [show (⟨(y - x).val, hx⟩ : Fin d).castLE hd = y - x from Fin.ext rfl, sub_sub_cancel]

private lemma mem_rightChoices {a m d : ℕ} [NeZero m] {hd : d ≤ m} {x : Fin m}
    {v : Vertex a m} :
    v ∈ rightChoices a m d hd x ↔ ∃ y : Fin m, v = right y ∧ (y - x).val < d := by
  constructor
  · intro hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hv
    refine ⟨x + j.castLE hd, rfl, ?_⟩
    simp [add_comm x (j.castLE hd)]
  · rintro ⟨y, rfl, hy⟩
    refine Finset.mem_map.2 ⟨⟨(y - x).val, hy⟩, Finset.mem_univ _, ?_⟩
    change right (x + (⟨(y - x).val, hy⟩ : Fin d).castLE hd) = right y
    rw [show (⟨(y - x).val, hy⟩ : Fin d).castLE hd = y - x from Fin.ext rfl, add_sub_cancel]

private lemma center_right_disjoint (a m d : ℕ) [NeZero m] (hd : d ≤ m) (x : Fin m) :
    Disjoint (center a m) (rightChoices a m d hd x) := by
  refine Finset.disjoint_left.2 ?_
  intro v hC hR
  obtain ⟨c, rfl⟩ := mem_center.1 hC
  obtain ⟨y, hy, _⟩ := mem_rightChoices.1 hR
  cases hy

private lemma center_left_disjoint (a m d : ℕ) [NeZero m] (hd : d ≤ m) (y : Fin m) :
    Disjoint (center a m) (leftChoices a m d hd y) := by
  refine Finset.disjoint_left.2 ?_
  intro v hC hL
  obtain ⟨c, rfl⟩ := mem_center.1 hC
  obtain ⟨x, hx, _⟩ := mem_leftChoices.1 hL
  cases hx

private lemma center_degree (a m d : ℕ) (x : Fin a) :
    (graph a m d).degree (Sum.inl x) = m + m := by
  have h : (graph a m d).neighborFinset (Sum.inl x) = body a m := by
    ext v
    rw [SimpleGraph.mem_neighborFinset, mem_body]
    rcases v with v | v
    · change False ↔ _
      simp
    · cases v <;> change True ↔ _ <;> simp
  simp [SimpleGraph.degree, h, body]

private lemma left_degree (a m d : ℕ) [NeZero m] (hd : d ≤ m) (x : Fin m) :
    (graph a m d).degree (left x) = a + d := by
  have h : (graph a m d).neighborFinset (left x) = center a m ∪ rightChoices a m d hd x := by
    ext v
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_union, mem_center, mem_rightChoices]
    rcases v with v | (v | v)
    · change True ↔ _
      simp
    · change False ↔ _
      simp [right]
    · change (v - x).val < d ↔ _
      simp [right]
  rw [SimpleGraph.degree, h, Finset.card_union_of_disjoint (center_right_disjoint a m d hd x)]
  simp [center, rightChoices]

private lemma right_degree (a m d : ℕ) [NeZero m] (hd : d ≤ m) (y : Fin m) :
    (graph a m d).degree (right y) = a + d := by
  have h : (graph a m d).neighborFinset (right y) = center a m ∪ leftChoices a m d hd y := by
    ext v
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_union, mem_center, mem_leftChoices]
    rcases v with v | (v | v)
    · change True ↔ _
      simp
    · change (y - v).val < d ↔ _
      simp [left]
    · change False ↔ _
      simp [left]
  rw [SimpleGraph.degree, h, Finset.card_union_of_disjoint (center_left_disjoint a m d hd y)]
  simp [center, leftChoices]

private lemma edge_card (a m d : ℕ) [NeZero m] (hd : d ≤ m) :
    (graph a m d).edgeSet.ncard = m * (2 * a + d) := by
  have h := (graph a m d).sum_degrees_eq_twice_card_edges
  simp only [Vertex, Fintype.sum_sum_type] at h
  have hleft (x : Fin m) : (graph a m d).degree (Sum.inr (Sum.inl x)) = a + d :=
    left_degree a m d hd x
  have hright (y : Fin m) : (graph a m d).degree (Sum.inr (Sum.inr y)) = a + d :=
    right_degree a m d hd y
  simp only [center_degree, hleft, hright, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  rw [Set.ncard_eq_toFinset_card']
  change (graph a m d).edgeFinset.card = _
  have heq : a * (m + m) + (m * (a + d) + m * (a + d)) = 2 * (m * (2 * a + d)) := by ring
  change a * (m + m) + (m * (a + d) + m * (a + d)) = 2 * (graph a m d).edgeFinset.card at h
  rw [heq] at h
  omega

private def part {a m : ℕ} : Vertex a m → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

private lemma adj_part_ne {a m d : ℕ} {u v : Vertex a m} (h : (graph a m d).Adj u v) :
    part u ≠ part v := by
  rcases u with u | (u | u) <;> rcases v with v | (v | v) <;>
    first | exact False.elim h | (dsimp [part]; decide)

private lemma part_injOn {a m d k : ℕ} {T : Finset (Vertex a m)}
    (hT : (graph a m d).IsNClique k T) :
    Set.InjOn part (T : Set (Vertex a m)) := by
  intro u hu v hv hp
  by_contra huv
  exact adj_part_ne (hT.isClique hu hv huv) hp

private lemma clique_free (a m d : ℕ) : (graph a m d).CliqueFree 4 := by
  intro T hT
  have h : (T.image part).card ≤ 3 := by
    simpa using (Finset.card_le_univ (T.image part))
  rw [Finset.card_image_of_injOn (part_injOn hT), hT.card_eq] at h
  omega

private lemma triangle_parts {a m d : ℕ} {T : Finset (Vertex a m)}
    (hT : (graph a m d).IsNClique 3 T) :
    ∃ c : Fin a, ∃ x y : Fin m, T = {Sum.inl c, left x, right y} := by
  have heq : T.image part = univ := by
    refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
    simp [Finset.card_image_of_injOn (part_injOn hT), hT.card_eq]
  have hvertex (i : Fin 3) : ∃ v ∈ T, part v = i := by
    exact Finset.mem_image.1 (heq.symm ▸ Finset.mem_univ i)
  obtain ⟨c, hc, hpc⟩ := hvertex 0
  obtain ⟨x, hx, hpx⟩ := hvertex 1
  obtain ⟨y, hy, hpy⟩ := hvertex 2
  have hC : ∃ c' : Fin a, c = Sum.inl c' := by
    rcases c with c | (c | c)
    · exact ⟨c, rfl⟩
    · exact False.elim ((by decide : (1 : Fin 3) ≠ 0) hpc)
    · exact False.elim ((by decide : (2 : Fin 3) ≠ 0) hpc)
  have hL : ∃ x' : Fin m, x = left x' := by
    rcases x with x | (x | x)
    · exact False.elim ((by decide : (0 : Fin 3) ≠ 1) hpx)
    · exact ⟨x, rfl⟩
    · exact False.elim ((by decide : (2 : Fin 3) ≠ 1) hpx)
  have hR : ∃ y' : Fin m, y = right y' := by
    rcases y with y | (y | y)
    · exact False.elim ((by decide : (0 : Fin 3) ≠ 2) hpy)
    · exact False.elim ((by decide : (1 : Fin 3) ≠ 2) hpy)
    · exact ⟨y, rfl⟩
  obtain ⟨c', rfl⟩ := hC
  obtain ⟨x', rfl⟩ := hL
  obtain ⟨y', rfl⟩ := hR
  refine ⟨c', x', y', (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  · rw [hT.card_eq]
    have h1 : (Sum.inl c' : Vertex a m) ∉ ({left x', right y'} : Finset (Vertex a m)) := by
      simp [left, right]
    have h2 : (left x' : Vertex a m) ∉ ({right y'} : Finset (Vertex a m)) := by simp [left, right]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]

private lemma triangle_bound {a m d : ℕ} [NeZero m] (hd : d ≤ m)
    {T Y : Finset (Vertex a m)} (hT : (graph a m d).IsNClique 3 T)
    (hY : Erdos1034.JoinedToTwo (graph a m d) T Y) :
    Y.card ≤ a + 2 * d := by
  obtain ⟨c, x, y, rfl⟩ := triangle_parts hT
  let S := center a m ∪ (leftChoices a m d hd y ∪ rightChoices a m d hd x)
  have hsub : Y ⊆ S := by
    intro v hv
    rcases v with v | (v | v)
    · exact Finset.mem_union_left _ (mem_center.2 ⟨v, rfl⟩)
    · have h : (y - v).val < d := by
        by_contra hbad
        obtain ⟨u, hu, w, hw, huw, hvu, hvw⟩ := hY (left v) hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
        have hone {z : Vertex a m}
            (hz : z = Sum.inl c ∨ z = left x ∨ z = right y)
            (hvz : (graph a m d).Adj (left v) z) : z = Sum.inl c := by
          rcases hz with rfl | rfl | rfl
          · rfl
          · exact False.elim hvz
          · exact False.elim (hbad hvz)
        exact huw ((hone hu hvu).trans (hone hw hvw).symm)
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (mem_leftChoices.2 ⟨v, rfl, h⟩))
    · have h : (v - x).val < d := by
        by_contra hbad
        obtain ⟨u, hu, w, hw, huw, hvu, hvw⟩ := hY (right v) hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
        have hone {z : Vertex a m}
            (hz : z = Sum.inl c ∨ z = left x ∨ z = right y)
            (hvz : (graph a m d).Adj (right v) z) : z = Sum.inl c := by
          rcases hz with rfl | rfl | rfl
          · rfl
          · exact False.elim (hbad hvz)
          · exact False.elim hvz
        exact huw ((hone hu hvu).trans (hone hw hvw).symm)
      exact Finset.mem_union_right _ (Finset.mem_union_right _ (mem_rightChoices.2 ⟨v, rfl, h⟩))
  calc
    Y.card ≤ S.card := Finset.card_le_card hsub
    _ ≤ (center a m).card + ((leftChoices a m d hd y).card + (rightChoices a m d hd x).card) :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)
    _ = a + 2 * d := by simp [center, leftChoices, rightChoices, two_mul]


/-- The two equal sides have limiting ratio √3/6. A positive degree slack absorbs rounding. -/
private lemma feasible (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ a m d : ℕ, 0 < m ∧ d ≤ m ∧ a + 2 * m = n ∧
      (n : ℝ) ^ 2 / 4 < (m : ℝ) * (2 * (a : ℝ) + (d : ℝ)) ∧
      (a : ℝ) + 2 * (d : ℝ) ≤ (2 * Real.sqrt 3 - 3 + ε) * (n : ℝ) := by
  let s := Real.sqrt 3
  let p := s / 6
  let q := 7 * s / 6 - 2
  let δ := min (ε / 4) (1 / 100)
  have hslo : (12 : ℝ) / 7 < s := by
    dsimp [s]
    exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hshi : s ≤ (7 : ℝ) / 4 := by
    dsimp [s]
    rw [Real.sqrt_le_iff]
    norm_num
  have hsq : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : (1 : ℝ) / 4 ≤ p := by dsimp [p]; linarith
  have hp0 : 0 < p := by linarith
  have hp2 : 2 * p ≤ 1 := by dsimp [p]; linarith
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδmax : δ ≤ 1 / 100 := min_le_right _ _
  have hqp : q + δ ≤ p := by dsimp [p, q]; linarith
  have hcrit : p * (s / 2) = 1 / 4 := by
    dsimp [p]
    nlinarith only [hsq]
  have hcoef : p + (s / 2 + δ) < 2 := by dsimp [p]; linarith
  obtain ⟨N, hN⟩ := exists_nat_ge ((8 : ℝ) / δ)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h8 : (8 : ℝ) ≤ δ * (n : ℝ) := by
    have hnR : (8 : ℝ) / δ ≤ n := hN.trans (by exact_mod_cast hn)
    simpa [mul_comm] using (div_le_iff₀ hδ).1 hnR
  have h800 : (800 : ℝ) ≤ n := by
    have h := mul_le_mul_of_nonneg_right hδmax hn0
    linarith
  have hnpos : (0 : ℝ) < n := by linarith
  let m := Nat.floor (p * (n : ℝ))
  let d := Nat.floor ((q + δ) * (n : ℝ))
  let a := n - 2 * m
  have hmhi : (m : ℝ) ≤ p * (n : ℝ) := Nat.floor_le (mul_nonneg hp0.le hn0)
  have hmlo : p * (n : ℝ) - 1 < (m : ℝ) := by
    linarith only [Nat.lt_floor_add_one (p * (n : ℝ))]
  have hdhi : (d : ℝ) ≤ (q + δ) * (n : ℝ) :=
    Nat.floor_le (mul_nonneg (add_nonneg hq0.le hδ.le) hn0)
  have hdlo : (q + δ) * (n : ℝ) - 1 < (d : ℝ) := by
    linarith only [Nat.lt_floor_add_one ((q + δ) * (n : ℝ))]
  have hmLo0 : 0 ≤ p * (n : ℝ) - 1 := by
    have h := mul_le_mul_of_nonneg_right hp hn0
    linarith
  have hmpos : 0 < m := by
    exact_mod_cast (hmLo0.trans_lt hmlo)
  have hdm : d ≤ m := Nat.floor_mono (mul_le_mul_of_nonneg_right hqp hn0)
  have h2mR : (2 : ℝ) * (m : ℝ) ≤ n := by
    have h := mul_le_mul_of_nonneg_right hp2 hn0
    linarith only [h, hmhi]
  have h2m : 2 * m ≤ n := by exact_mod_cast h2mR
  have ha : (a : ℝ) = (n : ℝ) - 2 * (m : ℝ) := by
    dsimp [a]
    rw [Nat.cast_sub h2m, Nat.cast_mul, Nat.cast_ofNat]
  refine ⟨a, m, d, hmpos, hdm, by dsimp [a]; omega, ?_, ?_⟩
  · have hfactor : (s / 2 + δ) * (n : ℝ) - 1 ≤ 2 * (a : ℝ) + (d : ℝ) := calc
      (s / 2 + δ) * (n : ℝ) - 1 = (2 - 4 * p + q + δ) * (n : ℝ) - 1 := by
        dsimp [p, q]
        ring
      _ ≤ _ := by linarith only [ha, hmhi, hdlo]
    have hfactor0 : 0 ≤ (s / 2 + δ) * (n : ℝ) - 1 := by
      have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) / 2 ≤ s / 2 + δ by linarith) hn0
      linarith
    have h2 : (2 : ℝ) ≤ p * (δ * (n : ℝ)) := calc
      2 = (1 / 4 : ℝ) * 8 := by norm_num
      _ ≤ _ := mul_le_mul hp h8 (by norm_num) hp0.le
    have hgain : 0 < p * δ * (n : ℝ) - (p + (s / 2 + δ)) := by
      linarith only [h2, hcoef]
    have hpositive := mul_pos hgain hnpos
    have hcritN : p * (s / 2) * (n : ℝ) ^ 2 = (n : ℝ) ^ 2 / 4 := by rw [hcrit]; ring
    calc
      (n : ℝ) ^ 2 / 4 < (p * (n : ℝ) - 1) * ((s / 2 + δ) * (n : ℝ) - 1) := by
        linarith only [hcritN, hpositive]
      _ ≤ _ := mul_le_mul hmlo.le hfactor hfactor0 (Nat.cast_nonneg m)
  · have hslack : 4 * δ * (n : ℝ) ≤ ε * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith only [hδε]) hn0
    calc
      (a : ℝ) + 2 * (d : ℝ) ≤ (n : ℝ) - 2 * (p * (n : ℝ) - 1) + 2 * (q + δ) * (n : ℝ) := by
        linarith only [ha, hmlo, hdhi]
      _ = (2 * s - 3 + 2 * δ) * (n : ℝ) + 2 := by dsimp [p, q]; ring
      _ ≤ _ := by
        change (2 * s - 3 + 2 * δ) * (n : ℝ) + 2 ≤ (2 * s - 3 + ε) * (n : ℝ)
        linarith only [h8, hslack]

end TriangleK4Free

open TriangleK4Free in
theorem OMA.solution : type_of% @Erdos1034.erdos_1034.variants.k4_free := by
  intro ε hε
  filter_upwards [feasible ε hε] with n hn
  obtain ⟨a, m, d, hm, hd, hsum, he, hb⟩ := hn
  let hmNeZero : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hc : Fintype.card (Vertex a m) = n := by
    simp only [Vertex, Fintype.card_sum, Fintype.card_fin]
    omega
  let e := Fintype.equivFinOfCardEq hc
  let G := (graph a m d).comap e.symm
  let I : G ≃g graph a m d := SimpleGraph.Iso.comap e.symm (graph a m d)
  classical
  have mapClique {k : ℕ} {T : Finset (Fin n)} (hT : G.IsNClique k T) :
      (graph a m d).IsNClique k (T.map e.symm.toEmbedding) := by
    refine ⟨?_, (Finset.card_map _).trans hT.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hy
    exact hT.isClique hu hv (fun huv => hxy (congrArg e.symm huv))
  refine ⟨G, ?_, ?_, ?_⟩
  · intro T hT
    exact clique_free a m d _ (mapClique hT)
  · have heq : G.edgeSet.ncard = (graph a m d).edgeSet.ncard := by
      rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
      exact I.card_edgeFinset_eq
    rw [heq, edge_card a m d hd]
    push_cast
    exact he
  · intro T hT Y hY
    have hy : Erdos1034.JoinedToTwo (graph a m d) (T.map e.symm.toEmbedding)
        (Y.map e.symm.toEmbedding) := by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hy
      obtain ⟨u, hu, w, hw, huw, hvu, hvw⟩ := hY v hv
      exact ⟨e.symm u, Finset.mem_map.2 ⟨u, hu, rfl⟩,
        e.symm w, Finset.mem_map.2 ⟨w, hw, rfl⟩,
        fun h => huw (e.symm.injective h), hvu, hvw⟩
    have hh := triangle_bound hd (mapClique hT) hy
    rw [Finset.card_map] at hh
    exact (show (Y.card : ℝ) ≤ (a : ℝ) + 2 * (d : ℝ) by exact_mod_cast hh).trans hb