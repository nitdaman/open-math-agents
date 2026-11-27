import FormalConjectures.ErdosProblems.«1066»

-- Problem: Erdős Problem 1066 — pollack
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- No four colour theorem needed: the lowest point of a penny configuration has at most
-- three neighbours, so greedily removing it gives an independent set of size n/4.

open scoped EuclideanGeometry Topology

namespace OMA

theorem sq_dist (p q : ℝ²) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
    Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- Two unit vectors in the closed upper half plane with inner product at most 1/2 have
arccos-angles at least π/3 apart. -/
theorem angle_sep (x1 y1 x2 y2 : ℝ) (h1 : x1 ^ 2 + y1 ^ 2 = 1) (h2 : x2 ^ 2 + y2 ^ 2 = 1)
    (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hdot : x1 * x2 + y1 * y2 ≤ 1 / 2) :
    Real.pi / 3 ≤ |Real.arccos x1 - Real.arccos x2| := by
  have hx1 : -1 ≤ x1 ∧ x1 ≤ 1 := by constructor <;> nlinarith
  have hx2 : -1 ≤ x2 ∧ x2 ≤ 1 := by constructor <;> nlinarith
  have hs1 : Real.sin (Real.arccos x1) = y1 := by
    rw [Real.sin_arccos, show 1 - x1 ^ 2 = y1 ^ 2 by linarith, Real.sqrt_sq hy1]
  have hs2 : Real.sin (Real.arccos x2) = y2 := by
    rw [Real.sin_arccos, show 1 - x2 ^ 2 = y2 ^ 2 by linarith, Real.sqrt_sq hy2]
  have hcos : Real.cos (Real.arccos x1 - Real.arccos x2) = x1 * x2 + y1 * y2 := by
    rw [Real.cos_sub, Real.cos_arccos hx1.1 hx1.2, Real.cos_arccos hx2.1 hx2.2, hs1, hs2]
  by_contra hlt
  push Not at hlt
  have hpi := Real.pi_pos
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (Real.arccos x1 - Real.arccos x2))
    (by linarith : Real.pi / 3 ≤ Real.pi) hlt
  rw [Real.cos_abs, hcos, Real.cos_pi_div_three] at this
  linarith

/-- The lowest point has at most three neighbours. -/
theorem few_nbrs (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y))
    (v : ℝ²) (hmin : ∀ p ∈ X, v 1 < p 1 ∨ (v 1 = p 1 ∧ v 0 ≤ p 0)) :
    (X.filter (fun p => dist p v = 1)).card ≤ 3 := by
  classical
  by_contra hcard
  push Not at hcard
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (show 4 ≤ _ from hcard)
  have hpi := Real.pi_pos
  -- data of each neighbour
  have hdata : ∀ p ∈ S, (p 0 - v 0) ^ 2 + (p 1 - v 1) ^ 2 = 1 ∧ 0 ≤ p 1 - v 1 ∧
      Real.arccos (p 0 - v 0) < Real.pi := by
    intro p hp
    have hpN := hSsub hp
    rw [Finset.mem_filter] at hpN
    have hd : (p 0 - v 0) ^ 2 + (p 1 - v 1) ^ 2 = 1 := by
      rw [← sq_dist, hpN.2]; norm_num
    have hm := hmin p hpN.1
    refine ⟨hd, by rcases hm with h | h <;> linarith, ?_⟩
    rw [Real.arccos_lt_pi]
    rcases hm with h | h
    · nlinarith
    · have h0 : p 1 - v 1 = 0 := by linarith
      rw [h0] at hd
      nlinarith
  have hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      Real.pi / 3 ≤ |Real.arccos (p 0 - v 0) - Real.arccos (q 0 - v 0)| := by
    intro p hp q hq hpq
    obtain ⟨hp1, hp2, -⟩ := hdata p hp
    obtain ⟨hq1, hq2, -⟩ := hdata q hq
    have hpX := (Finset.mem_filter.mp (hSsub hp)).1
    have hqX := (Finset.mem_filter.mp (hSsub hq)).1
    have hd := hX (Finset.mem_coe.mpr hpX) (Finset.mem_coe.mpr hqX) hpq
    have hd2 : 1 ≤ dist p q ^ 2 := by nlinarith [dist_nonneg (x := p) (y := q)]
    rw [sq_dist] at hd2
    apply angle_sep _ _ _ _ hp1 hq1 hp2 hq2
    nlinarith
  -- pigeonhole on buckets
  have hbucket : ∀ p ∈ S, ⌊Real.arccos (p 0 - v 0) / (Real.pi / 3)⌋₊ ∈ Finset.range 3 := by
    intro p hp
    obtain ⟨-, -, hlt⟩ := hdata p hp
    rw [Finset.mem_range, Nat.floor_lt (div_nonneg (Real.arccos_nonneg _) (by positivity))]
    rw [div_lt_iff₀ (by positivity)]
    push_cast
    linarith
  obtain ⟨p, hp, q, hq, hpq, hfl⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by rw [hScard, Finset.card_range]; norm_num) hbucket
  have hsp := hsep p hp q hq hpq
  have hp0 := div_nonneg (Real.arccos_nonneg (p 0 - v 0)) (by positivity : (0 : ℝ) ≤ Real.pi / 3)
  have hq0 := div_nonneg (Real.arccos_nonneg (q 0 - v 0)) (by positivity : (0 : ℝ) ≤ Real.pi / 3)
  have a1 := Nat.floor_le hp0
  have a2 := Nat.lt_floor_add_one (Real.arccos (p 0 - v 0) / (Real.pi / 3))
  have b1 := Nat.floor_le hq0
  have b2 := Nat.lt_floor_add_one (Real.arccos (q 0 - v 0) / (Real.pi / 3))
  rw [hfl] at a1 a2
  have hdiff : |Real.arccos (p 0 - v 0) / (Real.pi / 3) - Real.arccos (q 0 - v 0) / (Real.pi / 3)| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 3),
    div_lt_one (by positivity)] at hdiff
  linarith

/-- A lexicographically lowest point exists. -/
theorem exists_lowest (X : Finset ℝ²) (hne : X.Nonempty) :
    ∃ v ∈ X, ∀ p ∈ X, v 1 < p 1 ∨ (v 1 = p 1 ∧ v 0 ≤ p 0) := by
  classical
  obtain ⟨w, hw, hwmin⟩ := Finset.exists_min_image X (fun p : ℝ² => p 1) hne
  have hne2 : (X.filter (fun p : ℝ² => p 1 = w 1)).Nonempty := ⟨w, Finset.mem_filter.mpr ⟨hw, rfl⟩⟩
  obtain ⟨v, hv, hvmin⟩ := Finset.exists_min_image _ (fun p : ℝ² => p 0) hne2
  rw [Finset.mem_filter] at hv
  refine ⟨v, hv.1, fun p hp => ?_⟩
  rcases lt_or_eq_of_le (hwmin p hp) with h | h
  · exact Or.inl (hv.2 ▸ h)
  · exact Or.inr ⟨hv.2.trans h, hvmin p (Finset.mem_filter.mpr ⟨hp, h.symm⟩)⟩

/-- Greedy independent set. -/
theorem greedy : ∀ (n : ℕ) (X : Finset ℝ²), X.card = n →
    (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y) →
    ∃ I ⊆ X, (∀ p ∈ I, ∀ q ∈ I, dist p q ≠ 1) ∧ X.card ≤ 4 * I.card := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hXn hX
    rcases X.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    obtain ⟨v, hvX, hmin⟩ := exists_lowest X hne
    have hN := few_nbrs X hX v hmin
    set N := X.filter (fun p => dist p v = 1) with hNdef
    set X' := (X.erase v) \ N with hX'
    have hX'sub : X' ⊆ X := (Finset.sdiff_subset).trans (Finset.erase_subset _ _)
    have hcard1 : (X.erase v).card = X.card - 1 := Finset.card_erase_of_mem hvX
    have hcard2 : (X.erase v).card - N.card ≤ X'.card := Finset.le_card_sdiff _ _
    have hcard3 : X'.card ≤ (X.erase v).card := Finset.card_le_card Finset.sdiff_subset
    have hpos : 0 < X.card := Finset.card_pos.mpr hne
    have hlt : X'.card < n := by omega
    obtain ⟨I', hI'sub, hI'ind, hI'card⟩ := ih X'.card hlt X' rfl
      (hX.mono (by exact_mod_cast hX'sub))
    have hvI' : v ∉ I' := by
      intro h
      have := hI'sub h
      rw [hX', Finset.mem_sdiff, Finset.mem_erase] at this
      exact this.1.1 rfl
    refine ⟨insert v I', ?_, ?_, ?_⟩
    · intro p hp
      rw [Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · exact hvX
      · exact hX'sub (hI'sub hp)
    · have hfar : ∀ q ∈ I', dist q v ≠ 1 := by
        intro q hq hd
        have := hI'sub hq
        rw [hX', Finset.mem_sdiff] at this
        exact this.2 (Finset.mem_filter.mpr ⟨hX'sub (hI'sub hq), hd⟩)
      intro p hp q hq
      rw [Finset.mem_insert] at hp hq
      rcases hp with rfl | hp <;> rcases hq with rfl | hq
      · rw [dist_self]; norm_num
      · rw [dist_comm]; exact hfar q hq
      · exact hfar p hp
      · exact hI'ind p hp q hq
    · rw [Finset.card_insert_of_notMem hvI']
      omega

/-- The independence number bound. -/
theorem indep_bound (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)) :
    X.card ≤ 4 * (SimpleGraph.UnitDistancePlaneGraph (X : Set ℝ²)).indepNum := by
  classical
  obtain ⟨I, hIsub, hIind, hIcard⟩ := greedy X.card X rfl hX
  let s : Finset ((X : Set ℝ²)) := I.subtype (fun p => p ∈ (X : Set ℝ²))
  have hs : (SimpleGraph.UnitDistancePlaneGraph (X : Set ℝ²)).IsIndepSet (s : Set ((X : Set ℝ²))) := by
    intro a ha b hb _ hadj
    have ha' : (a : ℝ²) ∈ I := by simpa [s] using ha
    have hb' : (b : ℝ²) ∈ I := by simpa [s] using hb
    exact hIind _ ha' _ hb' hadj
  have hscard : s.card = I.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun p hp => Finset.mem_coe.mpr (hIsub hp))
  have := hs.card_le_indepNum
  omega

/-- An explicit configuration with `n` points. -/
theorem exists_config (n : ℕ) : ∃ X : Finset ℝ², X.card = n ∧
    (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y) := by
  classical
  have hinj : Function.Injective (fun i : ℕ => (!₂[(i : ℝ), 0] : ℝ²)) := by
    intro i j hij
    have := congrFun (congrArg (fun p : ℝ² => (p : Fin 2 → ℝ)) hij) 0
    simpa using this
  refine ⟨(Finset.range n).image (fun i : ℕ => (!₂[(i : ℝ), 0] : ℝ²)), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  · intro p hp q hq hpq
    simp only [Finset.coe_image, Set.mem_image] at hp hq
    obtain ⟨i, -, rfl⟩ := hp
    obtain ⟨j, -, rfl⟩ := hq
    have hij : i ≠ j := fun h => hpq (by rw [h])
    have h2 : (1 : ℝ) ≤ dist (!₂[(i : ℝ), 0] : ℝ²) (!₂[(j : ℝ), 0]) ^ 2 := by
      rw [sq_dist]
      simp
      have : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
        rcases Nat.lt_or_gt_of_ne hij with h | h
        · have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
        · have : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast h
          rw [abs_of_nonneg (by linarith)]; linarith
      nlinarith [abs_mul_abs_self ((i : ℝ) - (j : ℝ))]
    nlinarith [dist_nonneg (x := (!₂[(i : ℝ), 0] : ℝ²)) (y := !₂[(j : ℝ), 0])]

end OMA

theorem OMA.solution : type_of% @Erdos1066.erdos_1066.variants.pollack := by
  intro n
  have hmem : (n + 3) / 4 ∈ {m : ℕ | ∀ X : Finset ℝ², X.card = n →
      (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y) →
        m ≤ (SimpleGraph.UnitDistancePlaneGraph (X : Set ℝ²)).indepNum} := by
    intro X hXn hX
    have := OMA.indep_bound X hX
    omega
  have hbdd : BddAbove {m : ℕ | ∀ X : Finset ℝ², X.card = n →
      (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y) →
        m ≤ (SimpleGraph.UnitDistancePlaneGraph (X : Set ℝ²)).indepNum} := by
    obtain ⟨X0, hX0n, hX0⟩ := OMA.exists_config n
    exact ⟨_, fun m hm => hm X0 hX0n hX0⟩
  have hle : (n + 3) / 4 ≤ Erdos1066.g n := le_csSup hbdd hmem
  have h4 : n ≤ 4 * Erdos1066.g n := by omega
  have h4R : (n : ℝ) ≤ 4 * (Erdos1066.g n : ℝ) := by exact_mod_cast h4
  linarith
