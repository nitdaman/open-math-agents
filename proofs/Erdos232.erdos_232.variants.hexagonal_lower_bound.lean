import FormalConjectures.ErdosProblems.«232»

open scoped EuclideanGeometry
open MeasureTheory

namespace OMA

noncomputable def hexP (p : ℤ × ℤ) : ℝ² :=
  !₂[(2 : ℝ) * (p.1 : ℝ) + (p.2 : ℝ), Real.sqrt 3 * (p.2 : ℝ)]

lemma hexP_zero (p : ℤ × ℤ) : hexP p 0 = 2 * (p.1 : ℝ) + (p.2 : ℝ) := rfl
lemma hexP_one (p : ℤ × ℤ) : hexP p 1 = Real.sqrt 3 * (p.2 : ℝ) := rfl

lemma int_key (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) : (4 : ℤ) ≤ (2 * x + y) ^ 2 + 3 * y ^ 2 := by
  have hsq : ∀ n : ℤ, n ≠ 0 → (1 : ℤ) ≤ n ^ 2 := by
    intro n hn
    by_cases h1 : (1 : ℤ) ≤ n
    · nlinarith
    · have h2 : n ≤ -1 := by omega
      nlinarith
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    simp only [add_zero]
    rcases h with hx | hx
    · have := hsq x hx
      nlinarith
    · exact absurd rfl hx
  · have hy1 := hsq y hy
    rcases eq_or_ne (2 * x + y) 0 with hm | hm
    · have hx0 : x ≠ 0 := by rintro rfl; omega
      have hx1 := hsq x hx0
      have hyy : y = -2 * x := by omega
      rw [hyy]
      nlinarith
    · have hm1 := hsq (2 * x + y) hm
      nlinarith

lemma real_key (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) :
    (4 : ℝ) ≤ (2 * (x : ℝ) + (y : ℝ)) ^ 2 + 3 * (y : ℝ) ^ 2 := by
  have h' := int_key x y h
  have h'' : ((4 : ℤ) : ℝ) ≤ (((2 * x + y) ^ 2 + 3 * y ^ 2 : ℤ) : ℝ) := by exact_mod_cast h'
  push_cast at h''
  linarith

lemma norm_sq_hexP_sub (p q : ℤ × ℤ) :
    ‖hexP p - hexP q‖ ^ 2 =
      (2 * ((p.1 : ℝ) - (q.1 : ℝ)) + ((p.2 : ℝ) - (q.2 : ℝ))) ^ 2
        + 3 * ((p.2 : ℝ) - (q.2 : ℝ)) ^ 2 := by
  have h0 : (hexP p - hexP q) 0 = 2 * ((p.1 : ℝ) - (q.1 : ℝ)) + ((p.2 : ℝ) - (q.2 : ℝ)) := by
    simp only [hexP_zero, PiLp.sub_apply]
    ring
  have h1 : (hexP p - hexP q) 1 = Real.sqrt 3 * ((p.2 : ℝ) - (q.2 : ℝ)) := by
    simp only [hexP_one, PiLp.sub_apply]
    ring
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, h0, h1]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

lemma hexP_sep (p q : ℤ × ℤ) (h : p ≠ q) : 2 ≤ dist (hexP p) (hexP q) := by
  rw [dist_eq_norm]
  have hxy : (p.1 - q.1) ≠ 0 ∨ (p.2 - q.2) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (Prod.ext (sub_eq_zero.mp hc.1) (sub_eq_zero.mp hc.2))
  have h4 : (4 : ℝ) ≤ ‖hexP p - hexP q‖ ^ 2 := by
    rw [norm_sq_hexP_sub]
    have hk := real_key (p.1 - q.1) (p.2 - q.2) hxy
    push_cast at hk
    linarith
  nlinarith [norm_nonneg (hexP p - hexP q)]

/-! ## The fundamental boxes -/

noncomputable def hexCell (p : ℤ × ℤ) : Set ℝ² :=
  {x : ℝ² | x 0 ∈ Set.Ico (2 * (p.1 : ℝ) + (p.2 : ℝ)) (2 * (p.1 : ℝ) + (p.2 : ℝ) + 2) ∧
          x 1 ∈ Set.Ico (Real.sqrt 3 * (p.2 : ℝ)) (Real.sqrt 3 * (p.2 : ℝ) + Real.sqrt 3)}

lemma sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma volume_rect {l u l' u' : ℝ} :
    volume {x : ℝ² | x 0 ∈ Set.Ico l u ∧ x 1 ∈ Set.Ico l' u'} =
      ENNReal.ofReal (u - l) * ENNReal.ofReal (u' - l') := by
  have hmeas : NullMeasurableSet {x : ℝ² | x 0 ∈ Set.Ico l u ∧ x 1 ∈ Set.Ico l' u'} volume := by
    measurability
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage hmeas]
  have hpre : (WithLp.toLp 2 : (Fin 2 → ℝ) → ℝ²) ⁻¹'
      {x : ℝ² | x 0 ∈ Set.Ico l u ∧ x 1 ∈ Set.Ico l' u'}
      = Set.pi Set.univ
          (fun i : Fin 2 => Set.Ico ((![l, l'] : Fin 2 → ℝ) i) ((![u, u'] : Fin 2 → ℝ) i)) := by
    ext y
    simp [Set.mem_pi, Fin.forall_fin_two]
  rw [hpre, Real.volume_pi_Ico]
  simp [Fin.prod_univ_two]

lemma hexCell_measurableSet (p : ℤ × ℤ) : MeasurableSet (hexCell p) := by
  unfold hexCell
  measurability

lemma hexCell_volume (p : ℤ × ℤ) :
    volume (hexCell p) = ENNReal.ofReal (2 * Real.sqrt 3) := by
  unfold hexCell
  have h := volume_rect (l := 2 * (p.1 : ℝ) + (p.2 : ℝ))
    (u := 2 * (p.1 : ℝ) + (p.2 : ℝ) + 2)
    (l' := Real.sqrt 3 * (p.2 : ℝ)) (u' := Real.sqrt 3 * (p.2 : ℝ) + Real.sqrt 3)
  have e1 : 2 * (p.1 : ℝ) + (p.2 : ℝ) + 2 - (2 * (p.1 : ℝ) + (p.2 : ℝ)) = 2 := by ring
  have e2 : Real.sqrt 3 * (p.2 : ℝ) + Real.sqrt 3 - Real.sqrt 3 * (p.2 : ℝ)
      = Real.sqrt 3 := by ring
  rw [e1, e2] at h
  rw [h, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]

lemma hexCell_disjoint (p q : ℤ × ℤ) (h : p ≠ q) : Disjoint (hexCell p) (hexCell q) := by
  rw [Set.disjoint_left]
  rintro x ⟨hx0, hx1⟩ ⟨hy0, hy1⟩
  rcases eq_or_ne p.2 q.2 with hb | hb
  · have ha : p.1 ≠ q.1 := by
      intro h'; exact h (Prod.ext h' hb)
    rcases lt_or_gt_of_ne ha with hlt | hlt
    · have hle : (p.1 : ℝ) + 1 ≤ (q.1 : ℝ) := by
        have : p.1 + 1 ≤ q.1 := by omega
        exact_mod_cast this
      have hM : 2 * (p.1 : ℝ) + (p.2 : ℝ) + 2 ≤ 2 * (q.1 : ℝ) + (q.2 : ℝ) := by
        rw [hb]; nlinarith
      linarith [hx0.2, hy0.1]
    · have hle : (q.1 : ℝ) + 1 ≤ (p.1 : ℝ) := by
        have : q.1 + 1 ≤ p.1 := by omega
        exact_mod_cast this
      have hM : 2 * (q.1 : ℝ) + (q.2 : ℝ) + 2 ≤ 2 * (p.1 : ℝ) + (p.2 : ℝ) := by
        rw [hb]; nlinarith
      linarith [hy0.2, hx0.1]
  · rcases lt_or_gt_of_ne hb with hlt | hlt
    · have hle : (p.2 : ℝ) + 1 ≤ (q.2 : ℝ) := by
        have : p.2 + 1 ≤ q.2 := by omega
        exact_mod_cast this
      have hM : Real.sqrt 3 * (p.2 : ℝ) + Real.sqrt 3 ≤ Real.sqrt 3 * (q.2 : ℝ) := by
        nlinarith [sqrt3_pos]
      linarith [hx1.2, hy1.1]
    · have hle : (q.2 : ℝ) + 1 ≤ (p.2 : ℝ) := by
        have : q.2 + 1 ≤ p.2 := by omega
        exact_mod_cast this
      have hM : Real.sqrt 3 * (q.2 : ℝ) + Real.sqrt 3 ≤ Real.sqrt 3 * (p.2 : ℝ) := by
        nlinarith [sqrt3_pos]
      linarith [hy1.2, hx1.1]

lemma hexCell_cover (x : ℝ²) : ∃ p : ℤ × ℤ, x ∈ hexCell p := by
  set b : ℤ := ⌊x 1 / Real.sqrt 3⌋
  have hb1 : (b : ℝ) ≤ x 1 / Real.sqrt 3 := Int.floor_le _
  have hb2 : x 1 / Real.sqrt 3 < (b : ℝ) + 1 := Int.lt_floor_add_one _
  have hy1 : Real.sqrt 3 * (b : ℝ) ≤ x 1 := by
    have h := mul_le_mul_of_nonneg_left hb1 sqrt3_pos.le
    rwa [mul_div_cancel₀ _ sqrt3_pos.ne'] at h
  have hy2 : x 1 < Real.sqrt 3 * (b : ℝ) + Real.sqrt 3 := by
    have h := mul_lt_mul_of_pos_left hb2 sqrt3_pos
    rw [mul_add, mul_one, mul_div_cancel₀ _ sqrt3_pos.ne'] at h
    linarith
  set a : ℤ := ⌊(x 0 - (b : ℝ)) / 2⌋
  have ha1 : (a : ℝ) ≤ (x 0 - (b : ℝ)) / 2 := Int.floor_le _
  have ha2 : (x 0 - (b : ℝ)) / 2 < (a : ℝ) + 1 := Int.lt_floor_add_one _
  refine ⟨(a, b), ?_, ?_⟩
  · constructor <;> linarith
  · exact ⟨hy1, hy2⟩

lemma norm_sub_hexP_le (p : ℤ × ℤ) {x : ℝ²} (hx : x ∈ hexCell p) :
    ‖x - hexP p‖ ≤ Real.sqrt 7 := by
  have h2 : ‖x - hexP p‖ ^ 2 ≤ 7 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have e0 : (x - hexP p) 0 = x 0 - (2 * (p.1 : ℝ) + (p.2 : ℝ)) := by
      simp only [hexP_zero, PiLp.sub_apply]
    have e1 : (x - hexP p) 1 = x 1 - Real.sqrt 3 * (p.2 : ℝ) := by
      simp only [hexP_one, PiLp.sub_apply]
    rw [e0, e1]
    have hn0 : 0 ≤ x 0 - (2 * (p.1 : ℝ) + (p.2 : ℝ)) := by linarith [hx.1.1]
    have hn0' : x 0 - (2 * (p.1 : ℝ) + (p.2 : ℝ)) < 2 := by linarith [hx.1.2]
    have hn1 : 0 ≤ x 1 - Real.sqrt 3 * (p.2 : ℝ) := by linarith [hx.2.1]
    have hn1' : x 1 - Real.sqrt 3 * (p.2 : ℝ) < Real.sqrt 3 := by linarith [hx.2.2]
    nlinarith [sqrt3_sq]
  have hn : 0 ≤ ‖x - hexP p‖ := norm_nonneg _
  have heq : ‖x - hexP p‖ = Real.sqrt (‖x - hexP p‖ ^ 2) := (Real.sqrt_sq hn).symm
  rw [heq]
  exact Real.sqrt_le_sqrt h2

lemma norm_sq_hexP (p : ℤ × ℤ) :
    ‖hexP p‖ ^ 2 = (2 * (p.1 : ℝ) + (p.2 : ℝ)) ^ 2 + 3 * (p.2 : ℝ) ^ 2 := by
  have h := norm_sq_hexP_sub p (0, 0)
  have hz : hexP (0, 0) = 0 := by simp [hexP]
  rw [hz, sub_zero] at h
  simpa using h

lemma hexP_finite (M : ℝ) : {p : ℤ × ℤ | ‖hexP p‖ ≤ M}.Finite := by
  by_cases hM : M < 0
  · have hempty : {p : ℤ × ℤ | ‖hexP p‖ ≤ M} = ∅ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hp
      linarith [norm_nonneg (hexP p)]
    rw [hempty]
    exact Set.finite_empty
  push Not at hM
  set k : ℤ := ⌈M⌉
  have hkM : M ≤ (k : ℝ) := Int.le_ceil M
  have key : ∀ n : ℤ, |(n : ℝ)| ≤ M → -k ≤ n ∧ n ≤ k := by
    intro n hn
    obtain ⟨h1, h2⟩ := abs_le.mp hn
    constructor
    · have h3 : ((-k : ℤ) : ℝ) ≤ (n : ℝ) := by
        rw [Int.cast_neg]
        linarith
      exact_mod_cast h3
    · have h3 : (n : ℝ) ≤ ((k : ℤ) : ℝ) := by
        linarith
      exact_mod_cast h3
  refine Set.Finite.subset (Set.Finite.prod (Set.finite_Icc (-k) k) (Set.finite_Icc (-k) k)) ?_
  intro p hp
  have hp' : ‖hexP p‖ ≤ M := hp
  simp only [Set.mem_prod, Set.mem_Icc]
  have hnsq := norm_sq_hexP p
  have hM2 : ‖hexP p‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (hexP p)]
  have hb2 : ((p.2 : ℝ)) ^ 2 ≤ M ^ 2 := by nlinarith [sq_nonneg (2 * (p.1 : ℝ) + (p.2 : ℝ))]
  have ha2 : (2 * (p.1 : ℝ) + (p.2 : ℝ)) ^ 2 ≤ M ^ 2 := by nlinarith [sq_nonneg ((p.2 : ℝ))]
  have hab : |(p.2 : ℝ)| ≤ M := by
    have := sq_le_sq.mp hb2
    rwa [abs_of_nonneg hM] at this
  have h2ab : |2 * (p.1 : ℝ) + (p.2 : ℝ)| ≤ M := by
    have := sq_le_sq.mp ha2
    rwa [abs_of_nonneg hM] at this
  have h2a : |2 * (p.1 : ℝ)| ≤ 2 * M := by
    have he : 2 * (p.1 : ℝ) = (2 * (p.1 : ℝ) + (p.2 : ℝ)) - (p.2 : ℝ) := by ring
    rw [he]
    have := abs_sub (2 * (p.1 : ℝ) + (p.2 : ℝ)) (p.2 : ℝ)
    linarith
  have hab1 : |(p.1 : ℝ)| ≤ M := by
    have he : |2 * (p.1 : ℝ)| = 2 * |(p.1 : ℝ)| := by
      rw [abs_mul]; norm_num
    linarith
  obtain ⟨h1a, h1b⟩ := key p.1 hab1
  obtain ⟨h2a, h2b⟩ := key p.2 hab
  exact ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩

/-! ## Hexagonal disc packing and density bound -/

noncomputable def hexSet : Set ℝ² :=
  ⋃ p : ℤ × ℤ, Metric.ball (hexP p) (1 / 2)

lemma hexSet_nullMeasurable : NullMeasurableSet hexSet volume :=
  (isOpen_iUnion fun _ => Metric.isOpen_ball).measurableSet.nullMeasurableSet

lemma hexSet_unitDistanceAvoiding : Erdos214.UnitDistanceAvoiding hexSet := by
  intro x hx y hy
  rcases Set.mem_iUnion.mp hx with ⟨p, hxp⟩
  rcases Set.mem_iUnion.mp hy with ⟨q, hyq⟩
  rw [Metric.mem_ball] at hxp hyq
  rcases eq_or_ne p q with rfl | hpq
  · have hlt : dist x y < 1 := by
      calc dist x y ≤ dist x (hexP p) + dist (hexP p) y := dist_triangle _ _ _
        _ = dist x (hexP p) + dist y (hexP p) := by rw [dist_comm (hexP p) y]
        _ < 1 / 2 + 1 / 2 := add_lt_add hxp hyq
        _ = 1 := by norm_num
    exact ne_of_lt hlt
  · have hsep := hexP_sep p q hpq
    have hgt : 1 < dist x y := by
      have h1 := dist_triangle (hexP p) y (hexP q)
      have h2 := dist_triangle (hexP p) x y
      rw [dist_comm (hexP p) x] at h2
      linarith
    exact ne_of_gt hgt

lemma hexBall_disjoint (p q : ℤ × ℤ) (h : p ≠ q) :
    Disjoint (Metric.ball (hexP p) (1 / 2)) (Metric.ball (hexP q) (1 / 2)) := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  rw [Metric.mem_ball] at hxp hxq
  have hsep := hexP_sep p q h
  have htri : dist (hexP p) (hexP q) ≤ dist (hexP p) x + dist x (hexP q) := dist_triangle _ _ _
  rw [dist_comm (hexP p) x] at htri
  linarith

lemma volume_ball_R2 (x : ℝ²) (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]
  have hpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  rw [show ((2 : ℕ) : ℝ) / 2 + 1 = 2 by norm_num, Real.Gamma_two, div_one, hpi]
  rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (pow_nonneg hr 2), mul_comm]

lemma ballDensity_nonneg (A : Set ℝ²) (R : ℝ) : 0 ≤ Erdos232.ballDensity A R := by
  unfold Erdos232.ballDensity
  positivity

lemma ballDensity_le_one (A : Set ℝ²) (R : ℝ) : Erdos232.ballDensity A R ≤ 1 := by
  unfold Erdos232.ballDensity
  by_cases hR : R ≤ 0
  · have hb : Metric.ball (0 : ℝ²) R = ∅ := Metric.ball_eq_empty.mpr hR
    simp [hb]
  · push Not at hR
    have hvol : volume (Metric.ball (0 : ℝ²) R) = ENNReal.ofReal (Real.pi * R ^ 2) :=
      volume_ball_R2 0 R hR.le
    have hne_top : volume (Metric.ball (0 : ℝ²) R) ≠ ⊤ := by
      rw [hvol]; exact ENNReal.ofReal_ne_top
    have hpos : 0 < (volume (Metric.ball (0 : ℝ²) R)).toReal := by
      rw [hvol, ENNReal.toReal_ofReal (by positivity)]
      positivity
    rw [div_le_one hpos]
    exact ENNReal.toReal_mono hne_top (measure_mono Set.inter_subset_right)

lemma upperDensity_le_one (A : Set ℝ²) : Erdos232.upperDensity A ≤ 1 := by
  unfold Erdos232.upperDensity
  apply Filter.limsup_le_of_le
  · exact Filter.isCoboundedUnder_le_of_le Filter.atTop (fun R => ballDensity_nonneg A R)
  · exact Filter.Eventually.of_forall (fun R => ballDensity_le_one A R)

lemma ballDensity_hexSet_ge (R : ℝ) (hR : 4 < R) :
    (Real.pi / (8 * Real.sqrt 3)) * ((R - 4) / R) ^ 2 ≤ Erdos232.ballDensity hexSet R := by
  let S : Finset (ℤ × ℤ) := (hexP_finite (R - 1)).toFinset
  have hsub_balls : (⋃ p ∈ S, Metric.ball (hexP p) (1 / 2)) ⊆ hexSet ∩ Metric.ball 0 R := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hpS, hxp⟩
    refine ⟨Set.mem_iUnion.mpr ⟨p, hxp⟩, ?_⟩
    have hp : ‖hexP p‖ ≤ R - 1 := by
      have hp' : p ∈ (hexP_finite (R - 1)).toFinset := hpS
      simpa using hp'
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_ball, dist_eq_norm] at hxp
    have htri : ‖x‖ ≤ ‖x - hexP p‖ + ‖hexP p‖ := by
      simpa [sub_add_cancel] using norm_add_le (x - hexP p) (hexP p)
    linarith
  have hdisj : Set.PairwiseDisjoint (↑S : Set (ℤ × ℤ)) (fun p => Metric.ball (hexP p) (1 / 2)) :=
    fun p _ q _ hpq => hexBall_disjoint p q hpq
  have hvol_low_enn :
      (S.card : ENNReal) * ENNReal.ofReal (Real.pi / 4) ≤ volume (hexSet ∩ Metric.ball 0 R) := by
    calc (S.card : ENNReal) * ENNReal.ofReal (Real.pi / 4)
        = ∑ p ∈ S, volume (Metric.ball (hexP p) (1 / 2)) := by
          have hterm : ∀ p ∈ S, volume (Metric.ball (hexP p) (1 / 2)) = ENNReal.ofReal (Real.pi / 4) := by
            intro p _
            rw [volume_ball_R2 (hexP p) (1 / 2) (by norm_num)]
            congr 1
            ring
          rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
      _ = volume (⋃ p ∈ S, Metric.ball (hexP p) (1 / 2)) :=
          (measure_biUnion_finset hdisj (fun _ _ => Metric.isOpen_ball.measurableSet)).symm
      _ ≤ volume (hexSet ∩ Metric.ball 0 R) := measure_mono hsub_balls
  have hcov : Metric.ball (0 : ℝ²) (R - 4) ⊆ ⋃ p ∈ S, hexCell p := by
    intro x hx
    obtain ⟨p, hxp⟩ := hexCell_cover x
    refine Set.mem_iUnion₂.mpr ⟨p, ?_, hxp⟩
    change p ∈ (hexP_finite (R - 1)).toFinset
    rw [Set.Finite.mem_toFinset]
    change ‖hexP p‖ ≤ R - 1
    rw [Metric.mem_ball, dist_zero_right] at hx
    have hdiff := norm_sub_hexP_le p hxp
    have hsqrt7 : Real.sqrt 7 < 3 := by
      have h1 : (7 : ℝ) < 3 ^ 2 := by norm_num
      have h2 : Real.sqrt 7 < Real.sqrt (3 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h1
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)] at h2
    have htri : ‖hexP p‖ ≤ ‖x‖ + ‖x - hexP p‖ := by
      simpa [sub_sub_cancel] using norm_sub_le x (x - hexP p)
    linarith
  have hvol_cov_enn :
      ENNReal.ofReal (Real.pi * (R - 4) ^ 2) ≤
        (S.card : ENNReal) * ENNReal.ofReal (2 * Real.sqrt 3) := by
    calc ENNReal.ofReal (Real.pi * (R - 4) ^ 2)
        = volume (Metric.ball (0 : ℝ²) (R - 4)) := (volume_ball_R2 0 (R - 4) (by linarith)).symm
      _ ≤ volume (⋃ p ∈ S, hexCell p) := measure_mono hcov
      _ ≤ ∑ p ∈ S, volume (hexCell p) := measure_biUnion_finset_le S hexCell
      _ = (S.card : ENNReal) * ENNReal.ofReal (2 * Real.sqrt 3) := by
          simp [hexCell_volume, Finset.sum_const, nsmul_eq_mul]
  have hballR_vol : volume (Metric.ball (0 : ℝ²) R) = ENNReal.ofReal (Real.pi * R ^ 2) :=
    volume_ball_R2 0 R (by linarith)
  have hne_top_inter : volume (hexSet ∩ Metric.ball (0 : ℝ²) R) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    rw [hballR_vol]
    exact ENNReal.ofReal_ne_top
  have hlow_real : (S.card : ℝ) * (Real.pi / 4) ≤ (volume (hexSet ∩ Metric.ball 0 R)).toReal := by
    have h := ENNReal.toReal_mono hne_top_inter hvol_low_enn
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity)] at h
  have hcov_real : Real.pi * (R - 4) ^ 2 ≤ (S.card : ℝ) * (2 * Real.sqrt 3) := by
    have hne : (S.card : ENNReal) * ENNReal.ofReal (2 * Real.sqrt 3) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
    have h := ENNReal.toReal_mono hne hvol_cov_enn
    rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity)] at h
  have hR_pos : 0 < R := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsqrt3_pos : 0 < Real.sqrt 3 := sqrt3_pos
  have hS_ge : Real.pi * (R - 4) ^ 2 / (2 * Real.sqrt 3) ≤ (S.card : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    exact hcov_real
  have hnum_ge : Real.pi * (R - 4) ^ 2 / (2 * Real.sqrt 3) * (Real.pi / 4) ≤
      (volume (hexSet ∩ Metric.ball 0 R)).toReal :=
    le_trans (mul_le_mul_of_nonneg_right hS_ge (by positivity)) hlow_real
  unfold Erdos232.ballDensity
  rw [hballR_vol, ENNReal.toReal_ofReal (by positivity)]
  rw [le_div_iff₀ (by positivity)]
  have halg : (Real.pi / (8 * Real.sqrt 3)) * ((R - 4) / R) ^ 2 * (Real.pi * R ^ 2) =
      Real.pi * (R - 4) ^ 2 / (2 * Real.sqrt 3) * (Real.pi / 4) := by
    field_simp
    ring
  linarith

lemma hexSet_upperDensity_ge : Real.pi / (8 * Real.sqrt 3) ≤ Erdos232.upperDensity hexSet := by
  let g : ℝ → ℝ := fun R => (Real.pi / (8 * Real.sqrt 3)) * ((R - 4) / R) ^ 2
  have hg_tendsto : Filter.Tendsto g Filter.atTop (nhds (Real.pi / (8 * Real.sqrt 3))) := by
    have hinv : Filter.Tendsto (fun R : ℝ => (4 : ℝ) / R) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop Filter.tendsto_id
    have h1 : Filter.Tendsto (fun R : ℝ => 1 - (4 : ℝ) / R) Filter.atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hinv
    have h2 : Filter.Tendsto (fun R : ℝ => (R - 4) / R) Filter.atTop (nhds 1) := by
      refine h1.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
      field_simp
    have h3 : Filter.Tendsto (fun R : ℝ => ((R - 4) / R) ^ 2) Filter.atTop (nhds 1) := by
      simpa using h2.pow 2
    simpa using (tendsto_const_nhds.mul h3)
  have hle : g ≤ᶠ[Filter.atTop] Erdos232.ballDensity hexSet := by
    filter_upwards [Filter.eventually_gt_atTop (4 : ℝ)] with R hR
    exact ballDensity_hexSet_ge R hR
  have hlim_le : Filter.limsup g Filter.atTop ≤ Erdos232.upperDensity hexSet := by
    unfold Erdos232.upperDensity
    refine Filter.limsup_le_limsup hle ?_ ?_
    · exact hg_tendsto.isBoundedUnder_ge.isCoboundedUnder_le
    · exact Filter.isBoundedUnder_of ⟨1, fun R => ballDensity_le_one hexSet R⟩
  rwa [hg_tendsto.limsup_eq] at hlim_le

end OMA

theorem OMA.solution : type_of% @Erdos232.erdos_232.variants.hexagonal_lower_bound := by
  refine le_trans OMA.hexSet_upperDensity_ge ?_
  unfold Erdos232.m₁
  refine le_csSup ?_ ⟨OMA.hexSet, OMA.hexSet_nullMeasurable, OMA.hexSet_unitDistanceAvoiding, rfl⟩
  refine ⟨1, ?_⟩
  rintro d ⟨A, _, _, rfl⟩
  exact OMA.upperDensity_le_one A
