import FormalConjectures.ErdosProblems.«831»

-- Problem: Erdős Problem 831 — szekeres
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/831.lean:96 (declaration Erdos831.erdos_831.variants.szekeres)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open EuclideanGeometry

namespace OMA831

lemma ext2 {x y : ℝ²} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext i; fin_cases i <;> simp [h0, h1]

lemma dist_sq (x y : ℝ²) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

lemma dist_eq_iff (x y z w : ℝ²) :
    dist x y = dist z w ↔ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = (z 0 - w 0) ^ 2 + (z 1 - w 1) ^ 2 := by
  rw [← dist_sq, ← dist_sq]
  constructor
  · intro h; rw [h]
  · intro h
    exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).mp h

def cr (a b c : ℝ²) : ℝ := (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

lemma collinear_of_cr (a b c : ℝ²) (h : cr a b c = 0) : Collinear ℝ ({a, b, c} : Set ℝ²) := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  by_cases hab : b = a
  · refine ⟨c -ᵥ a, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp [hab]⟩
    · exact ⟨1, by simp⟩
  · refine ⟨b -ᵥ a, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · have hne : b 0 - a 0 ≠ 0 ∨ b 1 - a 1 ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hab (ext2 (by linarith [hc.1]) (by linarith [hc.2]))
      unfold cr at h
      rcases hne with h0 | h1
      · refine ⟨(p 0 - a 0) / (b 0 - a 0), ext2 ?_ ?_⟩
        · simp; field_simp; ring
        · simp; field_simp; linear_combination h
      · refine ⟨(p 1 - a 1) / (b 1 - a 1), ext2 ?_ ?_⟩
        · simp; field_simp; linear_combination -h
        · simp; field_simp; ring

lemma cr_of_collinear (a b c : ℝ²) (h : Collinear ℝ ({a, b, c} : Set ℝ²)) : cr a b c = 0 := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r, hr⟩ := hv b (by simp)
  obtain ⟨s, hs⟩ := hv c (by simp)
  have hb0 : b 0 = r * v 0 + a 0 := by rw [hr]; simp
  have hb1 : b 1 = r * v 1 + a 1 := by rw [hr]; simp
  have hc0 : c 0 = s * v 0 + a 0 := by rw [hs]; simp
  have hc1 : c 1 = s * v 1 + a 1 := by rw [hs]; simp
  unfold cr; rw [hb0, hb1, hc0, hc1]; ring

def d2 (x y : ℝ²) : ℝ := (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2

lemma d2_of_dist {x y z w : ℝ²} (h : dist x y = dist z w) : d2 x y = d2 z w :=
  (dist_eq_iff x y z w).mp h

lemma dist_of_d2 {x y z w : ℝ²} (h : d2 x y = d2 z w) : dist x y = dist z w :=
  (dist_eq_iff x y z w).mpr h

lemma uniq (a b c z z' : ℝ²) (h : cr a b c ≠ 0) (hz1 : d2 a z = d2 b z) (hz2 : d2 a z = d2 c z)
    (hz1' : d2 a z' = d2 b z') (hz2' : d2 a z' = d2 c z') : z = z' := by
  unfold d2 at *; unfold cr at h
  have e1 : (z 0 - z' 0) * (b 0 - a 0) + (z 1 - z' 1) * (b 1 - a 1) = 0 := by
    linear_combination (hz1 - hz1') / 2
  have e2 : (z 0 - z' 0) * (c 0 - a 0) + (z 1 - z' 1) * (c 1 - a 1) = 0 := by
    linear_combination (hz2 - hz2') / 2
  have f0 : (z 0 - z' 0) * ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) = 0 := by
    linear_combination (c 1 - a 1) * e1 - (b 1 - a 1) * e2
  have f1 : (z 1 - z' 1) * ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) = 0 := by
    linear_combination (b 0 - a 0) * e2 - (c 0 - a 0) * e1
  have g0 := (mul_eq_zero.mp f0).resolve_right h
  have g1 := (mul_eq_zero.mp f1).resolve_right h
  exact ext2 (by linarith) (by linarith)

lemma circumcenter_ex (a b c : ℝ²) (h : cr a b c ≠ 0) :
    ∃ O : ℝ², d2 a O = d2 b O ∧ d2 a O = d2 c O := by
  set u0 := b 0 - a 0; set u1 := b 1 - a 1; set w0 := c 0 - a 0; set w1 := c 1 - a 1
  have hD : u0 * w1 - u1 * w0 ≠ 0 := h
  set uu := u0 ^ 2 + u1 ^ 2; set ww := w0 ^ 2 + w1 ^ 2
  -- solve 2 (o - a) . u = uu, 2 (o - a) . w = ww
  set D := u0 * w1 - u1 * w0
  set o0 := a 0 + (uu * w1 - ww * u1) / (2 * D)
  set o1 := a 1 + (ww * u0 - uu * w0) / (2 * D)
  refine ⟨a + ((o0 - a 0) • EuclideanSpace.single 0 (1 : ℝ) +
    (o1 - a 1) • EuclideanSpace.single 1 (1 : ℝ)), ?_, ?_⟩
  · unfold d2; simp
    have : b 0 = a 0 + u0 := by simp [u0]
    have : b 1 = a 1 + u1 := by simp [u1]
    simp only [o0, o1] at *
    rw [show b 0 = a 0 + u0 by simp [u0], show b 1 = a 1 + u1 by simp [u1]]
    field_simp; ring
  · unfold d2; simp
    simp only [o0, o1] at *
    rw [show c 0 = a 0 + w0 by simp [w0], show c 1 = a 1 + w1 by simp [w1]]
    field_simp; ring

lemma vec_pm (v0 v1 w0 w1 : ℝ) (nv : v0 ^ 2 + v1 ^ 2 = w0 ^ 2 + w1 ^ 2)
    (hX : v0 * w1 - v1 * w0 = 0) : (v0 = w0 ∧ v1 = w1) ∨ (v0 = -w0 ∧ v1 = -w1) := by
  have hP : (v0 * w0 + v1 * w1 - (w0 ^ 2 + w1 ^ 2)) * (v0 * w0 + v1 * w1 + (w0 ^ 2 + w1 ^ 2)) = 0 := by
    linear_combination (w0 ^ 2 + w1 ^ 2) * nv - (v0 * w1 - v1 * w0) * hX
  rcases mul_eq_zero.mp hP with h | h
  · left
    have hs : (v0 - w0) ^ 2 + (v1 - w1) ^ 2 = 0 := by linear_combination nv - 2 * h
    constructor <;> nlinarith [sq_nonneg (v0 - w0), sq_nonneg (v1 - w1)]
  · right
    have hs : (v0 + w0) ^ 2 + (v1 + w1) ^ 2 = 0 := by linear_combination nv + 2 * h
    constructor <;> nlinarith [sq_nonneg (v0 + w0), sq_nonneg (v1 + w1)]

lemma cross_zero (v0 v1 w0 w1 u0 u1 : ℝ) (hu : u0 ≠ 0 ∨ u1 ≠ 0) (pv : v0 * u0 + v1 * u1 = 0)
    (pw : w0 * u0 + w1 * u1 = 0) : v0 * w1 - v1 * w0 = 0 := by
  rcases hu with h0 | h1
  · have : (v0 * w1 - v1 * w0) * u0 = 0 := by linear_combination w1 * pv - v1 * pw
    exact (mul_eq_zero.mp this).resolve_right h0
  · have : (v0 * w1 - v1 * w0) * u1 = 0 := by linear_combination v0 * pw - w0 * pv
    exact (mul_eq_zero.mp this).resolve_right h1

/-- Two points equidistant from `a` and `b` and at the same distance: centres `O` or `a + b - O`. -/
lemma two_centers (a b c O : ℝ²) (hab : a ≠ b) (hc : d2 a c = d2 b c) (hO : d2 a O = d2 b O)
    (hcO : d2 a c = d2 a O) : c = O ∨ c = a + b - O := by
  unfold d2 at *
  have hu : b 0 - a 0 ≠ 0 ∨ b 1 - a 1 ≠ 0 := by
    by_contra hh; push Not at hh
    exact hab (ext2 (by linarith [hh.1]) (by linarith [hh.2]))
  have pv : (2 * c 0 - a 0 - b 0) * (b 0 - a 0) + (2 * c 1 - a 1 - b 1) * (b 1 - a 1) = 0 := by
    linear_combination hc
  have pw : (2 * O 0 - a 0 - b 0) * (b 0 - a 0) + (2 * O 1 - a 1 - b 1) * (b 1 - a 1) = 0 := by
    linear_combination hO
  have nv : (2 * c 0 - a 0 - b 0) ^ 2 + (2 * c 1 - a 1 - b 1) ^ 2
      = (2 * O 0 - a 0 - b 0) ^ 2 + (2 * O 1 - a 1 - b 1) ^ 2 := by
    linear_combination 4 * hcO - 2 * hc + 2 * hO
  have hX := cross_zero _ _ _ _ _ _ hu pv pw
  rcases vec_pm _ _ _ _ nv hX with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · left; exact ext2 (by linarith) (by linarith)
  · right; exact ext2 (by simp; linarith) (by simp; linarith)

lemma right_of_dot (a b c : ℝ²)
    (h : (b 0 - a 0) * (c 0 - a 0) + (b 1 - a 1) * (c 1 - a 1) = 0) : ∠ b a c = Real.pi / 2 := by
  unfold EuclideanGeometry.angle
  rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  linear_combination h

lemma alt_cr (a b c O : ℝ²) (hb : d2 a O = d2 b O) (hc : d2 a O = d2 c O)
    (h : cr a b (a + b + c - O - O) = 0) :
    (b 0 - a 0) * (c 0 - a 0) + (b 1 - a 1) * (c 1 - a 1) = 0 ∨
    (a 0 - b 0) * (c 0 - b 0) + (a 1 - b 1) * (c 1 - b 1) = 0 := by
  unfold cr at h; unfold d2 at hb hc
  simp only [PiLp.add_apply, PiLp.sub_apply] at h
  have E1 : (a 0 + b 0 - 2 * O 0) * (b 0 - a 0) + (a 1 + b 1 - 2 * O 1) * (b 1 - a 1) = 0 := by
    linear_combination -hb
  have E2 : (b 0 + c 0 - 2 * O 0) * (c 0 - b 0) + (b 1 + c 1 - 2 * O 1) * (c 1 - b 1) = 0 := by
    linear_combination hb - hc
  have key : ((b 0 - a 0) * (c 0 - a 0) + (b 1 - a 1) * (c 1 - a 1)) *
      ((b 0 - a 0) * (c 0 - a 0) + (b 1 - a 1) * (c 1 - a 1) -
        ((b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2)) = 0 := by
    linear_combination ((b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2) * E2
      - (-(b 1 - a 1) * (c 0 - b 0) + (b 0 - a 0) * (c 1 - b 1)) * h
      - ((b 0 - a 0) * (c 0 - b 0) + (b 1 - a 1) * (c 1 - b 1)) * E1
  rcases mul_eq_zero.mp key with k | k
  · exact Or.inl k
  · right; linear_combination -k

lemma antipode (a b c O : ℝ²) (hb : d2 a O = d2 b O) (h0 : b 0 + c 0 = 2 * O 0)
    (h1 : b 1 + c 1 = 2 * O 1) :
    (b 0 - a 0) * (c 0 - a 0) + (b 1 - a 1) * (c 1 - a 1) = 0 := by
  unfold d2 at hb
  linear_combination hb + (b 0 - a 0) * h0 + (b 1 - a 1) * h1

lemma sphere_rad (a b c z : ℝ²) (hcr : cr a b c ≠ 0) (hb : d2 a z = d2 b z) (hc : d2 a z = d2 c z)
    (s : EuclideanGeometry.Sphere ℝ²) (ha : a ∈ s) (hbs : b ∈ s) (hcs : c ∈ s) :
    s.radius = dist a z := by
  rw [EuclideanGeometry.mem_sphere] at ha hbs hcs
  have e : s.center = z := uniq a b c s.center z hcr (d2_of_dist (ha.trans hbs.symm))
    (d2_of_dist (ha.trans hcs.symm)) hb hc
  rw [← ha, e]

lemma d2_r1 (p q O : ℝ²) : d2 p (p + q - O) = d2 q O := by simp [d2]; ring
lemma d2_r2 (p q O : ℝ²) : d2 q (p + q - O) = d2 p O := by simp [d2]; ring
lemma d2_h3 (a b c O : ℝ²) : d2 (a + b + c - O - O) (a + b - O) = d2 c O := by simp [d2]; ring
lemma d2_h2 (a b c O : ℝ²) : d2 (a + b + c - O - O) (a + c - O) = d2 b O := by simp [d2]; ring
lemma d2_h1 (a b c O : ℝ²) : d2 (a + b + c - O - O) (b + c - O) = d2 a O := by simp [d2]; ring

lemma ncard4_le (a b c d : ℝ²) : ({a, b, c, d} : Set ℝ²).ncard ≤ 4 := by
  calc ({a, b, c, d} : Set ℝ²).ncard ≤ ({b, c, d} : Set ℝ²).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ (({c, d} : Set ℝ²).ncard + 1) + 1 := by gcongr; exact Set.ncard_insert_le _ _
    _ ≤ ((({d} : Set ℝ²).ncard + 1) + 1) + 1 := by gcongr; exact Set.ncard_insert_le _ _
    _ = 4 := by rw [Set.ncard_singleton]

lemma three_le (P : Set ℝ²) [Finite P] (s : EuclideanGeometry.Sphere ℝ²) (a b c : ℝ²)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P)
    (has : a ∈ s) (hbs : b ∈ s) (hcs : c ∈ s) : 3 ≤ {p ∈ P | p ∈ s}.ncard := by
  have h3 : ({a, b, c} : Set ℝ²).ncard = 3 := Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  rw [← h3]
  apply Set.ncard_le_ncard
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨ha, has⟩
    · exact ⟨hb, hbs⟩
    · exact ⟨hc, hcs⟩
  · exact (Set.toFinite P).subset (fun p hp => hp.1)


lemma not_col {a b c : ℝ²} (h : cr a b c ≠ 0) : ¬ Collinear ℝ ({a, b, c} : Set ℝ²) :=
  fun hc => h (cr_of_collinear a b c hc)

lemma cr_ne_of_not_col {a b c : ℝ²} (h : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) : cr a b c ≠ 0 :=
  fun hc => h (collinear_of_cr a b c hc)

theorem main (x₁ x₂ x₃ : ℝ²) (hcol : ¬ Collinear ℝ ({x₁, x₂, x₃} : Set ℝ²))
    (hright : ¬ IsRightAngled x₁ x₂ x₃) :
    ∃! x₄ : ℝ², x₄ ∉ ({x₁, x₂, x₃} : Set ℝ²) ∧
      InGeneralPosition ({x₁, x₂, x₃, x₄} : Set ℝ²) ∧
      (Erdos831.circleRadii ({x₁, x₂, x₃, x₄} : Set ℝ²)).ncard = 1 := by
  have N0 : cr x₁ x₂ x₃ ≠ 0 := cr_ne_of_not_col hcol
  have nR1 : (x₂ 0 - x₁ 0) * (x₃ 0 - x₁ 0) + (x₂ 1 - x₁ 1) * (x₃ 1 - x₁ 1) ≠ 0 :=
    fun h => hright (Or.inl (right_of_dot _ _ _ h))
  have nR2 : (x₁ 0 - x₂ 0) * (x₃ 0 - x₂ 0) + (x₁ 1 - x₂ 1) * (x₃ 1 - x₂ 1) ≠ 0 :=
    fun h => hright (Or.inr (Or.inl (right_of_dot _ _ _ h)))
  have nR3 : (x₂ 0 - x₃ 0) * (x₁ 0 - x₃ 0) + (x₂ 1 - x₃ 1) * (x₁ 1 - x₃ 1) ≠ 0 :=
    fun h => hright (Or.inr (Or.inr (right_of_dot _ _ _ h)))
  have h12 : x₁ ≠ x₂ := by rintro rfl; apply N0; unfold cr; ring
  have h13 : x₁ ≠ x₃ := by rintro rfl; apply N0; unfold cr; ring
  have h23 : x₂ ≠ x₃ := by rintro rfl; apply N0; unfold cr; ring
  obtain ⟨O, hO2, hO3⟩ := circumcenter_ex x₁ x₂ x₃ N0
  have hO23 : d2 x₂ O = d2 x₃ O := hO2.symm.trans hO3
  set H : ℝ² := x₁ + x₂ + x₃ - O - O with hH
  set c12 : ℝ² := x₁ + x₂ - O with hc12
  set c13 : ℝ² := x₁ + x₃ - O with hc13
  set c23 : ℝ² := x₂ + x₃ - O with hc23
  have N1 : cr x₁ x₂ H ≠ 0 := by
    intro h
    rcases alt_cr x₁ x₂ x₃ O hO2 hO3 h with h' | h'
    · exact nR1 h'
    · exact nR2 h'
  have N2 : cr x₁ x₃ H ≠ 0 := by
    intro h
    rw [show H = x₁ + x₃ + x₂ - O - O by rw [hH]; abel] at h
    rcases alt_cr x₁ x₃ x₂ O hO3 hO2 h with h' | h'
    · exact nR1 (by linear_combination h')
    · exact nR3 (by linear_combination h')
  have N3 : cr x₂ x₃ H ≠ 0 := by
    intro h
    rw [show H = x₂ + x₃ + x₁ - O - O by rw [hH]; abel] at h
    rcases alt_cr x₂ x₃ x₁ O hO23 hO2.symm h with h' | h'
    · exact nR2 (by linear_combination h')
    · exact nR3 (by linear_combination h')
  have hH1 : H ≠ x₁ := by
    intro h
    have e0 := congrArg (· 0) h; have e1 := congrArg (· 1) h
    simp only [hH, PiLp.add_apply, PiLp.sub_apply] at e0 e1
    exact nR1 (antipode x₁ x₂ x₃ O hO2 (by linarith) (by linarith))
  have hH2 : H ≠ x₂ := by
    intro h
    have e0 := congrArg (· 0) h; have e1 := congrArg (· 1) h
    simp only [hH, PiLp.add_apply, PiLp.sub_apply] at e0 e1
    exact nR2 (antipode x₂ x₁ x₃ O hO2.symm (by linarith) (by linarith))
  have hH3 : H ≠ x₃ := by
    intro h
    have e0 := congrArg (· 0) h; have e1 := congrArg (· 1) h
    simp only [hH, PiLp.add_apply, PiLp.sub_apply] at e0 e1
    exact nR3 (by linear_combination antipode x₃ x₁ x₂ O hO3.symm (by linarith) (by linarith))
  have f12a : d2 x₁ c12 = d2 x₂ c12 := by rw [d2_r1, d2_r2]; exact hO2.symm
  have f12b : d2 x₁ c12 = d2 H c12 := by rw [d2_r1, d2_h3]; exact hO23
  have f12c : d2 x₁ c12 = d2 x₁ O := by rw [d2_r1]; exact hO2.symm
  have f13a : d2 x₁ c13 = d2 x₃ c13 := by rw [d2_r1, d2_r2]; exact hO3.symm
  have f13b : d2 x₁ c13 = d2 H c13 := by rw [d2_r1, d2_h2]; exact hO23.symm
  have f13c : d2 x₁ c13 = d2 x₁ O := by rw [d2_r1]; exact hO3.symm
  have f23a : d2 x₂ c23 = d2 x₃ c23 := by rw [d2_r1, d2_r2]; exact hO23.symm
  have f23b : d2 x₂ c23 = d2 H c23 := by rw [d2_r1, d2_h1]; exact hO3.symm
  have f23c : d2 x₂ c23 = d2 x₁ O := by rw [d2_r1]; exact hO3.symm
  have hHO : d2 x₁ O ≠ d2 H O := by
    intro h
    have e : O = c12 := uniq x₁ x₂ H O c12 N1 hO2 h f12a f12b
    have e0 := congrArg (· 0) e; have e1 := congrArg (· 1) e
    simp only [hc12, PiLp.add_apply, PiLp.sub_apply] at e0 e1
    exact nR3 (by linear_combination antipode x₃ x₁ x₂ O hO3.symm (by linarith) (by linarith))
  refine ⟨H, ⟨?_, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hH1, hH2, hH3⟩
  · intro x hx y hy z hz hxy hyz hxz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
    apply not_col
    intro hc
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl | rfl <;>
      first
      | exact hxy rfl | exact hyz rfl | exact hxz rfl
      | exact N0 (by unfold cr at hc ⊢; linear_combination hc)
      | exact N0 (by unfold cr at hc ⊢; linear_combination -hc)
      | exact N1 (by unfold cr at hc ⊢; linear_combination hc)
      | exact N1 (by unfold cr at hc ⊢; linear_combination -hc)
      | exact N2 (by unfold cr at hc ⊢; linear_combination hc)
      | exact N2 (by unfold cr at hc ⊢; linear_combination -hc)
      | exact N3 (by unfold cr at hc ⊢; linear_combination hc)
      | exact N3 (by unfold cr at hc ⊢; linear_combination -hc)
  · intro T hT hcard hcos
    have hTP : T = {x₁, x₂, x₃, H} :=
      Set.eq_of_subset_of_ncard_le hT (by rw [hcard]; exact ncard4_le _ _ _ _)
    obtain ⟨z, r, hz⟩ := hcos
    rw [hTP] at hz
    have z1 := hz x₁ (by simp)
    have z2 := hz x₂ (by simp)
    have z3 := hz x₃ (by simp)
    have z4 := hz H (by simp)
    have e : z = O := uniq x₁ x₂ x₃ z O N0 (d2_of_dist (z1.trans z2.symm))
      (d2_of_dist (z1.trans z3.symm)) hO2 hO3
    subst e
    exact hHO (d2_of_dist (z1.trans z4.symm))
  · have hR : Erdos831.circleRadii ({x₁, x₂, x₃, H} : Set ℝ²) = {dist x₁ O} := by
      ext r
      simp only [Erdos831.circleRadii, Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨s, hs, rfl⟩
        have hfin : ({p ∈ ({x₁, x₂, x₃, H} : Set ℝ²) | p ∈ s}).Finite :=
          (Set.toFinite _).subset (fun p hp => hp.1)
        obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
          (Set.two_lt_ncard_iff hfin).mp (by omega)
        obtain ⟨haP, has⟩ := ha
        obtain ⟨hbP, hbs⟩ := hb
        obtain ⟨hcP, hcs⟩ := hc
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at haP hbP hcP
        rcases haP with ha | ha | ha | ha <;> rcases hbP with hb | hb | hb | hb <;>
          rcases hcP with hc | hc | hc | hc <;>
          rw [ha] at has hab hac <;> rw [hb] at hbs hab hbc <;> rw [hc] at hcs hac hbc <;>
          first
          | exact absurd rfl hab | exact absurd rfl hac | exact absurd rfl hbc
          | exact sphere_rad x₁ x₂ x₃ O N0 hO2 hO3 s (by assumption) (by assumption)
              (by assumption)
          | exact (sphere_rad x₁ x₂ H c12 N1 f12a f12b s (by assumption) (by assumption)
              (by assumption)).trans (dist_of_d2 f12c)
          | exact (sphere_rad x₁ x₃ H c13 N2 f13a f13b s (by assumption) (by assumption)
              (by assumption)).trans (dist_of_d2 f13c)
          | exact (sphere_rad x₂ x₃ H c23 N3 f23a f23b s (by assumption) (by assumption)
              (by assumption)).trans (dist_of_d2 f23c)
      · rintro rfl
        refine ⟨⟨O, dist x₁ O⟩, ?_, rfl⟩
        apply three_le _ _ x₁ x₂ x₃ h12 h13 h23 (by simp) (by simp) (by simp)
        · exact EuclideanGeometry.mem_sphere.mpr rfl
        · exact EuclideanGeometry.mem_sphere.mpr (dist_of_d2 hO2.symm)
        · exact EuclideanGeometry.mem_sphere.mpr (dist_of_d2 hO3.symm)
    rw [hR, Set.ncard_singleton]
  · rintro y ⟨hy, ⟨hNT, hNF⟩, hcard⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy
    obtain ⟨hy1, hy2, hy3⟩ := hy
    have M12 : cr x₁ x₂ y ≠ 0 :=
      cr_ne_of_not_col (hNT (by simp) (by simp) (by simp) h12 (Ne.symm hy2) (Ne.symm hy1))
    have M13 : cr x₁ x₃ y ≠ 0 :=
      cr_ne_of_not_col (hNT (by simp) (by simp) (by simp) h13 (Ne.symm hy3) (Ne.symm hy1))
    obtain ⟨r, hr⟩ := Set.ncard_eq_one.mp hcard
    have hRmem : dist x₁ O ∈ Erdos831.circleRadii ({x₁, x₂, x₃, y} : Set ℝ²) := by
      refine ⟨⟨O, dist x₁ O⟩, ?_, rfl⟩
      apply three_le _ _ x₁ x₂ x₃ h12 h13 h23 (by simp) (by simp) (by simp)
      · exact EuclideanGeometry.mem_sphere.mpr rfl
      · exact EuclideanGeometry.mem_sphere.mpr (dist_of_d2 hO2.symm)
      · exact EuclideanGeometry.mem_sphere.mpr (dist_of_d2 hO3.symm)
    rw [hr, Set.mem_singleton_iff] at hRmem
    have hcosp : ¬ d2 x₁ O = d2 y O := by
      intro h
      have h4 : ({x₁, x₂, x₃, y} : Set ℝ²).ncard = 4 := by
        rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hy3)]
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨h23, (Ne.symm hy2)⟩
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨h12, h13, (Ne.symm hy1)⟩
      apply hNF _ le_rfl h4
      refine ⟨O, dist x₁ O, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · rfl
      · exact dist_of_d2 hO2.symm
      · exact dist_of_d2 hO3.symm
      · exact dist_of_d2 h.symm
    have side : ∀ (b : ℝ²) (hb1 : x₁ ≠ b) (hbO : d2 x₁ O = d2 b O) (hby : b ≠ y)
        (hbmem : b ∈ ({x₁, x₂, x₃, y} : Set ℝ²)) (hcr : cr x₁ b y ≠ 0),
        d2 x₁ (x₁ + b - O) = d2 y (x₁ + b - O) := by
      intro b hb1 hbO hby hbmem hcr
      obtain ⟨c, hc1, hc2⟩ := circumcenter_ex x₁ b y hcr
      have hcmem : dist x₁ c ∈ Erdos831.circleRadii ({x₁, x₂, x₃, y} : Set ℝ²) := by
        refine ⟨⟨c, dist x₁ c⟩, ?_, rfl⟩
        apply three_le _ _ x₁ b y hb1 (Ne.symm hy1) hby (by simp) hbmem (by simp)
        · exact EuclideanGeometry.mem_sphere.mpr rfl
        · exact EuclideanGeometry.mem_sphere.mpr (dist_of_d2 hc1.symm)
        · exact EuclideanGeometry.mem_sphere.mpr (dist_of_d2 hc2.symm)
      rw [hr, Set.mem_singleton_iff, ← hRmem] at hcmem
      rcases two_centers x₁ b c O hb1 hc1 hbO (d2_of_dist hcmem) with e | e
      · subst e; exact absurd hc2 hcosp
      · rw [← e]; exact hc2
    have s12 := side x₂ h12 hO2 (Ne.symm hy2) (by simp) M12
    have s13 := side x₃ h13 hO3 (Ne.symm hy3) (by simp) M13
    have hcc : d2 x₁ (x₁ + x₃ - O) = d2 x₁ (x₁ + x₂ - O) := by
      rw [d2_r1, d2_r1]; exact hO3.symm.trans hO2
    rcases two_centers x₁ y (x₁ + x₃ - O) (x₁ + x₂ - O) (Ne.symm hy1) s13 s12 hcc with e | e
    · exfalso; apply h23
      have e0 := congrArg (· 0) e
      have e1 := congrArg (· 1) e
      simp only [PiLp.add_apply, PiLp.sub_apply] at e0 e1
      exact ext2 (by linarith) (by linarith)
    · have e0 := congrArg (· 0) e
      have e1 := congrArg (· 1) e
      simp only [PiLp.add_apply, PiLp.sub_apply] at e0 e1
      exact ext2 (by simp only [hH, PiLp.add_apply, PiLp.sub_apply]; linarith)
        (by simp only [hH, PiLp.add_apply, PiLp.sub_apply]; linarith)

end OMA831

theorem OMA.solution : type_of% @Erdos831.erdos_831.variants.szekeres := by
  intro x₁ x₂ x₃ hcol hright
  exact OMA831.main x₁ x₂ x₃ hcol hright
