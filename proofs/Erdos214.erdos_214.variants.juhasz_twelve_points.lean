import FormalConjectures.ErdosProblems.«214»

-- Problem: Erdős Problem 214 — juhasz twelve points
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/214.lean:90 (declaration Erdos214.erdos_214.variants.juhasz_twelve_points)
-- Credit: @mucoucah (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-
Construction. S is the union of the open disks of radius 1/2 centred at the points
(2a+b, 7b/4), a b integers. Distinct centres are at distance at least 2, so S has no two
points at distance 1. Every point of the plane is within distance sqrt(27/20) of a centre.
K is a 4 x 3 grid of 12 points whose open 1/2-disks cover the disk of radius sqrt(27/20)
about the midpoint of K 0 and K 1. A congruent copy of K (same pairwise distances) is
an isometric image of K, so the copy also has a point within distance 1/2 of the centre
closest to the image of that midpoint, i.e. a point of S.
-/

open scoped EuclideanGeometry Congruent

namespace OMA214

lemma sign_lemma {ι : Type*} (C C' : ι → ℝ) (hC : ∀ i j, C i * C j = C' i * C' j) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧ ∀ i, C i = σ * C' i := by
  by_cases h : ∀ i, C' i = 0
  · refine ⟨1, by norm_num, fun i => ?_⟩
    have := hC i i
    rw [h i] at this ⊢
    have h2 : C i ^ 2 = 0 := by nlinarith
    simpa using h2
  · simp only [not_forall] at h
    obtain ⟨r, hr⟩ := h
    have hrr := hC r r
    refine ⟨C r / C' r, ?_, fun i => ?_⟩
    · rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 2 hr)]
      linear_combination hrr
    · have hir := hC i r
      have hz : C' r * (C i * C' r - C r * C' i) = 0 := by
        linear_combination (-C i) * hrr + C r * hir
      rcases mul_eq_zero.mp hz with h0 | h0
      · exact absurd h0 hr
      · rw [div_mul_eq_mul_div, eq_div_iff hr]
        linear_combination h0

lemma alg_step (D1 D2 P1 P2 Q1 Q2 w1 w2 W1 W2 σ k0x k0y kix kiy lx ly pix piy : ℝ)
    (hs : w1 ^ 2 + w2 ^ 2 = W1 ^ 2 + W2 ^ 2) (hne : W1 ^ 2 + W2 ^ 2 ≠ 0) (hσ2 : σ ^ 2 = 1)
    (hA : P1 * w1 + P2 * w2 = Q1 * W1 + Q2 * W2) (hC : P1 * w2 - P2 * w1 = σ * (Q1 * W2 - Q2 * W1))
    (hQ1 : kix = k0x + Q1) (hQ2 : kiy = k0y + Q2) (hD1 : lx - pix = D1 - P1)
    (hD2 : ly - piy = D2 - P2) :
    (k0x + ((D1 * w1 + D2 * w2) * W1 + σ * (D1 * w2 - D2 * w1) * W2) / (W1 ^ 2 + W2 ^ 2) - kix) ^ 2
      + (k0y + ((D1 * w1 + D2 * w2) * W2 - σ * (D1 * w2 - D2 * w1) * W1) / (W1 ^ 2 + W2 ^ 2)
        - kiy) ^ 2 = (lx - pix) ^ 2 + (ly - piy) ^ 2 := by
  rw [hD1, hD2, hQ1, hQ2]
  have e1 : (W1 ^ 2 + W2 ^ 2) * ((k0x + ((D1 * w1 + D2 * w2) * W1 + σ * (D1 * w2 - D2 * w1) * W2)
        / (W1 ^ 2 + W2 ^ 2) - (k0x + Q1)) ^ 2
      + (k0y + ((D1 * w1 + D2 * w2) * W2 - σ * (D1 * w2 - D2 * w1) * W1) / (W1 ^ 2 + W2 ^ 2)
        - (k0y + Q2)) ^ 2)
      = ((D1 * w1 + D2 * w2) - (Q1 * W1 + Q2 * W2)) ^ 2
        + (σ * (D1 * w2 - D2 * w1) - (Q1 * W2 - Q2 * W1)) ^ 2 := by
    field_simp
    ring
  have e2 : (W1 ^ 2 + W2 ^ 2) * ((D1 - P1) ^ 2 + (D2 - P2) ^ 2)
      = ((D1 * w1 + D2 * w2) - (P1 * w1 + P2 * w2)) ^ 2
        + ((D1 * w2 - D2 * w1) - (P1 * w2 - P2 * w1)) ^ 2 := by
    rw [← hs]
    ring
  have e3 : ((D1 * w2 - D2 * w1) - (P1 * w2 - P2 * w1)) ^ 2
      = (σ * (D1 * w2 - D2 * w1) - (Q1 * W2 - Q2 * W1)) ^ 2 := by
    rw [hC]
    linear_combination ((Q1 * W2 - Q2 * W1) ^ 2 - (D1 * w2 - D2 * w1) ^ 2) * hσ2
  apply mul_left_cancel₀ hne
  rw [e1, e2, e3, hA]

lemma transfer {ι : Type*} (px py kx ky : ι → ℝ) (i0 i1 : ι)
    (hd : ∀ i j, (px i - px j) ^ 2 + (py i - py j) ^ 2 = (kx i - kx j) ^ 2 + (ky i - ky j) ^ 2)
    (hne : (kx i1 - kx i0) ^ 2 + (ky i1 - ky i0) ^ 2 ≠ 0) (lx ly : ℝ) :
    ∃ zx zy : ℝ, ∀ i, (zx - kx i) ^ 2 + (zy - ky i) ^ 2 = (lx - px i) ^ 2 + (ly - py i) ^ 2 := by
  have hs : (px i1 - px i0) ^ 2 + (py i1 - py i0) ^ 2 = (kx i1 - kx i0) ^ 2 + (ky i1 - ky i0) ^ 2 :=
    hd i1 i0
  have hA : ∀ i, (px i - px i0) * (px i1 - px i0) + (py i - py i0) * (py i1 - py i0)
      = (kx i - kx i0) * (kx i1 - kx i0) + (ky i - ky i0) * (ky i1 - ky i0) := by
    intro i
    have h1 := hd i i0
    have h2 := hd i i1
    linear_combination (h1 + hs - h2) / 2
  have hC : ∀ i j, ((px i - px i0) * (py i1 - py i0) - (py i - py i0) * (px i1 - px i0)) *
        ((px j - px i0) * (py i1 - py i0) - (py j - py i0) * (px i1 - px i0))
      = ((kx i - kx i0) * (ky i1 - ky i0) - (ky i - ky i0) * (kx i1 - kx i0)) *
        ((kx j - kx i0) * (ky i1 - ky i0) - (ky j - ky i0) * (kx i1 - kx i0)) := by
    intro i j
    have hAi := hA i
    have hAj := hA j
    have h1 := hd i i0
    have h2 := hd j i0
    have h3 := hd i j
    linear_combination ((px i1 - px i0) ^ 2 + (py i1 - py i0) ^ 2) * (h1 + h2 - h3) / 2
      + (((kx i - kx i0) * (kx j - kx i0) + (ky i - ky i0) * (ky j - ky i0))) * hs
      - ((px i - px i0) * (px i1 - px i0) + (py i - py i0) * (py i1 - py i0)) * hAj
      - ((kx j - kx i0) * (kx i1 - kx i0) + (ky j - ky i0) * (ky i1 - ky i0)) * hAi
  obtain ⟨σ, hσ2, hσ⟩ := sign_lemma
    (fun i => (px i - px i0) * (py i1 - py i0) - (py i - py i0) * (px i1 - px i0))
    (fun i => (kx i - kx i0) * (ky i1 - ky i0) - (ky i - ky i0) * (kx i1 - kx i0)) hC
  exact ⟨_, _, fun i => alg_step (lx - px i0) (ly - py i0) (px i - px i0) (py i - py i0)
    (kx i - kx i0) (ky i - ky i0) (px i1 - px i0) (py i1 - py i0) (kx i1 - kx i0) (ky i1 - ky i0)
    σ (kx i0) (ky i0) (kx i) (ky i) (lx) (ly) (px i) (py i) hs hne hσ2 (hA i) (hσ i)
    (by ring) (by ring) (by ring) (by ring)⟩

lemma core (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (_hv1 : v ≤ 1)
    (h : 2 * u + 49 / 8 * v ≤ 65 / 16) : u ^ 2 + 49 / 16 * v ^ 2 ≤ 27 / 20 := by
  nlinarith [mul_nonneg hu0 (sub_nonneg.2 hu1), mul_nonneg hv0 (sub_nonneg.2 h),
    mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h), mul_nonneg hu0 hv0,
    mul_nonneg (sub_nonneg.2 hu1) hv0]

lemma core2 (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    u ^ 2 + 49 / 16 * v ^ 2 ≤ 27 / 20 ∨ (1 - u) ^ 2 + 49 / 16 * (1 - v) ^ 2 ≤ 27 / 20 := by
  rcases le_total (2 * u + 49 / 8 * v) (65 / 16) with h | h
  · exact Or.inl (core u v hu0 hu1 hv0 hv1 h)
  · right
    exact core (1 - u) (1 - v) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)

lemma lattice_cover (qx qy : ℝ) :
    ∃ a b : ℤ, (qx - (2 * (a : ℝ) + b)) ^ 2 + (qy - 7 / 4 * (b : ℝ)) ^ 2 ≤ 27 / 20 := by
  set b0 : ℤ := ⌊4 * qy / 7⌋ with hb0
  have hv0 : (b0 : ℝ) ≤ 4 * qy / 7 := Int.floor_le _
  have hv1 : 4 * qy / 7 < b0 + 1 := Int.lt_floor_add_one _
  set a0 : ℤ := ⌊(qx - b0) / 2⌋ with ha0
  have hh0 : (a0 : ℝ) ≤ (qx - b0) / 2 := Int.floor_le _
  have hh1 : (qx - b0) / 2 < a0 + 1 := Int.lt_floor_add_one _
  set v : ℝ := 4 * qy / 7 - b0 with hv
  set h : ℝ := qx - b0 - 2 * a0 with hh
  have ey0 : qy - 7 / 4 * (b0 : ℝ) = 7 / 4 * v := by rw [hv]; ring
  have ey1 : qy - 7 / 4 * ((b0 + 1 : ℤ) : ℝ) = -(7 / 4 * (1 - v)) := by rw [hv]; push_cast; ring
  rcases le_total h 1 with hle | hle
  · rcases core2 h v (by linarith) hle (by linarith) (by linarith) with hc | hc
    · refine ⟨a0, b0, ?_⟩
      have ex : qx - (2 * (a0 : ℝ) + b0) = h := by rw [hh]; ring
      rw [ex, ey0]
      nlinarith [hc]
    · refine ⟨a0, b0 + 1, ?_⟩
      have ex : qx - (2 * (a0 : ℝ) + ((b0 + 1 : ℤ) : ℝ)) = -(1 - h) := by rw [hh]; push_cast; ring
      rw [ex, ey1]
      nlinarith [hc]
  · rcases core2 (2 - h) v (by linarith) (by linarith) (by linarith) (by linarith) with hc | hc
    · refine ⟨a0 + 1, b0, ?_⟩
      have ex : qx - (2 * ((a0 + 1 : ℤ) : ℝ) + b0) = -(2 - h) := by rw [hh]; push_cast; ring
      rw [ex, ey0]
      nlinarith [hc]
    · refine ⟨a0, b0 + 1, ?_⟩
      have ex : qx - (2 * (a0 : ℝ) + ((b0 + 1 : ℤ) : ℝ)) = (1 - (2 - h)) := by
        rw [hh]; push_cast; ring
      rw [ex, ey1]
      nlinarith [hc]

lemma lattice_sep_int (da db : ℤ) (h : da ≠ 0 ∨ db ≠ 0) :
    64 ≤ 16 * (2 * da + db) ^ 2 + 49 * db ^ 2 := by
  have hc : db = 0 ∨ db = 1 ∨ db = -1 ∨ 2 ≤ db ∨ db ≤ -2 := by omega
  rcases hc with hc | hc | hc | hc | hc
  · subst hc
    have : da ≤ -1 ∨ 1 ≤ da := by omega
    rcases this with h2 | h2 <;> nlinarith
  · subst hc
    have : 2 * da + 1 ≤ -1 ∨ 1 ≤ 2 * da + 1 := by omega
    rcases this with h2 | h2 <;> nlinarith
  · subst hc
    have : 2 * da + -1 ≤ -1 ∨ 1 ≤ 2 * da + -1 := by omega
    rcases this with h2 | h2 <;> nlinarith
  · nlinarith [sq_nonneg (2 * da + db)]
  · nlinarith [sq_nonneg (2 * da + db)]

def X : Fin 12 → ℤ := ![-15, 15, -45, 45, -15, 15, -45, 45, -15, 15, -45, 45]
def Y : Fin 12 → ℤ := ![0, 0, 0, 0, 39, 39, 39, 39, -39, -39, -39, -39]

lemma XY_inj : ∀ i j : Fin 12, X i = X j → Y i = Y j → i = j := by decide

lemma cover (zx zy : ℝ) (h : zx ^ 2 + zy ^ 2 ≤ 27 / 20) :
    ∃ i : Fin 12, (zx - (X i : ℝ) / 50) ^ 2 + (zy - (Y i : ℝ) / 50) ^ 2 < 1 / 4 := by
  have hx1 : zx ≤ 117 / 100 := by nlinarith [sq_nonneg zy, sq_nonneg (zx - 117/100)]
  have hx2 : -117 / 100 ≤ zx := by nlinarith [sq_nonneg zy, sq_nonneg (zx + 117/100)]
  have hy1 : zy ≤ 117 / 100 := by nlinarith [sq_nonneg zx, sq_nonneg (zy - 117/100)]
  have hy2 : -117 / 100 ≤ zy := by nlinarith [sq_nonneg zx, sq_nonneg (zy + 117/100)]
  have bx : ∃ x : ℝ, (x = -45/50 ∨ x = -15/50 ∨ x = 15/50 ∨ x = 45/50) ∧ (zx - x) ^ 2 ≤ 9 / 100 := by
    rcases le_total zx (-6/10) with c1 | c1
    · exact ⟨-45/50, by norm_num, by nlinarith⟩
    rcases le_total zx 0 with c2 | c2
    · exact ⟨-15/50, by norm_num, by nlinarith⟩
    rcases le_total zx (6/10) with c3 | c3
    · exact ⟨15/50, by norm_num, by nlinarith⟩
    · exact ⟨45/50, by norm_num, by nlinarith⟩
  have by' : ∃ y : ℝ, (y = -39/50 ∨ y = 0 ∨ y = 39/50) ∧ (zy - y) ^ 2 ≤ 1521 / 10000 := by
    rcases le_total zy (-39/100) with c1 | c1
    · exact ⟨-39/50, by norm_num, by nlinarith⟩
    rcases le_total zy (39/100) with c2 | c2
    · exact ⟨0, by norm_num, by nlinarith⟩
    · exact ⟨39/50, by norm_num, by nlinarith⟩
  obtain ⟨x, hx, hxb⟩ := bx
  obtain ⟨y, hy, hyb⟩ := by'
  have hlt : (zx - x) ^ 2 + (zy - y) ^ 2 < 1 / 4 := by linarith
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact ⟨10, by simp [X, Y]; norm_num at hlt ⊢; linarith⟩
  · exact ⟨2, by simp [X, Y]; norm_num at hlt ⊢; linarith⟩
  · exact ⟨6, by simp [X, Y]; norm_num at hlt ⊢; linarith⟩
  · exact ⟨8, by simp [X, Y]; norm_num at hlt ⊢; linarith⟩
  · exact ⟨0, by simp [X, Y]; norm_num at hlt ⊢; linarith⟩
  · exact ⟨4, by simp [X, Y]; norm_num at hlt ⊢; linarith⟩
  · exact ⟨9, by simp [X, Y]; norm_num at hlt ⊢; linarith⟩
  · exact ⟨1, by simp [X, Y]; norm_num at hlt ⊢; linarith⟩
  · exact ⟨5, by simp [X, Y]; norm_num at hlt ⊢; linarith⟩
  · exact ⟨11, by simp [X, Y]; norm_num at hlt ⊢; linarith⟩
  · exact ⟨3, by simp [X, Y]; norm_num at hlt ⊢; linarith⟩
  · exact ⟨7, by simp [X, Y]; norm_num at hlt ⊢; linarith⟩

noncomputable def L (a b : ℤ) : ℝ² := !₂[2 * (a : ℝ) + b, 7 / 4 * (b : ℝ)]

def S : Set ℝ² := {x | ∃ a b : ℤ, dist x (L a b) < 1 / 2}

noncomputable def K (i : Fin 12) : ℝ² := !₂[(X i : ℝ) / 50, (Y i : ℝ) / 50]

lemma dist_sq (x y : ℝ²) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

lemma L_sep (a b a' b' : ℤ) (h : (a, b) ≠ (a', b')) : 2 ≤ dist (L a b) (L a' b') := by
  have h1 : a - a' ≠ 0 ∨ b - b' ≠ 0 := by
    by_contra hc
    simp only [not_or, not_not] at hc
    apply h
    have e1 : a = a' := by omega
    have e2 : b = b' := by omega
    rw [e1, e2]
  have h2 := lattice_sep_int (a - a') (b - b') h1
  have h2' : (64 : ℝ) ≤ 16 * (2 * ((a : ℝ) - a') + ((b : ℝ) - b')) ^ 2 + 49 * ((b : ℝ) - b') ^ 2 := by
    exact_mod_cast h2
  have h3 : dist (L a b) (L a' b') ^ 2
      = (2 * (a : ℝ) + b - (2 * a' + b')) ^ 2 + (7 / 4 * (b : ℝ) - 7 / 4 * b') ^ 2 := by
    rw [dist_sq]
    simp [L]
  have h4 : (4 : ℝ) ≤ dist (L a b) (L a' b') ^ 2 := by
    rw [h3]
    nlinarith
  nlinarith [dist_nonneg (x := L a b) (y := L a' b')]

lemma S_avoid : Erdos214.UnitDistanceAvoiding S := by
  intro x hx y hy hxy
  obtain ⟨a, b, hab⟩ := hx
  obtain ⟨a', b', hab'⟩ := hy
  by_cases he : (a, b) = (a', b')
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := dist_triangle_right x y (L a b)
    linarith
  · have h2 := L_sep a b a' b' he
    have t1 := dist_triangle (L a b) x (L a' b')
    have t2 := dist_triangle x y (L a' b')
    rw [dist_comm] at hab
    linarith

lemma K_inj : Function.Injective K := by
  intro i j h
  have h0 := congrArg (fun v : ℝ² => v 0) h
  have h1 := congrArg (fun v : ℝ² => v 1) h
  simp [K] at h0 h1
  exact XY_inj i j h0 h1

lemma main (p : Fin 12 → ℝ²) (hpS : ∀ i, p i ∈ Sᶜ) (hc : p ≅ K) : False := by
  have hd : ∀ i j, (p i 0 - p j 0) ^ 2 + (p i 1 - p j 1) ^ 2
      = (K i 0 - K j 0) ^ 2 + (K i 1 - K j 1) ^ 2 := by
    intro i j
    rw [← dist_sq, ← dist_sq, (congruent_iff_dist_eq.mp hc) i j]
  have hK0 : K 0 0 = -15 / 50 ∧ K 0 1 = 0 := by simp [K, X, Y]
  have hK1 : K 1 0 = 15 / 50 ∧ K 1 1 = 0 := by simp [K, X, Y]
  have hne : (K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2 ≠ 0 := by
    rw [hK0.1, hK0.2, hK1.1, hK1.2]
    norm_num
  obtain ⟨a, b, hab⟩ := lattice_cover ((p 0 0 + p 1 0) / 2) ((p 0 1 + p 1 1) / 2)
  obtain ⟨zx, zy, hz⟩ := transfer (fun i => p i 0) (fun i => p i 1) (fun i => K i 0)
    (fun i => K i 1) 0 1 hd hne (2 * (a : ℝ) + b) (7 / 4 * (b : ℝ))
  have hz0 := hz 0
  have hz1 := hz 1
  have h01 := hd 0 1
  simp only at hz0 hz1
  rw [hK0.1, hK0.2] at hz0
  rw [hK1.1, hK1.2] at hz1
  rw [hK0.1, hK0.2, hK1.1, hK1.2] at h01
  have hzr : zx ^ 2 + zy ^ 2 ≤ 27 / 20 := by nlinarith
  obtain ⟨i, hi⟩ := cover zx zy hzr
  have hzi := hz i
  have hKi : K i 0 = (X i : ℝ) / 50 ∧ K i 1 = (Y i : ℝ) / 50 := by simp [K]
  simp only at hzi
  rw [hKi.1, hKi.2] at hzi
  apply hpS i
  refine ⟨a, b, ?_⟩
  have hdl : dist (p i) (L a b) ^ 2 < 1 / 4 := by
    rw [dist_sq]
    simp only [L]
    simp
    nlinarith
  nlinarith [dist_nonneg (x := p i) (y := L a b)]

end OMA214

theorem OMA.solution : type_of% @Erdos214.erdos_214.variants.juhasz_twelve_points := by
  intro hR
  obtain ⟨p, hpS, hc⟩ := hR OMA214.S OMA214.S_avoid OMA214.K OMA214.K_inj
  exact OMA214.main p hpS hc
