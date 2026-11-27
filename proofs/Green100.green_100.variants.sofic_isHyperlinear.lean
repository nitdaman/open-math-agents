import FormalConjectures.GreensOpenProblems.«100»

-- Problem: Ben Green's Open Problem 100 — sofic isHyperlinear
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/100.lean:189 (declaration Green100.green_100.variants.sofic_isHyperlinear)
-- Credit: @niclorusso (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Hyperlinear

/-- The permutation matrix of `σ`: entry `(i, j)` is `1` iff `σ j = i`. -/
noncomputable def pm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if σ j = i then (1 : ℂ) else 0

lemma pm_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    pm σ i j = if σ j = i then (1 : ℂ) else 0 := rfl

lemma pm_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : pm (σ * τ) = pm σ * pm τ := by
  ext i j
  by_cases h : σ (τ j) = i <;> simp [pm_apply, Matrix.mul_apply, h]

lemma pm_one {n : ℕ} : pm (1 : Equiv.Perm (Fin n)) = 1 := by
  ext i j
  simp [pm_apply, Matrix.one_apply, eq_comm]

lemma star_pm {n : ℕ} (σ : Equiv.Perm (Fin n)) : star (pm σ) = pm σ⁻¹ := by
  ext i j
  rw [Matrix.star_apply, pm_apply, pm_apply]
  by_cases h : σ i = j
  · rw [if_pos h, if_pos (Equiv.Perm.inv_eq_iff_eq.mpr h.symm), star_one]
  · rw [if_neg h, if_neg (fun h' => h (Equiv.Perm.inv_eq_iff_eq.mp h').symm), star_zero]

lemma pm_mem {n : ℕ} (σ : Equiv.Perm (Fin n)) : pm σ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_pm, ← pm_mul, mul_inv_cancel, pm_one]

/-- The permutation matrix as an element of the unitary group. -/
noncomputable def U {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨pm σ, pm_mem σ⟩

lemma U_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : U (σ * τ) = U σ * U τ :=
  Subtype.ext (pm_mul σ τ)

lemma U_one {n : ℕ} : U (1 : Equiv.Perm (Fin n)) = 1 :=
  Subtype.ext pm_one

lemma col_sum {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (j : Fin n) :
    ∑ i, ‖pm σ i j - pm τ i j‖ ^ 2 = if σ j = τ j then (0 : ℝ) else 2 := by
  by_cases h : σ j = τ j
  · rw [if_pos h]
    simp [pm_apply, h]
  · rw [if_neg h]
    have key : ∀ i, ‖pm σ i j - pm τ i j‖ ^ 2 =
        (if σ j = i then (1 : ℝ) else 0) + (if τ j = i then (1 : ℝ) else 0) := by
      intro i
      by_cases h1 : σ j = i
      · by_cases h2 : τ j = i
        · exact absurd (h1.trans h2.symm) h
        · simp [pm_apply, h1, h2]
      · by_cases h2 : τ j = i
        · simp [pm_apply, h1, h2]
        · simp [pm_apply, h1, h2]
    rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    norm_num

lemma sum_sq {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    ∑ i, ∑ j, ‖pm σ i j - pm τ i j‖ ^ 2 = 2 * (hammingDist ⇑σ ⇑τ : ℝ) := by
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => col_sum σ τ j)]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
    mul_comm]
  rfl

lemma hsDist_U {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    Green100.hsDist (U σ) (U τ) = Real.sqrt (2 * Green100.hammingDistNorm σ τ) := by
  unfold Green100.hsDist Green100.hammingDistNorm
  change Real.sqrt ((∑ i, ∑ j, ‖pm σ i j - pm τ i j‖ ^ 2) / n) = _
  rw [sum_sq, mul_div_assoc]

lemma hdn_nonneg {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : 0 ≤ Green100.hammingDistNorm σ τ := by
  unfold Green100.hammingDistNorm
  positivity

lemma hsDist_U_lt {n : ℕ} (σ τ : Equiv.Perm (Fin n)) {ε : ℝ} (hε : 0 < ε)
    (h : Green100.hammingDistNorm σ τ < ε ^ 2 / 2) : Green100.hsDist (U σ) (U τ) < ε := by
  rw [hsDist_U]
  have h0 := hdn_nonneg σ τ
  calc Real.sqrt (2 * Green100.hammingDistNorm σ τ) < Real.sqrt (ε ^ 2) :=
        Real.sqrt_lt_sqrt (by positivity) (by linarith)
    _ = ε := Real.sqrt_sq hε.le

lemma hsDist_U_ge {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (h : (1 / 4 : ℝ) ≤ Green100.hammingDistNorm σ τ) :
    (1 / 4 : ℝ) ≤ Green100.hsDist (U σ) (U τ) := by
  rw [hsDist_U, Real.le_sqrt (by norm_num) (by linarith)]
  nlinarith

end OMA.Hyperlinear

open OMA.Hyperlinear in
theorem OMA.solution : type_of% @Green100.green_100.variants.sofic_isHyperlinear := by
  intro G _ hG
  unfold Green100.IsSofic at hG
  unfold Green100.IsHyperlinear
  intro F ε hε
  obtain ⟨n, θ, h1, h2, h3⟩ := hG F (ε ^ 2 / 2) (by positivity)
  refine ⟨n, fun g => U (θ g), ?_, ?_, ?_⟩
  · intro g hg h hh hgh
    show Green100.hsDist (U (θ g) * U (θ h)) (U (θ (g * h))) < ε
    rw [← U_mul]
    exact hsDist_U_lt _ _ hε (h1 g hg h hh hgh)
  · intro h1F
    show Green100.hsDist (U (θ 1)) 1 < ε
    rw [← U_one]
    exact hsDist_U_lt _ _ hε (h2 h1F)
  · intro x hx y hy hxy
    exact hsDist_U_ge _ _ (h3 x hx y hy hxy)
