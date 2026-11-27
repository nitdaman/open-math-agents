import OMAReductions.R_RiemannZetaValues_apery_central_binomial_series_R1

/-! # A uniform bound on the boundary of the WZ triangle -/
-- Credit: @steveDOTdigital

open Filter Topology Finset
namespace OMA.AperyTail
private theorem fact_le (a b : ℕ) : a.factorial * b.factorial ≤ (a+b).factorial :=
  Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
private theorem bound {N k : ℕ} (h : k < N) :
    N*(N+1)*k.factorial^2*(N-k-1).factorial ≤ (N+k+1).factorial := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show N ≠ 0 by omega)
  have h₁ := fact_le k (m-k)
  rw [show k+(m-k)=m by omega] at h₁
  have h₂ := fact_le (m+2) k
  rw [show m+2+k=m+1+k+1 by omega] at h₂
  apply le_trans _ h₂
  rw [Nat.factorial_succ (m+1), Nat.factorial_succ m]
  rw [show m.succ-k-1=m-k by omega]
  calc
    _ = ((m+1)*(m+2)*k.factorial)*(k.factorial*(m-k).factorial) := by simp only [Nat.succ_eq_add_one]; ring
    _ ≤ ((m+1)*(m+2)*k.factorial)*m.factorial := Nat.mul_le_mul_left _ h₁
    _ = _ := by ring

theorem vanish : OMA.R_RiemannZetaValues_apery_central_binomial_series_R1.H2 := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let F (k : ℕ) := (-1 : ℂ)^k * (k.factorial : ℂ)^2 * ((N-k-1).factorial : ℂ) /
      (((N+k+1).factorial : ℂ) * (k+1))
  change ‖∑ k ∈ range N, F k‖ ≤ _
  calc
    _ ≤ ∑ k ∈ range N, ‖F k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range N, 1/((N : ℝ)*(N+1)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hh := bound (mem_range.mp hk)
      have hcast : (N : ℝ)*(N+1)*(k.factorial : ℝ)^2*((N-k-1).factorial : ℝ) ≤ (N+k+1).factorial := by exact_mod_cast hh
      have hkn : ‖(k : ℂ)+1‖ = (k : ℝ)+1 := by exact_mod_cast Complex.norm_natCast (k+1)
      rw [show ‖F k‖ = (k.factorial : ℝ)^2 * ((N-k-1).factorial : ℝ) / (((N+k+1).factorial : ℝ) * (k+1)) by simp [F,norm_pow,hkn]]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg (show 0 ≤ ((N+k+1).factorial : ℝ) by positivity) (Nat.cast_nonneg (α := ℝ) k)]
    _ = _ := by simp; field_simp
end OMA.AperyTail

theorem OMA.solution : OMA.R_RiemannZetaValues_apery_central_binomial_series_R1.H2 := OMA.AperyTail.vanish
