import FormalConjectures.ErdosProblems.«1121»

/-!
A nonseparable family of balls is covered by the ball of total radius about its
radius-weighted center. We first bound the right endpoints of its projections.
-/

-- Problem: Erdős Problem 1121 — higher dimension
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1121.lean:64 (declaration Erdos1121.erdos_1121.variants.higher_dimension)
-- Credit: @vkascheev (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open MeasureTheory
open scoped BigOperators

namespace Erdos1121Cover

/-- The intervals ending beyond the right endpoint of interval `i` cover the gap
from that endpoint to the right endpoint of interval `j`. -/
lemma endpoint_gap {n : ℕ} (t r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hcut : ∀ x : ℝ, (∀ k, x ∉ Set.Icc (t k - r k) (t k + r k)) →
      (∀ k, t k < x) ∨ (∀ k, x < t k)) (i j : Fin n) :
    (t j + r j) - (t i + r i) ≤
      ∑ k ∈ Finset.univ.filter (fun k => t i + r i < t k + r k), 2 * r k := by
  classical
  let b (k : Fin n) := t k + r k
  let I (k : Fin n) := Set.Icc (t k - r k) (b k)
  let s := Finset.univ.filter (fun k => b i < b k)
  change b j - b i ≤ ∑ k ∈ s, 2 * r k
  have hcover : Set.Ioc (b i) (b j) ⊆ ⋃ k ∈ s, I k := by
    intro x hx
    have hhit : ∃ k, x ∈ I k := by
      by_contra h
      have hall : ∀ k, x ∉ I k := fun k hk => h ⟨k, hk⟩
      rcases hcut x hall with hleft | hright
      · exact hall j ⟨(sub_le_self _ (hr j)).trans (hleft j).le, hx.2⟩
      · have hi : t i ≤ b i := le_add_of_nonneg_right (hr i)
        exact (not_lt_of_ge (hi.trans hx.1.le)) (hright i)
    obtain ⟨k, hk⟩ := hhit
    have hks : k ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.1.trans_le hk.2⟩
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hks, hk⟩⟩
  have hlen (k : Fin n) : volume (I k) = ENNReal.ofReal (2 * r k) := by
    dsimp [I, b]
    rw [Real.volume_Icc]
    congr 1
    ring
  have hn (k : Fin n) (_ : k ∈ s) : 0 ≤ 2 * r k := mul_nonneg (by norm_num) (hr k)
  apply (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg hn)).mp
  rw [ENNReal.ofReal_sum_of_nonneg hn]
  calc
    ENNReal.ofReal (b j - b i) = volume (Set.Ioc (b i) (b j)) := Real.volume_Ioc.symm
    _ ≤ volume (⋃ k ∈ s, I k) := measure_mono hcover
    _ ≤ ∑ k ∈ s, volume (I k) := measure_biUnion_finset_le s I
    _ = ∑ k ∈ s, ENNReal.ofReal (2 * r k) := by simp only [hlen]

/-- Every right endpoint is at most one total radius above the weighted mean. -/
lemma weighted_endpoint {n : ℕ} (t r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hcut : ∀ x : ℝ, (∀ k, x ∉ Set.Icc (t k - r k) (t k + r k)) →
      (∀ k, t k < x) ∨ (∀ k, x < t k)) (j : Fin n) :
    (∑ i, r i) * (t j + r j) ≤ (∑ i, r i * t i) + (∑ i, r i) ^ 2 := by
  classical
  let b (i : Fin n) := t i + r i
  -- The diagonal contributes once. Each interval ending later contributes its full length.
  let A (i k : Fin n) := (if k = i then r i * r k else 0) +
    (if b i < b k then r i * (2 * r k) else 0)
  have row (i : Fin n) : r i * (b j - t i) ≤ ∑ k, A i k := by
    let s := Finset.univ.filter (fun k => b i < b k)
    have hgap : b j - b i ≤ ∑ k ∈ s, 2 * r k := endpoint_gap t r hr hcut i j
    have hi : b j - t i ≤ r i + ∑ k ∈ s, 2 * r k := by
      change b j - (t i + r i) ≤ _ at hgap
      linarith only [hgap]
    calc
      r i * (b j - t i) ≤ r i * (r i + ∑ k ∈ s, 2 * r k) :=
        mul_le_mul_of_nonneg_left hi (hr i)
      _ = ∑ k, A i k := by
        simp [s, A, Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.sum_filter, mul_ite]
  have hpair (i k : Fin n) : A i k + A k i ≤ 2 * (r i * r k) := by
    by_cases he : i = k
    · subst k
      simp [A] <;> exact le_of_eq (by ring)
    by_cases hik : b i < b k
    · simp [A, he, Ne.symm he, hik, not_lt.mpr hik.le] <;> exact le_of_eq (by ring)
    by_cases hki : b k < b i
    · simp [A, he, Ne.symm he, hik, hki] <;> exact le_of_eq (by ring)
    · have hpos := mul_nonneg (hr i) (hr k)
      simp [A, he, Ne.symm he, hik, hki] <;> linarith only [hpos]
  have htotal : (∑ i, ∑ k, A i k) ≤ (∑ i, r i) ^ 2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) fun k _ => hpair i k
    have hswap : (∑ i, ∑ k, A k i) = ∑ i, ∑ k, A i k := Finset.sum_comm
    simp only [Finset.sum_add_distrib] at hh
    rw [hswap] at hh
    have hprod : (∑ i, ∑ k, 2 * (r i * r k)) = 2 * (∑ i, r i) ^ 2 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, sq]
    rw [hprod] at hh
    linarith only [hh]
  have hh := (Finset.sum_le_sum (s := Finset.univ) fun i _ => row i).trans htotal
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hh
  change (∑ i, r i) * b j ≤ _
  linarith only [hh]

lemma project_ball {d : ℕ} {v c p : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hv : ‖v‖ = 1) (hp : p ∈ Metric.closedBall c r) :
    inner ℝ v p ∈ Set.Icc (inner ℝ v c - r) (inner ℝ v c + r) := by
  have h := abs_real_inner_le_norm v (p - c)
  rw [hv, one_mul, inner_sub_right] at h
  have hd : ‖p - c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hp
  obtain ⟨hl, hu⟩ := abs_le.mp (h.trans hd)
  exact ⟨by linarith only [hl], by linarith only [hu]⟩

end Erdos1121Cover

theorem OMA.solution : type_of% @Erdos1121.erdos_1121.variants.higher_dimension := by
  classical
  intro d n c r hr hsep
  let R := ∑ i, r i
  let z := R⁻¹ • ∑ i, r i • c i
  refine ⟨z, ?_⟩
  intro p hp
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
  have hrj : r j ≤ R := Finset.single_le_sum (fun i _ => (hr i).le) (Finset.mem_univ j)
  have hR : 0 < R := (hr j).trans_le hrj
  rw [Metric.mem_closedBall, dist_eq_norm]
  change ‖p - z‖ ≤ R
  by_cases heq : p - z = 0
  · simpa only [heq, norm_zero] using hR.le
  let v := (‖p - z‖⁻¹ : ℝ) • (p - z)
  have hv : ‖v‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) heq
  have hv0 : v ≠ 0 := by
    intro h
    simp [h] at hv
  let t (i : Fin n) := inner ℝ v (c i)
  have hcut : ∀ x : ℝ, (∀ k, x ∉ Set.Icc (t k - r k) (t k + r k)) →
      (∀ k, t k < x) ∨ (∀ k, x < t k) := by
    intro x hx
    apply hsep v x hv0
    intro i q hq he
    apply hx i
    rw [← he]
    exact Erdos1121Cover.project_ball hv hq
  have hend := Erdos1121Cover.weighted_endpoint t r (fun i => (hr i).le) hcut j
  have hpj : inner ℝ v p ≤ t j + r j := (Erdos1121Cover.project_ball hv hj).2
  have hbound : R * inner ℝ v p ≤ (∑ i, r i * t i) + R ^ 2 :=
    (mul_le_mul_of_nonneg_left hpj hR.le).trans hend
  have hz : R * inner ℝ v z = ∑ i, r i * t i := by
    dsimp only [z]
    rw [real_inner_smul_right, inner_sum]
    simp only [real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, t]
  have hdir : inner ℝ v (p - z) = ‖p - z‖ := by
    dsimp only [v]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [sq, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr heq), one_mul]
  rw [← hdir, inner_sub_right]
  apply (mul_le_mul_iff_right₀ hR).mp
  linarith only [hbound, hz]
