import OMAReductions.R_Erdos442_erdos_442_variants_tao_R1_H2_R1
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-! A finite Euler product bounds the harmonic sum and gives the needed prime reciprocal mass. -/

-- Step Erdos442.erdos_442.variants.tao.R1.H2.R1.H1: hypothesis H1 of reduction Erdos442.erdos_442.variants.tao.R1.H2.R1
-- Credit: @dk8827
-- H1 := ∀ t : ℕ → ℝ, (∀ k, t k = Real.exp (Real.exp ((k : ℝ) ^ 2))) →     ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,       ∃ k : ℕ, 1 ≤ k ∧ t k < x ∧ x ≤ t (k + 1) ∧         let a := ∑ p ∈ Nat.primesLE ⌊t k⌋₊, (1 : ℝ) / p         2 * (k : ℝ) ≤ a ∧ c * (k : ℝ) ^ 2 ≤ a  /-- The lower reciprocal-mass estimate for Tao's explicit set, in terms of the small-prime reciprocal mass and the additional contribution of one large prime. -/

open Filter
open scoped BigOperators

lemma log_le_exp_prime_reciprocal_sum (N : ℕ) :
    Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.exp (2 * (∑ p ∈ N.primesLE, (1 : ℝ) / p)) := by
  classical
  let f : ℕ →* ℝ := {
    toFun := fun n => (1 : ℝ) / n
    map_one' := by simp
    map_mul' := by intro n m; simp [Nat.cast_mul, one_div, mul_comm] }
  have hnorm {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(1 : ℝ) / p‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hp' : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    exact (div_lt_one hp').mpr (by exact_mod_cast hp.one_lt)
  obtain ⟨hs, hsum⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric (f := f) hnorm (N + 1)
  let s := Finset.Icc 1 N
  let e : ↥s ↪ (N + 1).smoothNumbers :=
    ⟨fun n => ⟨n.val, Nat.mem_smoothNumbers_of_lt (Finset.mem_Icc.mp n.property).1
      (Nat.lt_succ_of_le (Finset.mem_Icc.mp n.property).2)⟩,
    fun a b h => Subtype.ext (congrArg (fun n : (N + 1).smoothNumbers => n.val) h)⟩
  have hpart : (∑ n ∈ s, (1 : ℝ) / n) ≤ ∏ p ∈ (N + 1).primesBelow, (1 - f p)⁻¹ := by
    rw [← hsum.tsum_eq]
    have hle : (∑ n ∈ s.attach.map e, f n) ≤ ∑' n : (N + 1).smoothNumbers, f n :=
      hs.of_norm.sum_le_tsum _ (fun _ _ => by change 0 ≤ (1 : ℝ) / _; positivity)
    rw [Finset.sum_map] at hle
    change (∑ n ∈ s.attach, (1 : ℝ) / (n.val : ℝ)) ≤ _ at hle
    rw [Finset.sum_attach s (fun n : ℕ => (1 : ℝ) / n)] at hle
    exact hle
  have hexp (p : ℕ) (hp : p ∈ (N + 1).primesBelow) :
      (1 - f p)⁻¹ ≤ Real.exp (2 * ((1 : ℝ) / p)) := by
    let q := (1 : ℝ) / p
    have hp' := Nat.prime_of_mem_primesBelow hp
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp'.pos
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hq : q ≤ 1 / 2 := by
      apply (div_le_div_iff₀ hp0 (by norm_num : (0 : ℝ) < 2)).mpr
      linarith
    have hden : 0 < 1 - q := by linarith
    have hratio : q / (1 - q) ≤ 2 * q := by
      apply (div_le_iff₀ hden).mpr
      have h : 1 ≤ 2 * (1 - q) := by linarith
      calc
        q = q * 1 := by ring
        _ ≤ q * (2 * (1 - q)) := mul_le_mul_of_nonneg_left h hq0
        _ = _ := by ring
    change (1 - q)⁻¹ ≤ Real.exp (2 * q)
    calc
      _ = q / (1 - q) + 1 := by field_simp; ring
      _ ≤ Real.exp (q / (1 - q)) := Real.add_one_le_exp _
      _ ≤ _ := Real.exp_le_exp.mpr hratio
  calc
    _ ≤ (harmonic N : ℝ) := log_add_one_le_harmonic N
    _ = ∑ n ∈ s, (1 : ℝ) / n := by
      simp only [s, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    _ ≤ ∏ p ∈ (N + 1).primesBelow, (1 - f p)⁻¹ := hpart
    _ ≤ ∏ p ∈ (N + 1).primesBelow, Real.exp (2 * ((1 : ℝ) / p)) := by
      apply Finset.prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        have h := hnorm (Nat.prime_of_mem_primesBelow hp)
        have habs : f p ≤ ‖f p‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
        linarith
      · exact hexp
    _ = _ := by
      rw [← Real.exp_sum, ← Finset.mul_sum]
      rfl

theorem OMA.solution : OMA.R_Erdos442_erdos_442_variants_tao_R1_H2_R1.H1 := by
  intro t hT
  have monoT : StrictMono t := by
    intro i j hij
    rw [hT i, hT j]
    exact Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr
      (pow_lt_pow_left₀ (by exact_mod_cast hij) (by positivity) (by decide)))
  have grows (k : ℕ) : (k : ℝ) ≤ t k := by
    rw [hT]
    have h0 := Real.add_one_le_exp ((k : ℝ) ^ 2)
    have h1 := Real.add_one_le_exp (Real.exp ((k : ℝ) ^ 2))
    nlinarith only [h0, h1, sq_nonneg ((k : ℝ) - 1/2)]
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [eventually_gt_atTop (t 4)] with x hx
  have hex : ∃ j : ℕ, x ≤ t j := by
    obtain ⟨j, hj⟩ := exists_nat_gt x
    exact ⟨j, hj.le.trans (grows j)⟩
  let j := Nat.find hex
  have hj : x ≤ t j := Nat.find_spec hex
  have hj4 : 4 < j := by
    by_contra! h
    exact (not_le_of_gt hx) (hj.trans (monoT.monotone h))
  let k := j - 1
  have hk4 : 4 ≤ k := by dsimp [k]; omega
  have hkj : k < j := by dsimp [k]; omega
  have hkjs : k + 1 = j := by dsimp [k]; omega
  refine ⟨k, by omega, lt_of_not_ge (Nat.find_min hex hkj), hkjs.symm ▸ hj, ?_⟩
  let N := ⌊t k⌋₊
  have htk : 0 < t k := by rw [hT]; positivity
  have hfloor : t k < ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_floor_add_one (a := t k)
  have hlog : Real.exp ((k : ℝ) ^ 2) ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
    have hle := Real.log_le_log htk hfloor.le
    simpa only [hT k, Real.log_exp] using hle
  have hbound := Real.exp_le_exp.mp (hlog.trans (log_le_exp_prime_reciprocal_sum N))
  have hk4' : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
  have hm : 0 ≤ (k : ℝ) * ((k : ℝ) - 4) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hk4')
  dsimp only
  constructor <;> nlinarith only [hbound, hm]
