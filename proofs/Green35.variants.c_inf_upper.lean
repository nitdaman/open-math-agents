import FormalConjectures.GreensOpenProblems.«35»

-- Problem: Ben Green's Open Problem 35 — c inf upper
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/35.lean:105 (declaration Green35.variants.c_inf_upper)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open MeasureTheory
open scoped Convolution ENNReal

namespace OMA

def wl : List ℕ := [121174638, 0, 0, 25997048, 47606812, 62295219, 32965860, 0, 29734381, 0, 0, 0, 0, 0, 0, 0, 846453, 5731673, 0, 13014906, 0, 8357863, 5268549, 6456956, 6158231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2396999, 0, 0, 5846552, 0, 0, 0, 0, 0, 263320, 5098350, 0, 12833130, 9049240, 21232176, 24866151, 9933512, 1963586, 1363895, 32389841, 0, 0, 14467517, 1297520, 0, 0, 16299837, 38329665, 11361262, 32074656, 17344291, 33181372, 24357561, 25770030, 20567824, 13085743, 17116496, 14349025, 7019695, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1317410, 3425410, 4275650, 3045044, 7900079, 7020678, 8528342, 9705597, 9328960, 9360206, 6227754, 7943462, 8176106, 10667185, 10178412, 11421821, 7773213, 11021377, 12190377, 6572457, 7494855, 0, 0, 2140202, 0, 0, 2314780, 127997, 0, 4672881, 3886266, 11141784, 695668, 4662240, 3543131, 8803511, 4165729, 10785652, 6747342, 18785215, 31908323, 32497050, 9824861, 23309878, 12428441, 3200975, 9331630, 9527521, 12202693, 13179059, 9266878, 2013746, 16448047, 20324945, 21810431, 27321179, 25242816, 19993811, 13683837, 13304836, 8794214, 12893672, 16904485, 22510883, 26079786, 27367504, 26271896, 20457964, 15073917, 11014028, 9896000, 9260690, 13269111, 17329988, 20761774, 21707182, 18933169, 14601258, 8531506, 6187865, 6100211, 9064962, 12781018, 17038096, 18576600, 17345010, 14667009, 9569536, 6092822, 3219067, 4955870, 9657756, 16382398, 22606693, 22230709, 19833621, 16155032, 9330751, 2838363, 2769322, 3349924, 9448887, 20517242, 22849741, 24175836, 19700135, 18168723]

def w (j : ℕ) : ℕ := wl.getD j 0

def S : ℕ := ∑ j ∈ Finset.range 208, w j

theorem S_eq : S = 2039607811 := by decide +kernel

def dd1 (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range 208, (if i + 1 ≤ m ∧ m - (i + 1) < 208 then w i * w (m - (i + 1)) else 0)

theorem dd_ok : ∀ m ∈ Finset.range 419, 2080000 * dd1 m ≤ 7549 * S ^ 2 := by
  decide +kernel

theorem collapse (i m : ℕ) :
    ∑ j ∈ Finset.range 208, (if i + j + 1 = m then w i * w j else 0)
      = if i + 1 ≤ m ∧ m - (i + 1) < 208 then w i * w (m - (i + 1)) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (m - (i + 1))]
    · rw [if_pos (by omega)]
    · intro b _ hb
      rw [if_neg (by omega)]
    · intro hn
      exfalso
      apply hn
      simp only [Finset.mem_range]
      omega
  · apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    rw [if_neg (by omega)]

noncomputable def cc (j : ℕ) : ℝ := 208 * (w j : ℝ) / (S : ℝ)

noncomputable def ind (j : ℕ) (t : ℝ) : ℝ :=
  (Set.Icc ((j : ℝ) / 208) (((j : ℝ) + 1) / 208)).indicator (fun _ => (1 : ℝ)) t

noncomputable def gf (t : ℝ) : ℝ := ∑ j ∈ Finset.range 208, cc j * ind j t

noncomputable def Lam (d : ℝ) : ℝ := max 0 (1 / 208 - |d|)

theorem integrable_ind (j : ℕ) : Integrable (ind j) := by
  unfold ind
  exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (C := (1:ℝ)) (hs := measure_Icc_lt_top.ne))

theorem prod_ind (i j : ℕ) (x t : ℝ) :
    ind i t * ind j (x - t) =
      (Set.Icc (max ((i : ℝ) / 208) (x - ((j : ℝ) + 1) / 208))
        (min (((i : ℝ) + 1) / 208) (x - (j : ℝ) / 208))).indicator (fun _ => (1 : ℝ)) t := by
  unfold ind
  have hc : t ∈ Set.Icc (max ((i : ℝ) / 208) (x - ((j : ℝ) + 1) / 208))
        (min (((i : ℝ) + 1) / 208) (x - (j : ℝ) / 208)) ↔
      t ∈ Set.Icc ((i : ℝ) / 208) (((i : ℝ) + 1) / 208) ∧
        x - t ∈ Set.Icc ((j : ℝ) / 208) (((j : ℝ) + 1) / 208) := by
    simp only [Set.mem_Icc, max_le_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h3⟩, by linarith, by linarith⟩
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩
      exact ⟨⟨h1, by linarith⟩, h3, by linarith⟩
  simp only [Set.indicator_apply, hc]
  by_cases h1 : t ∈ Set.Icc ((i : ℝ) / 208) (((i : ℝ) + 1) / 208) <;>
  by_cases h2 : x - t ∈ Set.Icc ((j : ℝ) / 208) (((j : ℝ) + 1) / 208) <;> simp [h1, h2]

theorem integral_prod (i j : ℕ) (x : ℝ) :
    ∫ t, ind i t * ind j (x - t) = Lam (x - ((i : ℝ) + (j : ℝ) + 1) / 208) := by
  simp_rw [prod_ind]
  rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one, measureReal_def,
    Real.volume_Icc, ENNReal.toReal_ofReal']
  unfold Lam
  have hk : min (((i : ℝ) + 1) / 208) (x - (j : ℝ) / 208)
      - max ((i : ℝ) / 208) (x - ((j : ℝ) + 1) / 208)
      = 1 / 208 - |x - ((i : ℝ) + (j : ℝ) + 1) / 208| := by
    rw [min_def, max_def, abs_eq_max_neg, max_def]
    split_ifs <;> linarith
  rw [hk, max_comm]

theorem integrable_prod (i j : ℕ) (x : ℝ) :
    Integrable (fun t => ind i t * ind j (x - t)) := by
  simp_rw [prod_ind]
  exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (C := (1:ℝ)) (hs := measure_Icc_lt_top.ne))

theorem integral_ind (j : ℕ) : ∫ t, ind j t = 1 / 208 := by
  unfold ind
  rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one, measureReal_def,
    Real.volume_Icc, ENNReal.toReal_ofReal']
  have : ((j : ℝ) + 1) / 208 - (j : ℝ) / 208 = 1 / 208 := by ring
  rw [this, max_eq_left (by norm_num)]

theorem gf_nonneg (t : ℝ) : 0 ≤ gf t := by
  unfold gf
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg
  · unfold cc
    apply div_nonneg
    · positivity
    · positivity
  · unfold ind
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) t

theorem gf_support (t : ℝ) (ht : gf t ≠ 0) : t ∈ Set.Icc (0 : ℝ) 1 := by
  by_contra hn
  apply ht
  unfold gf
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  have hj' : (j : ℝ) + 1 ≤ 208 := by exact_mod_cast hj
  have : ind j t = 0 := by
    unfold ind
    rw [Set.indicator_of_notMem]
    intro hm
    apply hn
    constructor
    · have : (0 : ℝ) ≤ (j : ℝ) / 208 := by positivity
      linarith [hm.1]
    · have : ((j : ℝ) + 1) / 208 ≤ 1 := by
        rw [div_le_one (by norm_num)]
        exact hj'
      linarith [hm.2]
  rw [this, mul_zero]

theorem gf_zero (t : ℝ) (ht : t ∉ Set.Icc (0 : ℝ) 1) : gf t = 0 := by
  by_contra h
  exact ht (gf_support t h)

theorem conv_def' (x : ℝ) : (gf ⋆ gf) x = ∫ t, gf t * gf (x - t) := by
  rw [convolution_def]
  rfl

theorem conv_nonneg (x : ℝ) : 0 ≤ (gf ⋆ gf) x := by
  rw [conv_def']
  exact integral_nonneg fun t => mul_nonneg (gf_nonneg t) (gf_nonneg _)

theorem conv_outside (x : ℝ) (hx : x ∉ Set.Icc (0 : ℝ) 2) : (gf ⋆ gf) x = 0 := by
  rw [conv_def']
  have hz : ∀ t, gf t * gf (x - t) = 0 := by
    intro t
    by_cases h1 : t ∈ Set.Icc (0 : ℝ) 1
    · by_cases h2 : x - t ∈ Set.Icc (0 : ℝ) 1
      · exfalso
        exact hx ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
      · rw [gf_zero (x - t) h2, mul_zero]
    · rw [gf_zero t h1, zero_mul]
  simp only [hz, integral_zero]

theorem gf_integrable : Integrable gf := by
  unfold gf
  exact integrable_finset_sum _ (fun j _ => (integrable_ind j).const_mul _)

theorem gf_integral : ∫ t, gf t = 1 := by
  unfold gf
  rw [integral_finset_sum _ (fun j _ => (integrable_ind j).const_mul _)]
  simp only [integral_const_mul, integral_ind]
  have hS : (S : ℝ) = ∑ j ∈ Finset.range 208, (w j : ℝ) := by
    unfold S
    push_cast
    rfl
  have hS0 : (S : ℝ) ≠ 0 := by
    rw [S_eq]; norm_num
  have : ∑ j ∈ Finset.range 208, cc j * (1 / 208) = ∑ j ∈ Finset.range 208, (w j : ℝ) / (S : ℝ) := by
    apply Finset.sum_congr rfl
    intro j _
    unfold cc
    field_simp
  rw [this, ← Finset.sum_div, ← hS, div_self hS0]

/-- The key pointwise expansion. -/
theorem conv_eq (x : ℝ) :
    (gf ⋆ gf) x = ∑ i ∈ Finset.range 208, ∑ j ∈ Finset.range 208,
      cc i * cc j * Lam (x - ((i : ℝ) + (j : ℝ) + 1) / 208) := by
  rw [conv_def']
  have h1 : ∀ t, gf t * gf (x - t) =
      ∑ i ∈ Finset.range 208, ∑ j ∈ Finset.range 208, cc i * cc j * (ind i t * ind j (x - t)) := by
    intro t
    unfold gf
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [h1]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_prod]
    · intro j _
      exact (integrable_prod i j x).const_mul _
  · intro i _
    exact integrable_finset_sum _ (fun j _ => (integrable_prod i j x).const_mul _)

/-- Coefficient of the hat centred at `m/208`. -/
noncomputable def D (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range 208, ∑ j ∈ Finset.range 208, if i + j + 1 = m then cc i * cc j else 0

theorem reindex (x : ℝ) :
    ∑ i ∈ Finset.range 208, ∑ j ∈ Finset.range 208,
      cc i * cc j * Lam (x - ((i : ℝ) + (j : ℝ) + 1) / 208)
      = ∑ m ∈ Finset.range 419, D m * Lam (x - (m : ℝ) / 208) := by
  unfold D
  simp only [Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.2 (by have := Finset.mem_range.1 hi; have := Finset.mem_range.1 hj; omega))]
  push_cast
  rfl

theorem partition (x : ℝ) (h0 : 0 ≤ x) (h2 : x ≤ 2) :
    ∑ m ∈ Finset.range 419, Lam (x - (m : ℝ) / 208) = 1 / 208 := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ⌊x * 208⌋₊ := ⟨_, rfl⟩
  have hq1 : (q : ℝ) ≤ x * 208 := by
    rw [hq]; exact Nat.floor_le (by positivity)
  have hq2 : x * 208 < (q : ℝ) + 1 := by
    rw [hq]; exact Nat.lt_floor_add_one _
  have hq3 : q ≤ 416 := by
    have : (q : ℝ) ≤ 416 := by linarith
    exact_mod_cast this
  have hsub : ({q, q + 1} : Finset ℕ) ⊆ Finset.range 419 := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rw [Finset.mem_range]
    omega
  have hzero : ∀ m ∈ Finset.range 419, m ∉ ({q, q + 1} : Finset ℕ) →
      Lam (x - (m : ℝ) / 208) = 0 := by
    intro m _ hnm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnm
    unfold Lam
    apply max_eq_left
    rw [sub_nonpos]
    rcases lt_or_gt_of_ne hnm.1 with h | h
    · have h' : (m : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast h
      refine le_trans ?_ (le_abs_self _)
      linarith
    · have h' : (q : ℝ) + 2 ≤ (m : ℝ) := by
        have : q + 2 ≤ m := by omega
        exact_mod_cast this
      exact le_abs.2 (Or.inr (by linarith))
  rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by omega : q ≠ q + 1)]
  unfold Lam
  push_cast
  have ha : |x - (q : ℝ) / 208| = x - (q : ℝ) / 208 := abs_of_nonneg (by linarith)
  have hb : |x - ((q : ℝ) + 1) / 208| = ((q : ℝ) + 1) / 208 - x := by
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [ha, hb, max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

theorem D_bound (m : ℕ) (hm : m ∈ Finset.range 419) : D m ≤ 157.0192 := by
  have hS0 : (S : ℝ) ≠ 0 := by rw [S_eq]; norm_num
  have hS2 : (0 : ℝ) < (S : ℝ) ^ 2 := by positivity
  have hcast : (2080000 : ℝ) * ((dd1 m : ℕ) : ℝ) ≤ 7549 * (S : ℝ) ^ 2 := by
    exact_mod_cast dd_ok m hm
  have hnat : dd1 m = ∑ i ∈ Finset.range 208,
      ∑ j ∈ Finset.range 208, (if i + j + 1 = m then w i * w j else 0) := by
    unfold dd1
    apply Finset.sum_congr rfl
    intro i _
    rw [collapse]
  have hdd : ((dd1 m : ℕ) : ℝ) = ∑ i ∈ Finset.range 208,
      ∑ j ∈ Finset.range 208, (if i + j + 1 = m then (w i : ℝ) * (w j : ℝ) else 0) := by
    rw [hnat]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  have hD : D m = ∑ i ∈ Finset.range 208, ∑ j ∈ Finset.range 208,
      (43264 / (S : ℝ) ^ 2) * (if i + j + 1 = m then (w i : ℝ) * (w j : ℝ) else 0) := by
    unfold D
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i + j + 1 = m
    · simp only [h, if_true]
      unfold cc
      field_simp
      ring
    · simp only [h, if_false, mul_zero]
  have hD' : D m = 43264 / (S : ℝ) ^ 2 * ((dd1 m : ℕ) : ℝ) := by
    rw [hD, hdd, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [hD', div_mul_eq_mul_div, div_le_iff₀ hS2]
  linarith

theorem bound_mid (x : ℝ) (h0 : 0 ≤ x) (h2 : x ≤ 2) : (gf ⋆ gf) x ≤ 7549 / 10000 := by
  rw [conv_eq, reindex]
  calc ∑ m ∈ Finset.range 419, D m * Lam (x - (m : ℝ) / 208)
      ≤ ∑ m ∈ Finset.range 419, (157.0192 : ℝ) * Lam (x - (m : ℝ) / 208) := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_right (D_bound m hm) (le_max_left _ _)
    _ = 157.0192 * (1 / 208) := by rw [← Finset.mul_sum, partition x h0 h2]
    _ = 7549 / 10000 := by norm_num

end OMA

open OMA

theorem OMA.main_target : Green35.c ∞ ≤ 0.7549 := by
  have hg : Green35.IsUnitIntervalDensity gf :=
    ⟨gf_integrable, gf_nonneg, fun t ht => gf_support t ht, gf_integral⟩
  unfold Green35.c
  refine le_trans (sInf_le ⟨gf, hg, rfl⟩) ?_
  rw [eLpNorm_exponent_top]
  have hC : ∀ᵐ x ∂(volume : Measure ℝ), ‖(gf ⋆ gf) x‖ ≤ 7549 / 10000 := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [OMA.conv_nonneg x]
    · by_cases hx : x ∈ Set.Icc (0 : ℝ) 2
      · exact OMA.bound_mid x hx.1 hx.2
      · rw [OMA.conv_outside x hx]
        norm_num
  refine le_trans (eLpNormEssSup_le_of_ae_bound hC) ?_
  have h1 : (7549 / 10000 : NNReal) = (0.7549 : NNReal) := by
    apply NNReal.eq
    rw [NNReal.coe_ofScientific]
    norm_num
  have hlit : (0.7549 : ℝ≥0∞) = ((7549 / 10000 : NNReal) : ℝ≥0∞) := by
    rw [h1]
    rfl
  rw [hlit, ENNReal.ofReal, ENNReal.coe_le_coe, Real.toNNReal_le_iff_le_coe]
  simp

theorem OMA.solution : type_of% @Green35.variants.c_inf_upper := OMA.main_target
