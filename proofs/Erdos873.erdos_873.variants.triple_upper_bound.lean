import FormalConjectures.ErdosProblems.«873»

/-! The Erdős–Szemerédi upper bound, recorded in Erdős (1992), pp. 48–49.
https://doi.org/10.46298/hrj.1992.125
A small least common multiple forces a large logarithmic increment across
the window. Those increments can be charged to a telescoping sum. -/

open Filter
open scoped BigOperators ENNReal

private theorem OMA.gcd_le_gap {x y w : ℕ} (hxy : x < y) (hw : y - x ≤ w) :
    x.gcd y ≤ w :=
  (Nat.le_of_dvd (Nat.sub_pos_of_lt hxy)
    (Nat.dvd_sub (Nat.gcd_dvd_right x y) (Nat.gcd_dvd_left x y))).trans hw

private theorem OMA.tripleLcmGap {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    x ^ 3 ≤ z.lcm (x.lcm y) * (z - x) ^ 3 := by
  have hz : 0 < z := by omega
  have hprod : x.lcm y ∣ x * y := Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
  have hdiv : z.gcd (x.lcm y) ∣ z.gcd x * z.gcd y := by
    have hp : z.gcd (x.lcm y) ∣ z.gcd (x * y) :=
      Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).trans hprod)
    exact hp.trans (gcd_mul_dvd_mul_gcd z x y)
  have hb : z.gcd (x.lcm y) ≤ z.gcd x * z.gcd y := Nat.le_of_dvd
    (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hz) (Nat.gcd_pos_of_pos_left _ hz)) hdiv
  have hwxy : x.gcd y ≤ z - x := OMA.gcd_le_gap hxy (by omega)
  have hwxz : z.gcd x ≤ z - x := by rw [Nat.gcd_comm]; exact OMA.gcd_le_gap (by omega) le_rfl
  have hwyz : z.gcd y ≤ z - x := by rw [Nat.gcd_comm]; exact OMA.gcd_le_gap hyz (by omega)
  calc
    x ^ 3 ≤ x * y * z := by
      rw [pow_succ, pow_two]
      gcongr
      omega
    _ = x.gcd y * (z.gcd (x.lcm y) * z.lcm (x.lcm y)) := by
      rw [Nat.gcd_mul_lcm]
      calc
        x * y * z = (x.gcd y * x.lcm y) * z := by rw [Nat.gcd_mul_lcm]
        _ = _ := by ac_rfl
    _ ≤ x.gcd y * ((z.gcd x * z.gcd y) * z.lcm (x.lcm y)) := by gcongr
    _ ≤ (z - x) * (((z - x) * (z - x)) * z.lcm (x.lcm y)) := by gcongr
    _ = _ := by ring

private theorem OMA.logLcmGap {x y z : ℕ} {X : ℝ} (hX : 1 ≤ X)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z) (hlcm : (z.lcm (x.lcm y) : ℝ) < X) :
    1 ≤ 2 * X ^ (1 / 3 : ℝ) * (Real.log z - Real.log x) := by
  let s := X ^ (1 / 3 : ℝ)
  have hs : 1 ≤ s := Real.one_le_rpow hX (by norm_num)
  have hsCube : s ^ 3 = X := by
    dsimp only [s]
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ X)]
    norm_num
  have hxr : 0 < (x : ℝ) := by exact_mod_cast hx
  have hz : x ≤ z := hxy.le.trans hyz.le
  have hzr : 0 < (z : ℝ) := by
    exact_mod_cast hx.trans_le hz
  have hgap : 0 ≤ (z : ℝ) - (x : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hz)
  have hp := OMA.tripleLcmGap hx hxy hyz
  have hcube : (x : ℝ) ^ 3 ≤ (z.lcm (x.lcm y) : ℝ) * ((z : ℝ) - (x : ℝ)) ^ 3 := by
    exact_mod_cast hp
  have hsg : (x : ℝ) ≤ s * ((z : ℝ) - (x : ℝ)) := by
    have hp' := hcube.trans (mul_le_mul_of_nonneg_right hlcm.le
      (pow_nonneg hgap 3))
    rw [← hsCube, ← mul_pow] at hp'
    exact (pow_le_pow_iff_left₀ hxr.le (mul_nonneg (by linarith) hgap) (by decide : 3 ≠ 0)).mp hp'
  have hnum : (z : ℝ) ≤ (s + 1) * ((z : ℝ) - (x : ℝ)) := by linarith
  have hrel : 1 / (s + 1) ≤ ((z : ℝ) - (x : ℝ)) / (z : ℝ) := by
    apply (div_le_div_iff₀ (by linarith : 0 < s + 1) hzr).2
    linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hxr hzr)
  rw [Real.log_div hxr.ne' hzr.ne'] at hlog
  have hrelLog : 1 / (s + 1) ≤ Real.log z - Real.log x := by
    rw [sub_div, div_self hzr.ne'] at hrel
    linarith
  have hcoef : 1 ≤ 2 * s * (1 / (s + 1)) := by
    rw [mul_one_div]
    apply (le_div_iff₀ (by linarith : 0 < s + 1)).2
    linarith
  exact hcoef.trans (mul_le_mul_of_nonneg_left hrelLog (by linarith))

private theorem OMA.lcmRangeThree (a : ℕ → ℕ) (i : ℕ) :
    (Finset.range 3).lcm (fun j => a (i + j)) = (a (i + 2)).lcm ((a i).lcm (a (i + 1))) := by
  have h3 : Finset.range 3 = {2, 0, 1} := by decide
  rw [h3, Finset.lcm_insert, Finset.lcm_insert]
  simp
  rfl

theorem OMA.solution : type_of% @Erdos873.erdos_873.variants.triple_upper_bound := by
  classical
  refine ⟨4, by norm_num, fun a ha hm => ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  let P (i : ℕ) : Prop := (((Finset.range 3).lcm (fun j => a (i + j)) : ℕ) : ℝ) < X
  let N := ⌊X⌋₊ + 1
  let W := (Finset.range N).filter P
  have haSize (i : ℕ) : i + 1 ≤ a i := by
    induction i with
    | zero => exact Nat.succ_le_of_lt ha
    | succ i ih =>
      have h : a i < a (i + 1) := hm (Nat.lt_succ_self i)
      change i + 1 + 1 ≤ a (i + 1)
      omega
  have hUpper {i : ℕ} (hi : P i) : (a (i + 2) : ℝ) < X := by
    have hl := Nat.le_of_dvd
      (Nat.lcm_pos (by have := haSize (i + 2); omega) (Nat.lcm_pos
        (by have := haSize i; omega) (by have := haSize (i + 1); omega)))
      (Nat.dvd_lcm_left (a (i + 2)) ((a i).lcm (a (i + 1))))
    have hl' : (a (i + 2) : ℝ) ≤ (((a (i + 2)).lcm ((a i).lcm (a (i + 1))) : ℕ) : ℝ) := by
      exact_mod_cast hl
    exact hl'.trans_lt (by simpa only [P, OMA.lcmRangeThree] using hi)
  have hset : {i : ℕ | P i} = (W : Set ℕ) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, W, Finset.mem_filter, Finset.mem_range]
    refine ⟨fun hi => ⟨?_, hi⟩, fun h => h.2⟩
    have hil : (i : ℝ) ≤ (a (i + 2) : ℝ) := by
      exact_mod_cast (show i ≤ a (i + 2) by have := haSize (i + 2); omega)
    exact Nat.lt_succ_of_le (Nat.le_floor (hil.trans (hUpper hi).le))
  let L (i : ℕ) := min (Real.log (a i : ℝ)) (Real.log X)
  have hL : Monotone L := by
    intro i j h
    apply min_le_min _ le_rfl
    exact Real.log_le_log (by exact_mod_cast (show 0 < a i by have := haSize i; omega))
      (by exact_mod_cast hm.monotone h)
  have hLnonneg (i : ℕ) : 0 ≤ L i := by
    apply le_min (Real.log_nonneg _) (Real.log_nonneg hX)
    exact_mod_cast (show 1 ≤ a i by have := haSize i; omega)
  have hLbound (i : ℕ) : L i ≤ Real.log X := min_le_right _ _
  have hLstep {i} (hi : P i) :
      1 ≤ 2 * X ^ (1 / 3 : ℝ) * (L (i + 2) - L i) := by
    have hpos (j : ℕ) : 0 < (a j : ℝ) := by
      exact_mod_cast (show 0 < a j by have := haSize j; omega)
    have hlt : (a i : ℝ) ≤ (a (i + 2) : ℝ) := by
      exact_mod_cast hm.monotone (show i ≤ i + 2 by omega)
    rw [show L (i + 2) = Real.log (a (i + 2)) from
        min_eq_left (Real.log_le_log (hpos _) (hUpper hi).le),
      show L i = Real.log (a i) from
        min_eq_left (Real.log_le_log (hpos _) (hlt.trans (hUpper hi).le))]
    have h₁ : a i < a (i + 1) := hm (by omega)
    have h₂ : a (i + 1) < a (i + 2) := hm (by omega)
    exact OMA.logLcmGap hX (by have := haSize i; omega) h₁ h₂
      (by simpa only [P, OMA.lcmRangeThree] using hi)
  have htel (m : ℕ) :
      (∑ i ∈ Finset.range m, (L (i + 2) - L i)) = L m + L (m + 1) - L 0 - L 1 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      change L m + L (m + 1) - L 0 - L 1 + (L (m + 2) - L m) =
        L (m + 1) + L (m + 2) - L 0 - L 1
      ring
  have hcoef : 0 ≤ 2 * X ^ (1 / 3 : ℝ) := by positivity
  have hcard : (W.card : ℝ) ≤ 4 * X ^ (1 / 3 : ℝ) * Real.log X := by
    calc
      _ = ∑ _ ∈ W, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ W, 2 * X ^ (1 / 3 : ℝ) * (L (i + 2) - L i) :=
        Finset.sum_le_sum fun i hi => hLstep (Finset.mem_filter.mp hi).2
      _ ≤ ∑ i ∈ Finset.range N, 2 * X ^ (1 / 3 : ℝ) * (L (i + 2) - L i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        exact fun i _ _ => mul_nonneg hcoef (sub_nonneg.mpr (hL (by omega)))
      _ = 2 * X ^ (1 / 3 : ℝ) * (L N + L (N + 1) - L 0 - L 1) := by
        rw [← Finset.mul_sum, htel]
      _ ≤ _ := by
        have hbound : L N + L (N + 1) - L 0 - L 1 ≤ 2 * Real.log X := by
          linarith [hLbound N, hLbound (N + 1), hLnonneg 0, hLnonneg 1]
        calc
          _ ≤ 2 * X ^ (1 / 3 : ℝ) * (2 * Real.log X) :=
            mul_le_mul_of_nonneg_left hbound hcoef
          _ = _ := by ring
  change ({i : ℕ | P i}.encard : EReal) ≤ _
  rw [hset, Set.encard_coe_eq_coe_finsetCard]
  rw [ENat.toENNReal_coe, ← EReal.coe_ennreal_toReal (by simp : (W.card : ℝ≥0∞) ≠ ⊤)]
  exact EReal.coe_le_coe (by simpa using hcard)