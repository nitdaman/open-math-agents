import FormalConjectures.ErdosProblems.«785»

-- Problem: Erdős Problem 785 — chen fang sharp
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/785.lean:197 (declaration Erdos785.erdos_785.variants.chen_fang_sharp)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Alternating binary digits give two additive complements with explicit counting bounds. -/

open Filter Pointwise
open scoped Topology

namespace Erdos785Digits

/-- Move the binary digit at position `i` to position `2 * i`. -/
private def spread (n : ℕ) : ℕ :=
  Nat.binaryRec (motive := fun _ => ℕ) 0 (fun b _ a => 4 * a + b.toNat) n

@[simp] private theorem spread_zero : spread 0 = 0 := rfl

private theorem spread_bit (b : Bool) (n : ℕ) :
    spread (Nat.bit b n) = 4 * spread n + b.toNat := by
  exact Nat.binaryRec_eq b n (Or.inl rfl)

@[simp] private theorem spread_even (n : ℕ) : spread (2 * n) = 4 * spread n := by
  simpa [Nat.bit] using spread_bit false n

@[simp] private theorem spread_odd (n : ℕ) : spread (2 * n + 1) = 4 * spread n + 1 := by
  simpa [Nat.bit, Nat.add_comm, Nat.mul_comm] using spread_bit true n

private theorem spread_step (n : ℕ) : spread n = 4 * spread (n / 2) + n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · conv_lhs => rw [show n = 2 * (n / 2) by omega]
    simp [h]
  · conv_lhs => rw [show n = 2 * (n / 2) + 1 by omega]
    simp [h]

private theorem spread_strictMono : StrictMono spread := by
  apply strictMono_nat_of_lt_succ
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j := ⟨n / 2, by omega⟩
      rw [spread_even, spread_odd]
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 1 := ⟨n / 2, by omega⟩
      have hj := ih j (by omega)
      rw [spread_odd, show 2 * j + 1 + 1 = 2 * (j + 1) by omega, spread_even]
      omega

private theorem split_digits (n : ℕ) : ∃ a b, n = spread a + 2 * spread b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · exact ⟨0, 0, by simp [hn]⟩
    obtain ⟨a, b, hab⟩ := ih (n / 4) (by omega)
    refine ⟨2 * a + n % 2, 2 * b + (n % 4) / 2, ?_⟩
    rw [spread_step (2 * a + n % 2), spread_step (2 * b + (n % 4) / 2)]
    rw [show (2 * a + n % 2) / 2 = a by omega,
      show (2 * b + (n % 4) / 2) / 2 = b by omega]
    omega

private def digits (d : ℕ) : Set ℕ := Set.range (fun i => d * spread i + 1)

private theorem digits_strictMono {d : ℕ} (hd : 0 < d) :
    StrictMono (fun i => d * spread i + 1) :=
  fun _ _ h => Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left (spread_strictMono h) hd) 1

private noncomputable def count (d x : ℕ) := Erdos785.counting (digits d) x

private theorem count_eq {d x r : ℕ} (hd : 0 < d) (hr : ∀ i, i < r ↔ d * spread i < x) :
    count d x = r := by
  have hset : digits d ∩ Set.Icc 1 x = (fun i => d * spread i + 1) '' Set.Iio r := by
    ext a
    constructor
    · rintro ⟨⟨i, rfl⟩, _, hi⟩
      change d * spread i + 1 ≤ x at hi
      exact ⟨i, (hr i).mpr (by omega), rfl⟩
    · rintro ⟨i, hi, rfl⟩
      have hi' := (hr i).mp hi
      exact ⟨⟨i, rfl⟩, show 1 ≤ d * spread i + 1 by omega,
        show d * spread i + 1 ≤ x by omega⟩
  rw [count, Erdos785.counting, hset,
    Set.ncard_image_of_injective _ (digits_strictMono hd).injective, Set.ncard_Iio_nat]

private theorem count_spec {d : ℕ} (hd : 0 < d) (x i : ℕ) :
    i < count d x ↔ d * spread i < x := by
  have hex : ∃ j, x ≤ d * spread j := ⟨x, calc
    x ≤ spread x := spread_strictMono.id_le x
    _ ≤ d * spread x := by exact Nat.le_mul_of_pos_left _ hd⟩
  have hr (j : ℕ) : j < Nat.find hex ↔ d * spread j < x := by
    constructor
    · intro hj
      exact Nat.lt_of_not_ge (Nat.find_min hex hj)
    · intro hj
      by_contra! hn
      have hh := (Nat.find_spec hex).trans
        (Nat.mul_le_mul_left d (spread_strictMono.monotone hn))
      omega
  rw [count_eq hd hr]
  exact hr i

private theorem count_eq_of_bounds {d x r : ℕ} (hd : 0 < d) (hu : x ≤ d * spread r)
    (hl : ∀ i < r, d * spread i < x) : count d x = r := by
  refine count_eq hd (fun i => ⟨hl i, ?_⟩)
  intro hi
  by_contra! hn
  exact (hu.trans (Nat.mul_le_mul_left d (spread_strictMono.monotone hn))).not_gt hi

private theorem count_eq_of_last {d x r : ℕ} (hd : 0 < d) (hu : x ≤ d * spread r)
    (hl : d * spread (r - 1) < x) : count d x = r := by
  apply count_eq_of_bounds hd hu
  intro i hi
  exact (Nat.mul_le_mul_left d (spread_strictMono.monotone (by omega))).trans_lt hl

private theorem spread_square (n : ℕ) : (n + 1) ^ 2 ≤ 3 * spread n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn]
    have h := ih (n / 2) (by omega)
    rw [spread_step]
    rcases Nat.mod_two_eq_zero_or_one n with hh | hh
    · rw [hh]
      have he : n = 2 * (n / 2) := by omega
      conv_lhs => rw [he]
      nlinarith
    · rw [hh]
      have he : n = 2 * (n / 2) + 1 := by omega
      conv_lhs => rw [he]
      nlinarith

private theorem count_square {d : ℕ} (hd : 0 < d) (hd' : d ≤ 2) (x : ℕ) :
    d * (count d x) ^ 2 ≤ 3 * x := by
  by_cases h : count d x = 0
  · simp [h]
  have hi : count d x - 1 < count d x := by omega
  have hc := (count_spec hd x _).mp hi
  have hs := spread_square (count d x - 1)
  rw [show count d x - 1 + 1 = count d x by omega] at hs
  have hmul := Nat.mul_le_mul_left d hs
  nlinarith

private theorem spread_shift (k j : ℕ) (hj : j < 2 ^ k) :
    spread (2 ^ k + j) = 4 ^ k + spread j := by
  induction k generalizing j with
  | zero =>
      have hj' : j = 0 := by simpa using hj
      subst j
      exact spread_odd 0
  | succ k ih =>
      rw [pow_succ', pow_succ'] at *
      have hsmall : j / 2 < 2 ^ k := by omega
      have hq : (2 * 2 ^ k + j) / 2 = 2 ^ k + j / 2 := by omega
      have hr : (2 * 2 ^ k + j) % 2 = j % 2 := by omega
      rw [spread_step (2 * 2 ^ k + j), hq, hr, ih _ hsmall, spread_step j]
      omega

private theorem spread_pow (k : ℕ) : spread (2 ^ k) = 4 ^ k := by
  simpa using spread_shift k 0 (by positivity)

private theorem spread_last (k : ℕ) : 3 * spread (2 ^ k - 1) + 1 = 4 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', pow_succ']
      have hp : 0 < 2 ^ k := by positivity
      rw [show 2 * 2 ^ k - 1 = 2 * (2 ^ k - 1) + 1 by omega, spread_odd]
      omega

private theorem count_shift {d : ℕ} (hd : 0 < d) (k z : ℕ) (hz : z ≤ d * 4 ^ k) :
    count d (d * 4 ^ k + z) = 2 ^ k + count d z := by
  have hr : count d z ≤ 2 ^ k := by
    by_contra! h
    have hc := (count_spec hd z _).mp h
    rw [spread_pow] at hc
    omega
  apply count_eq_of_bounds hd
  · by_cases h : count d z < 2 ^ k
    · rw [spread_shift _ _ h, Nat.mul_add]
      gcongr
      exact Nat.le_of_not_gt (fun hh => (Nat.lt_irrefl _ ((count_spec hd z _).mpr hh)))
    · have he : count d z = 2 ^ k := by omega
      rw [he, ← two_mul, ← pow_succ', spread_pow, pow_succ', Nat.mul_left_comm]
      omega
  · intro i hi
    by_cases h : i < 2 ^ k
    · have hs := Nat.mul_lt_mul_of_pos_left (spread_strictMono h) hd
      rw [spread_pow] at hs
      omega
    · have hj : i - 2 ^ k < count d z := by omega
      have hh := (count_spec hd z _).mp hj
      have he : i = 2 ^ k + (i - 2 ^ k) := by omega
      rw [he, spread_shift _ _ (hj.trans_le hr), Nat.mul_add]
      omega

private theorem count_two_first (k x : ℕ) (hl : 4 ^ k ≤ x) (hu : x ≤ 2 * 4 ^ k) :
    count 2 x = 2 ^ k := by
  apply count_eq_of_last (by decide)
  · simpa [spread_pow] using hu
  · have h := spread_last k
    omega

private theorem count_one_second (k x : ℕ) (hl : 2 * 4 ^ k ≤ x) (hu : x ≤ 4 ^ (k + 1)) :
    count 1 x = 2 * 2 ^ k := by
  rw [← pow_succ']
  apply count_eq_of_last (by decide)
  · simpa [spread_pow] using hu
  · have h₁ := spread_last (k + 1)
    have h₂ : 0 < 4 ^ k := by positivity
    rw [show (4 : ℕ) ^ (k + 1) = 4 * 4 ^ k by rw [pow_succ']] at h₁
    omega

private theorem product_bound (x : ℕ) (hx : x ≠ 0) :
    2 * count 1 x * count 2 x ≤ 3 * x := by
  let k := Nat.log 4 x
  have hx1 : 4 ^ k ≤ x := Nat.pow_log_le_self _ hx
  have hx2 : x ≤ 4 ^ (k + 1) := (Nat.lt_pow_succ_log_self (by decide) x).le
  have hpow : (2 ^ k : ℕ) ^ 2 = 4 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  by_cases h : x ≤ 2 * 4 ^ k
  · have h₂ := count_two_first k x hx1 h
    have h₁ : count 1 x = 2 ^ k + count 1 (x - 4 ^ k) := by
      have h' := count_shift (show 0 < 1 by decide) k (x - 4 ^ k) (by omega)
      simpa only [one_mul, Nat.add_sub_of_le hx1] using h'
    rw [h₁, h₂]
    have hs := count_square (d := 1) (by decide) (by decide) (x - 4 ^ k)
    have he : x - 4 ^ k + 4 ^ k = x := Nat.sub_add_cancel hx1
    zify at hpow hs he ⊢
    nlinarith only [hpow, hs, he, sq_nonneg ((2 : ℤ) ^ k - (count 1 (x - 4 ^ k) : ℤ))]
  · have hm : 2 * 4 ^ k ≤ x := by omega
    have h₁ := count_one_second k x hm hx2
    have h₂ : count 2 x = 2 ^ k + count 2 (x - 2 * 4 ^ k) := by
      have h' := count_shift (show 0 < 2 by decide) k (x - 2 * 4 ^ k) (by
        rw [pow_succ'] at hx2
        omega)
      simpa only [Nat.add_sub_of_le hm] using h'
    rw [h₁, h₂]
    have hs := count_square (d := 2) (by decide) (by decide) (x - 2 * 4 ^ k)
    have he : x - 2 * 4 ^ k + 2 * 4 ^ k = x := Nat.sub_add_cancel hm
    zify at hpow hs he ⊢
    nlinarith only [hpow, hs, he, sq_nonneg ((2 : ℤ) ^ k - (count 2 (x - 2 * 4 ^ k) : ℤ))]

private def peak (k : ℕ) : ℕ := 4 ^ k + spread (2 ^ k - 1) + 1

private theorem peak_formula (k : ℕ) : 3 * peak k = 4 * 4 ^ k + 2 := by
  unfold peak
  have h := spread_last k
  omega

private theorem peak_counts (k : ℕ) :
    count 1 (peak k) = 2 * 2 ^ k ∧ count 2 (peak k) = 2 ^ k := by
  have h := peak_formula k
  have hp : 0 < 4 ^ k := by positivity
  have h₁ : 4 ^ k ≤ peak k := by unfold peak; omega
  have h₂ : peak k ≤ 2 * 4 ^ k := by omega
  refine ⟨?_, count_two_first k _ h₁ h₂⟩
  rw [← pow_succ']
  apply count_eq_of_last (by decide)
  · rw [one_mul, spread_pow, pow_succ']
    omega
  · rw [one_mul]
    have hp' : 0 < 2 ^ k := by positivity
    rw [pow_succ', show 2 * 2 ^ k - 1 = 2 ^ k + (2 ^ k - 1) by omega,
      spread_shift _ _ (by omega)]
    unfold peak
    omega

private theorem trough_counts (k : ℕ) (hk : 0 < k) (d : ℕ) (hd : 0 < d) (hd' : d ≤ 2) :
    count d (4 ^ k - 1) = 2 ^ k := by
  apply count_eq_of_last hd
  · rw [spread_pow]
    exact (Nat.sub_le _ _).trans (Nat.le_mul_of_pos_left _ hd)
  · have h := spread_last k
    have hp : 4 ≤ (4 : ℕ) ^ k := by
      simpa using (pow_le_pow_right₀ (show 1 ≤ (4 : ℕ) by decide) hk)
    have hc := Nat.mul_le_mul_right (spread (2 ^ k - 1)) hd'
    omega

private noncomputable def ratio (x : ℕ) : ℝ :=
  (count 1 x : ℝ) * (count 2 x : ℝ) / x

private theorem peak_tendsto : Tendsto peak atTop atTop := by
  exact tendsto_atTop_mono (fun k => show (4 : ℕ) ^ k ≤ peak k by unfold peak; omega)
    (tendsto_pow_atTop_atTop_of_one_lt (by decide))

private theorem ratio_tendsto : Tendsto (fun k => ratio (peak k)) atTop (𝓝 (3 / 2 : ℝ)) := by
  have hpow : Tendsto (fun k : ℕ => (4 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hi := tendsto_inv_atTop_zero.comp hpow
  have hden : Tendsto (fun k : ℕ => (4 : ℝ) / 3 + (2 / 3) * ((4 : ℝ) ^ k)⁻¹)
      atTop (𝓝 ((4 : ℝ) / 3)) := by
    simpa using tendsto_const_nhds.add ((tendsto_const_nhds (x := (2 / 3 : ℝ))).mul hi)
  have ht : Tendsto (fun k : ℕ => (2 : ℝ) / (4 / 3 + (2 / 3) * ((4 : ℝ) ^ k)⁻¹))
      atTop (𝓝 (3 / 2 : ℝ)) := by
    have hlim := (tendsto_const_nhds (x := (2 : ℝ))).div hden (by norm_num)
    change Tendsto (fun k : ℕ => (2 : ℝ) / (4 / 3 + (2 / 3) * ((4 : ℝ) ^ k)⁻¹))
      atTop (𝓝 ((2 : ℝ) / (4 / 3))) at hlim
    rwa [show (2 : ℝ) / (4 / 3) = 3 / 2 by norm_num] at hlim
  apply ht.congr
  intro k
  have hp : (0 : ℝ) < (4 : ℝ) ^ k := by positivity
  have hpk : (0 : ℝ) < (peak k : ℝ) := by
    exact_mod_cast (show 0 < peak k from Nat.zero_lt_succ _)
  have hf : 3 * (peak k : ℝ) = 4 * (4 : ℝ) ^ k + 2 := by exact_mod_cast peak_formula k
  have hpow' : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [ratio, (peak_counts k).1, (peak_counts k).2]
  push_cast
  rw [show (2 * (2 : ℝ) ^ k) * (2 : ℝ) ^ k = 2 * (4 : ℝ) ^ k by
    rw [← hpow']; ring]
  apply (div_eq_div_iff (by positivity) hpk.ne').mpr
  calc
    _ = 2 * ((4 / 3) * (4 : ℝ) ^ k + 2 / 3) := by linarith
    _ = _ := by
      rw [show (2 * (4 : ℝ) ^ k) * (4 / 3 + 2 / 3 * ((4 : ℝ) ^ k)⁻¹) =
        2 * ((4 / 3) * (4 : ℝ) ^ k + 2 / 3 * ((4 : ℝ) ^ k * ((4 : ℝ) ^ k)⁻¹)) by ring,
        mul_inv_cancel₀ hp.ne', mul_one]

end Erdos785Digits

open Erdos785Digits in
theorem OMA.solution : type_of% @Erdos785.erdos_785.variants.chen_fang_sharp := by
  refine ⟨digits 1, digits 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Set.infinite_range_of_injective (digits_strictMono (by decide : 0 < 1)).injective
  · exact Set.infinite_range_of_injective (digits_strictMono (by decide : 0 < 2)).injective
  · rintro ⟨a, ha⟩
    change 1 * spread a + 1 = 0 at ha
    omega
  · rintro ⟨a, ha⟩
    change 2 * spread a + 1 = 0 at ha
    omega
  · apply eventually_atTop.mpr
    refine ⟨2, fun n hn => ?_⟩
    obtain ⟨a, b, h⟩ := split_digits (n - 2)
    exact Set.mem_add.mpr ⟨1 * spread a + 1, ⟨a, rfl⟩, 2 * spread b + 1, ⟨b, rfl⟩, by omega⟩
  · change limsup (fun x => (ratio x : EReal)) atTop = _
    apply le_antisymm
    · apply limsup_le_of_le (hf := isCobounded_le_of_bot)
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
      rw [EReal.coe_le_coe_iff, ratio]
      apply (div_le_iff₀ (by exact_mod_cast (show 0 < x by omega))).mpr
      have h : 2 * (count 1 x : ℝ) * (count 2 x : ℝ) ≤ 3 * (x : ℝ) := by
        exact_mod_cast product_bound x (by omega)
      nlinarith only [h]
    · have he := (EReal.tendsto_coe.mpr ratio_tendsto).limsup_eq
      rw [← he]
      exact peak_tendsto.limsup_comp_le_limsup (u := fun x => (ratio x : EReal))
        isCobounded_le_of_bot isBounded_le_of_top
  · apply frequently_atTop.mpr
    intro a
    obtain ⟨k, hk, ha⟩ : ∃ k : ℕ, 0 < k ∧ a + 1 ≤ 4 ^ k := by
      have ht : Tendsto (fun k : ℕ => (4 : ℕ) ^ k) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by decide)
      exact ((eventually_ge_atTop (1 : ℕ)).and ((tendsto_atTop.mp ht) (a + 1))).exists
    refine ⟨4 ^ k - 1, by omega, ?_⟩
    change (count 1 (4 ^ k - 1) : ℝ) * (count 2 (4 ^ k - 1) : ℝ) -
      ((4 ^ k - 1 : ℕ) : ℝ) = 1
    rw [trough_counts k hk 1 (by decide) (by decide), trough_counts k hk 2 (by decide) (by decide)]
    have hp : (2 ^ k : ℕ) * 2 ^ k = 4 ^ k := by
      rw [← pow_two, ← pow_mul, mul_comm, pow_mul]
      norm_num
    have hp' : (((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ)) = ((4 ^ k : ℕ) : ℝ) := by
      exact_mod_cast hp
    rw [hp', Nat.cast_sub (by omega)]
    norm_num