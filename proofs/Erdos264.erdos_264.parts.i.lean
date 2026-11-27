import FormalConjectures.ErdosProblems.«264»

/-! A direct construction for the powers-of-two case of the Kovač–Tao result.
Credit: @rleshner. -/
namespace OMA.PowersOfTwo

open Filter Finset
open scoped Topology

private abbrev State := Set.Icc (2 : ℝ) 10

-- For x = 2^(n+8), the desired sum of the remaining terms is 2/x - t/x².
-- Choosing k = floor(t-1) keeps the next scaled error in the same interval.
private noncomputable def digit (t : State) : ℕ := ⌊(t : ℝ) - 1⌋₊

private lemma digit_spec (t : State) :
    1 ≤ digit t ∧ digit t ≤ 9 ∧ (digit t : ℝ) ≤ (t : ℝ) - 1 ∧
    (t : ℝ) - 1 < digit t + 1 := by
  have h := t.property
  have hlo := Nat.floor_le (show 0 ≤ (t : ℝ) - 1 by linarith [h.1])
  have hhi := Nat.lt_floor_add_one ((t : ℝ) - 1)
  change _ ∧ _ ∧ (⌊(t : ℝ) - 1⌋₊ : ℝ) ≤ _ ∧ _
  refine ⟨?_, ?_, hlo, hhi⟩
  · change 1 ≤ ⌊(t : ℝ) - 1⌋₊
    exact (Nat.le_floor (by push_cast; linarith [h.1]))
  · change ⌊(t : ℝ) - 1⌋₊ ≤ 9
    exact_mod_cast (show (⌊(t : ℝ) - 1⌋₊ : ℝ) ≤ 9 by linarith [h.2])

private def scale (n : ℕ) : ℝ := 2 ^ (n + 8)

private lemma scale_ge (n : ℕ) : 256 ≤ scale n := by
  have h : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  dsimp [scale]
  rw [pow_add]
  norm_num
  linarith

private lemma scale_succ (n : ℕ) : scale (n+1) = 2 * scale n := by
  unfold scale
  rw [show n + 1 + 8 = (n + 8) + 1 by omega, pow_succ, mul_comm]

private noncomputable def advance (n : ℕ) (t : State) : State :=
  let k : ℝ := digit t
  let x := scale n
  ⟨4 * (t - k + k^2 / (x+k)), by
    obtain ⟨_, h9, hlo, hhi⟩ := digit_spec t
    have hk : k ≤ 9 := by dsimp [k]; exact_mod_cast h9
    have hk0 : 0 ≤ k := by dsimp [k]; positivity
    have hx : 256 ≤ x := scale_ge n
    have hden : 0 < x + k := by linarith
    have herr : k^2 / (x+k) ≤ 1/2 := by
      apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ 9+k by linarith)]
    have herr0 : 0 ≤ k^2 / (x+k) := div_nonneg (sq_nonneg _) hden.le
    change 2 ≤ _ ∧ _ ≤ 10
    change k ≤ (t : ℝ) - 1 at hlo
    change (t : ℝ) - 1 < k + 1 at hhi
    constructor <;> linarith⟩

private noncomputable def state : ℕ → State
  | 0 => ⟨2, by constructor <;> norm_num⟩
  | n+1 => advance n (state n)

private noncomputable def remainder (n : ℕ) : ℝ :=
  2 / scale n - (state n : ℝ) / (scale n)^2

private lemma remainder_step (n : ℕ) :
    remainder n - remainder (n+1) = 1 / (scale n + digit (state n)) := by
  have hx : 0 < scale n := lt_of_lt_of_le (by norm_num) (scale_ge n)
  have hd : 0 < scale n + digit (state n) := by positivity
  dsimp only [remainder]
  rw [scale_succ]
  change 2 / scale n - _ / scale n ^ 2 -
    (2 / (2 * scale n) -
      (4 * ((state n : ℝ) - digit (state n) +
        (digit (state n) : ℝ)^2 / (scale n + digit (state n)))) / (2 * scale n)^2) = _
  field_simp [hx.ne', hd.ne']
  ring

private lemma remainder_limit : Tendsto remainder atTop (𝓝 0) := by
  have hx : Tendsto scale atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 8)
  apply squeeze_zero (g := fun n => 2 / scale n) _ _ (tendsto_const_nhds.div_atTop hx)
  · intro n
    have hs := (state n).property
    have h := scale_ge n
    have hpos : 0 < scale n := by linarith
    unfold remainder
    apply sub_nonneg.mpr
    field_simp
    nlinarith [hs.2]
  · intro n
    have h := (state n).property.1
    exact sub_le_self _ (div_nonneg (by linarith) (sq_nonneg _))

private lemma tail_sum : HasSum (fun n => 1 / (scale n + digit (state n))) (remainder 0) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by
    have := scale_ge n
    positivity) _).2
  simp_rw [← remainder_step, Finset.sum_range_sub']
  simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => remainder 0) atTop (𝓝 (remainder 0))).sub remainder_limit)

-- The first eight perturbations are 1. Only the tail needs steering.
private noncomputable def shift (n : ℕ) : ℤ :=
  if n < 8 then 1 else digit (state (n - 8))

private lemma shift_bounds (n : ℕ) : 1 ≤ shift n ∧ shift n ≤ 9 := by
  unfold shift
  split
  · norm_num
  · obtain ⟨h, h', _⟩ := digit_spec (state (n-8))
    exact ⟨by exact_mod_cast h, by exact_mod_cast h'⟩

private def prefixTerm (n : ℕ) : ℚ := 1 / ((2 : ℚ)^n + 1)

end OMA.PowersOfTwo

open OMA.PowersOfTwo Filter Finset in
theorem OMA.solution : type_of% @Erdos264.erdos_264.parts.i := by
  intro h
  have hi := h shift ⟨9, by rintro _ ⟨n, rfl⟩; exact (shift_bounds n).2⟩
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (shift_bounds n).1⟩
    (by
      rintro ⟨n, hn⟩
      change (↑((2 : ℕ)^n) : ℤ) + shift n = 0 at hn
      have hb := (shift_bounds n).1
      have ha : (0 : ℤ) ≤ (↑((2 : ℕ)^n) : ℤ) := by positivity
      omega)
    (by rintro ⟨n, hn⟩; have := (shift_bounds n).1; omega)
  let f (n : ℕ) : ℝ := 1 / ((2 : ℝ)^n + shift n)
  have hi' : Irrational (∑' n, f n) := by simpa [f] using hi
  have ht : HasSum (fun n => f (n+8)) (remainder 0) := by
    simpa [f, shift, scale] using tail_sum
  have hs : HasSum f ((∑ i ∈ range 8, f i) + remainder 0) := by
    apply (hasSum_nat_add_iff' 8).mp
    simpa using ht
  apply hi'
  refine ⟨(∑ i ∈ range 8, prefixTerm i) + (255/32768 : ℚ), ?_⟩
  rw [hs.tsum_eq]
  push_cast
  have hp : ∀ i ∈ range 8, (prefixTerm i : ℝ) = f i := by
    intro i hi
    simp [prefixTerm, f, shift, mem_range.mp hi]
  rw [Finset.sum_congr rfl hp]
  norm_num [remainder, scale, state]
