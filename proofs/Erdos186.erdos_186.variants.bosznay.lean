import FormalConjectures.ErdosProblems.«186»

-- Problem: Erdős Problem 186 — bosznay
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/186.lean:93 (declaration Erdos186.erdos_186.variants.bosznay)
-- Credit: @vkascheev (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! A construction of non-averaging sets using the first two moments. -/

open Finset Filter
open scoped BigOperators

namespace BosznayProof

def encode (k i : ℕ) : ℕ := (k ^ 3 + 1) * i + i ^ 2

theorem encode_strictMono (k : ℕ) : StrictMono (encode k) := by
  intro i j hij
  unfold encode
  exact add_lt_add_of_lt_of_le
    (Nat.mul_lt_mul_of_pos_left hij (Nat.zero_lt_succ _))
    (pow_le_pow_left' hij.le 2)

theorem moments {k j : ℕ} {T : Finset ℕ} (hj : j ≤ k) (hT : T ⊆ Icc 1 k)
    (heq : (∑ i ∈ T, encode k i) = T.card * encode k j) :
    (∑ i ∈ T, i) = T.card * j ∧ (∑ i ∈ T, i ^ 2) = T.card * j ^ 2 := by
  have hcard : T.card ≤ k := by
    calc
      T.card ≤ (Icc 1 k).card := card_le_card hT
      _ = k := by simp [Nat.card_Icc]
  have hj_sq : T.card * j ^ 2 ≤ k ^ 3 := by
    calc
      T.card * j ^ 2 ≤ k * k ^ 2 := Nat.mul_le_mul hcard (pow_le_pow_left' hj 2)
      _ = k ^ 3 := by ring
  have hsum_sq : (∑ i ∈ T, i ^ 2) ≤ k ^ 3 := by
    calc
      (∑ i ∈ T, i ^ 2) ≤ ∑ _i ∈ T, k ^ 2 :=
        sum_le_sum fun i hi => pow_le_pow_left' (mem_Icc.mp (hT hi)).2 2
      _ = T.card * k ^ 2 := by simp
      _ ≤ k * k ^ 2 := Nat.mul_le_mul_right _ hcard
      _ = k ^ 3 := by ring
  simp only [encode, sum_add_distrib] at heq
  rw [← mul_sum T (fun i => i) (k ^ 3 + 1), Nat.mul_add, show T.card * ((k ^ 3 + 1) * j) =
    (k ^ 3 + 1) * (T.card * j) by ring] at heq
  -- Both sums of squares fit below the base, so reduction modulo the base recovers them.
  have hs := congrArg (fun n : ℕ => n % (k ^ 3 + 1)) heq
  change ((_ + ∑ i ∈ T, i ^ 2) % (k ^ 3 + 1)) =
    ((_ + T.card * j ^ 2) % (k ^ 3 + 1)) at hs
  rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hsum_sq),
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le hj_sq)] at hs
  refine ⟨?_, hs⟩
  rw [hs] at heq
  exact Nat.mul_left_cancel (Nat.zero_lt_succ (k ^ 3)) (Nat.add_right_cancel heq)

theorem equal_of_moments {j : ℕ} {T : Finset ℕ}
    (h₁ : (∑ i ∈ T, i) = T.card * j)
    (h₂ : (∑ i ∈ T, i ^ 2) = T.card * j ^ 2)
    {i : ℕ} (hi : i ∈ T) : i = j := by
  have h₁' : (∑ x ∈ T, (x : ℤ)) = (T.card : ℤ) * (j : ℤ) := by
    simpa only [Nat.cast_sum, Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℤ)) h₁
  have h₂' : (∑ x ∈ T, (x : ℤ) ^ 2) = (T.card : ℤ) * (j : ℤ) ^ 2 := by
    exact_mod_cast h₂
  have hzero : (∑ x ∈ T, ((x : ℤ) - (j : ℤ)) ^ 2) = 0 := by
    calc
      (∑ x ∈ T, ((x : ℤ) - (j : ℤ)) ^ 2) =
          ∑ x ∈ T, ((x : ℤ) ^ 2 - (2 * (j : ℤ)) * (x : ℤ) + (j : ℤ) ^ 2) :=
        sum_congr rfl fun x _ => by ring
      _ = 0 := by
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, h₁', h₂']
        simp only [sum_const, nsmul_eq_mul]
        ring
  have hi_sq : ((i : ℤ) - (j : ℤ)) ^ 2 = 0 :=
    (sum_eq_zero_iff_of_nonneg (s := T) (fun x _ => sq_nonneg ((x : ℤ) - (j : ℤ)))).mp
      hzero i hi
  have hi_diff : (i : ℤ) - (j : ℤ) = 0 := by
    simpa using hi_sq
  exact_mod_cast sub_eq_zero.mp hi_diff

theorem nonAveraging (k : ℕ) : Erdos186.NonAveraging ((Icc 1 k).image (encode k)) := by
  intro a ha S hS hcard heq
  obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
  have hsubset : S ⊆ (Icc 1 k).image (encode k) := fun _ hx =>
    (mem_erase.mp (hS hx)).2
  obtain ⟨T, hT, rfl⟩ := subset_image_iff.mp hsubset
  have hinj := (encode_strictMono k).injective
  rw [card_image_of_injective _ hinj] at hcard heq
  rw [sum_image (fun _ _ _ _ h => hinj h)] at heq
  obtain ⟨h₁, h₂⟩ := moments (mem_Icc.mp hj).2 hT heq
  obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < T.card)
  have hij : i = j := equal_of_moments h₁ h₂ hi
  exact (mem_erase.mp (hS (mem_image_of_mem (encode k) hi))).1 (congrArg (encode k) hij)

theorem encode_bound {k : ℕ} (hk : 1 ≤ k) : encode k k ≤ (2 * k) ^ 4 := by
  have hk₂ : 1 ≤ k ^ 2 := by
    simpa using (pow_le_pow_left' hk 2)
  have hk_le : k ≤ k ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left k hk
  have hsq_le : k ^ 2 ≤ k ^ 4 := by
    calc
      k ^ 2 ≤ k ^ 2 * k ^ 2 := by simpa using Nat.mul_le_mul_left (k ^ 2) hk₂
      _ = k ^ 4 := by ring
  calc
    encode k k = k ^ 4 + k + k ^ 2 := by unfold encode; ring
    _ ≤ 3 * k ^ 4 := by omega
    _ ≤ (2 * k) ^ 4 := by
      rw [mul_pow]
      omega

theorem lower_bound {N k : ℕ} (hk : 1 ≤ k) (hN : (2 * k) ^ 4 ≤ N) :
    k ≤ Erdos186.F N := by
  let A := (Icc 1 k).image (encode k)
  have hA : A ⊆ Icc 1 N := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    obtain ⟨hi₁, hi₂⟩ := mem_Icc.mp hi
    refine mem_Icc.mpr ⟨?_, ((encode_strictMono k).monotone hi₂).trans
      ((encode_bound hk).trans hN)⟩
    exact (show 1 ≤ encode k 1 by simp [encode]).trans ((encode_strictMono k).monotone hi₁)
  have hcard : A.card = k := by
    dsimp [A]
    rw [card_image_of_injective _ (encode_strictMono k).injective]
    simp [Nat.card_Icc]
  rw [← hcard]
  exact Erdos186.card_le_F hA (nonAveraging k)

end BosznayProof

theorem OMA.solution : type_of% @Erdos186.erdos_186.variants.bosznay := by
  refine ⟨1 / 4, by norm_num, eventually_atTop.mpr ⟨256, ?_⟩⟩
  intro N hN
  let r := (N : ℝ) ^ ((1 : ℝ) / 4)
  have hr : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hr_pow : r ^ 4 = (N : ℝ) := by
    calc
      r ^ 4 = (N : ℝ) ^ (((1 : ℝ) / 4) * (4 : ℕ)) :=
        (Real.rpow_mul_natCast (Nat.cast_nonneg _) _ _).symm
      _ = (N : ℝ) := by norm_num
  have hr_large : 4 ≤ r := by
    by_contra! h
    have hp : r ^ 4 < (4 : ℝ) ^ 4 := pow_lt_pow_left₀ h hr (by decide)
    rw [hr_pow] at hp
    norm_num at hp
    exact (not_lt_of_ge hN) hp
  let k := ⌊r / 2⌋₊
  have hk : 1 ≤ k := Nat.le_floor (by norm_num; linarith)
  have hk_upper : (k : ℝ) ≤ r / 2 := Nat.floor_le (by positivity)
  have hk_lower : r / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hpow : (2 * k) ^ 4 ≤ N := by
    have h : (2 * (k : ℝ)) ^ 4 ≤ (N : ℝ) := by
      rw [← hr_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    exact_mod_cast h
  have hF : (k : ℝ) ≤ (Erdos186.F N : ℝ) := by exact_mod_cast BosznayProof.lower_bound hk hpow
  change (1 / 4) * r ≤ (Erdos186.F N : ℝ)
  exact le_trans (by linarith : (1 / 4) * r ≤ (k : ℝ)) hF
