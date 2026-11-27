import FormalConjectures.ErdosProblems.«205»

/-!
# Proof of Erdős Problem 205 (part i)

We refute `∀ᶠ n : ℕ in atTop, IsRepresentable (fun m => Real.log (Real.log m)) n`:
For any `L ≥ 200`, Bertrand's postulate gives `L + 1` distinct odd primes
`p_0 < ... < p_{L-1} < q` with `p_k ≤ 2 ^ (k + 2)`. Setting
`P = 2 ^ L * q * ∏_{k < L} p_k ^ L`, the Chinese remainder theorem produces `n ∈ [P, 2P)`
with `2 ^ L ∣ n`, `q ∣ n`, and `n ≡ 2 ^ k [MOD p_k ^ L]` for all `k < L`.
For every representation `n = 2 ^ k + m`:
- `q ∣ n` forces `m ≠ 0`,
- either `p_k ^ L ∣ m` (`k < L`) or `2 ^ L ∣ m` (`k ≥ L`), yielding `2 ^ L ≤ m` and `L ≤ Ω m`,
- `m ≤ 2P ≤ 2 ^ (8 L ^ 3)` gives `Real.log (Real.log m) ≤ Real.log (8 L ^ 3) < L ≤ Ω m`.
-/

-- Problem: Erdős Problem 205 — i
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/205.lean:58 (declaration Erdos205.erdos_205.parts.i)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)

namespace Erdos205Proof

open Erdos205 Asymptotics Filter
open scoped ArithmeticFunction.Omega

private noncomputable def oddPrime : ℕ → ℕ
  | 0 => 3
  | k + 1 =>
    let p := oddPrime k
    if hp : p ≠ 0 then Classical.choose (Nat.exists_prime_lt_and_le_two_mul p hp) else 3

private lemma oddPrime_spec (k : ℕ) :
    (oddPrime k).Prime ∧ 3 ≤ oddPrime k ∧ oddPrime k ≤ 2 ^ (k + 2) := by
  induction k with
  | zero =>
    refine ⟨by norm_num [oddPrime], by norm_num [oddPrime], by norm_num [oddPrime]⟩
  | succ k ih =>
    rcases ih with ⟨_, h3, hle⟩
    have hne : oddPrime k ≠ 0 := by omega
    have hspec := Classical.choose_spec (Nat.exists_prime_lt_and_le_two_mul (oddPrime k) hne)
    have heq : oddPrime (k + 1) =
        Classical.choose (Nat.exists_prime_lt_and_le_two_mul (oddPrime k) hne) := by
      simp [oddPrime, hne]
    rw [heq]
    refine ⟨hspec.1, by omega, ?_⟩
    calc
      Classical.choose (Nat.exists_prime_lt_and_le_two_mul (oddPrime k) hne)
          ≤ 2 * oddPrime k := hspec.2.2
      _ ≤ 2 * 2 ^ (k + 2) := Nat.mul_le_mul_left 2 hle
      _ = 2 ^ (k + 1 + 2) := by ring

private lemma oddPrime_prime (k : ℕ) : (oddPrime k).Prime := (oddPrime_spec k).1
private lemma oddPrime_ge_three (k : ℕ) : 3 ≤ oddPrime k := (oddPrime_spec k).2.1
private lemma oddPrime_le_pow (k : ℕ) : oddPrime k ≤ 2 ^ (k + 2) := (oddPrime_spec k).2.2

private lemma oddPrime_lt_succ (k : ℕ) : oddPrime k < oddPrime (k + 1) := by
  have hne : oddPrime k ≠ 0 := by have := oddPrime_ge_three k; omega
  have hspec := Classical.choose_spec (Nat.exists_prime_lt_and_le_two_mul (oddPrime k) hne)
  have heq : oddPrime (k + 1) =
      Classical.choose (Nat.exists_prime_lt_and_le_two_mul (oddPrime k) hne) := by
    simp [oddPrime, hne]
  rw [heq]
  exact hspec.2.1

private lemma oddPrime_strictMono : StrictMono oddPrime :=
  strictMono_nat_of_lt_succ oddPrime_lt_succ

private lemma oddPrime_coprime {i j : ℕ} (hij : i ≠ j) :
    Nat.Coprime (oddPrime i) (oddPrime j) :=
  (Nat.coprime_primes (oddPrime_prime i) (oddPrime_prime j)).mpr
    (fun h => hij (oddPrime_strictMono.injective h))

private lemma two_coprime_oddPrime (k : ℕ) : Nat.Coprime 2 (oddPrime k) :=
  (Nat.coprime_primes Nat.prime_two (oddPrime_prime k)).mpr
    (by have := oddPrime_ge_three k; omega)

private lemma crt_exists (L : ℕ) :
    ∀ j ≤ L, ∃ x : ℕ, 2 ^ L * oddPrime L ∣ x ∧
      ∀ k < j, x ≡ 2 ^ k [MOD oddPrime k ^ L] := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨0, dvd_zero _, fun k hk => by omega⟩
  | succ j ih =>
    intro hjL
    rcases ih (by omega) with ⟨x, hx_dvd, hx_mod⟩
    let m1 : ℕ := 2 ^ L * oddPrime L * ∏ k ∈ Finset.range j, oddPrime k ^ L
    let m2 : ℕ := oddPrime j ^ L
    have hcop1 : Nat.Coprime (2 ^ L) m2 := (two_coprime_oddPrime j).pow L L
    have hcop2 : Nat.Coprime (oddPrime L) m2 :=
      (oddPrime_coprime (by omega : L ≠ j)).pow_right L
    have hcop3 : Nat.Coprime (∏ k ∈ Finset.range j, oddPrime k ^ L) m2 := by
      refine Nat.Coprime.prod_left fun k hk => ?_
      have hkj : k < j := Finset.mem_range.mp hk
      exact (oddPrime_coprime (by omega : k ≠ j)).pow L L
    have hcop : Nat.Coprime m1 m2 := (hcop1.mul_left hcop2).mul_left hcop3
    let y : ℕ := (Nat.chineseRemainder hcop x (2 ^ j)).val
    have hy1 : y ≡ x [MOD m1] := (Nat.chineseRemainder hcop x (2 ^ j)).property.1
    have hy2 : y ≡ 2 ^ j [MOD m2] := (Nat.chineseRemainder hcop x (2 ^ j)).property.2
    refine ⟨y, ?_, ?_⟩
    · have hmod : y ≡ x [MOD 2 ^ L * oddPrime L] :=
        hy1.of_dvd (dvd_mul_right (2 ^ L * oddPrime L) _)
      exact (Nat.ModEq.dvd_iff hmod dvd_rfl).mpr hx_dvd
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · have hkdvd : oddPrime k ^ L ∣ m1 :=
          dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hlt)) _
        exact (hy1.of_dvd hkdvd).trans (hx_mod k hlt)
      · exact hy2

private lemma le_omega_of_prime_pow_dvd {p L m : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hdvd : p ^ L ∣ m) : L ≤ Ω m := by
  rcases hdvd with ⟨d, rfl⟩
  have hpL : p ^ L ≠ 0 := pow_ne_zero L hp.ne_zero
  have hd0 : d ≠ 0 := fun h => hm (by simp [h])
  rw [ArithmeticFunction.cardFactors_mul hpL hd0,
    ArithmeticFunction.cardFactors_apply_prime_pow hp]
  omega

private lemma exists_bad_n (L : ℕ) (hL : 200 ≤ L) :
    ∃ n : ℕ, 2 ^ L ≤ n ∧
      ∀ k m : ℕ, n = 2 ^ k + m →
        2 ^ L ≤ m ∧ L ≤ Ω m ∧ Real.log (Real.log (m : ℝ)) < (L : ℝ) := by
  let q : ℕ := oddPrime L
  let P : ℕ := 2 ^ L * q * ∏ k ∈ Finset.range L, oddPrime k ^ L
  have hP_pos : 0 < P := by
    have hq : 0 < q := (oddPrime_prime L).pos
    have hprod : 0 < ∏ k ∈ Finset.range L, oddPrime k ^ L :=
      Finset.prod_pos fun k _ => pow_pos (oddPrime_prime k).pos L
    exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) L) hq) hprod
  have h2L_le_P : 2 ^ L ≤ P := by
    have h1 : 1 ≤ q * ∏ k ∈ Finset.range L, oddPrime k ^ L := by
      have hq : 1 ≤ q := (oddPrime_prime L).one_lt.le
      have hprod : 1 ≤ ∏ k ∈ Finset.range L, oddPrime k ^ L :=
        Finset.one_le_prod' fun k _ => Nat.one_le_pow L _ (oddPrime_prime k).pos
      exact Nat.mul_pos hq hprod
    calc
      2 ^ L = 2 ^ L * 1 := (mul_one _).symm
      _ ≤ 2 ^ L * (q * ∏ k ∈ Finset.range L, oddPrime k ^ L) := Nat.mul_le_mul_left _ h1
      _ = P := by dsimp only [P]; ring
  rcases crt_exists L L le_rfl with ⟨x, hx_dvd, hx_mod⟩
  let n : ℕ := x % P + P
  have hn_ge_P : P ≤ n := Nat.le_add_left P (x % P)
  have hn_lt_2P : n < 2 * P := by
    have hmod_lt : x % P < P := Nat.mod_lt x hP_pos
    dsimp only [n]
    omega
  have hn_mod_P : n ≡ x [MOD P] := by
    dsimp only [n]
    calc
      x % P + P ≡ x % P + 0 [MOD P] := Nat.ModEq.add_left (x % P) (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
      _ = x % P := add_zero _
      _ ≡ x [MOD P] := Nat.mod_modEq x P
  have h2L_dvd_n : 2 ^ L ∣ n := by
    have h2L_dvd_P : 2 ^ L ∣ P := dvd_trans (dvd_mul_right (2 ^ L) q) (dvd_mul_right _ _)
    have h2L_dvd_x : 2 ^ L ∣ x := dvd_trans (dvd_mul_right (2 ^ L) q) hx_dvd
    exact (Nat.ModEq.dvd_iff (hn_mod_P.of_dvd h2L_dvd_P) dvd_rfl).mpr h2L_dvd_x
  have hq_dvd_n : q ∣ n := by
    have hq_dvd_P : q ∣ P := dvd_trans (dvd_mul_left q (2 ^ L)) (dvd_mul_right _ _)
    have hq_dvd_x : q ∣ x := dvd_trans (dvd_mul_left q (2 ^ L)) hx_dvd
    exact (Nat.ModEq.dvd_iff (hn_mod_P.of_dvd hq_dvd_P) dvd_rfl).mpr hq_dvd_x
  have hn_mod_pk : ∀ k < L, n ≡ 2 ^ k [MOD oddPrime k ^ L] := by
    intro k hk
    have hkdvd : oddPrime k ^ L ∣ P :=
      dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hk)) _
    exact (hn_mod_P.of_dvd hkdvd).trans (hx_mod k hk)
  have h2P_le : 2 * P ≤ 2 ^ (8 * L ^ 3) := by
    have hq_le : q ≤ 2 ^ (L + 2) := oddPrime_le_pow L
    have hprod_le : ∏ k ∈ Finset.range L, oddPrime k ^ L ≤ 2 ^ (L ^ 2 * (L + 2)) := by
      calc
        ∏ k ∈ Finset.range L, oddPrime k ^ L
            ≤ ∏ _k ∈ Finset.range L, (2 ^ (L + 2)) ^ L := by
              refine Finset.prod_le_prod' fun k hk => ?_
              have hkle : oddPrime k ≤ 2 ^ (L + 2) :=
                le_trans (oddPrime_le_pow k) (Nat.pow_le_pow_right (by omega)
                  (by have := Finset.mem_range.mp hk; omega))
              exact Nat.pow_le_pow_left hkle L
        _ = (2 ^ (L + 2)) ^ (L * L) := by
              rw [Finset.prod_const, Finset.card_range, ← pow_mul]
        _ = 2 ^ (L ^ 2 * (L + 2)) := by
              rw [← pow_mul]
              congr 1
              ring
    have hexp_le : 1 + L + (L + 2) + L ^ 2 * (L + 2) ≤ 8 * L ^ 3 := by
      have hsq : L ≤ L ^ 2 := by nlinarith
      have hcube : L ^ 2 ≤ L ^ 3 := by rw [pow_succ]; nlinarith
      have h3 : L ^ 2 * (L + 2) = L ^ 3 + 2 * L ^ 2 := by ring
      omega
    calc
      2 * P = 2 * (2 ^ L * q * ∏ k ∈ Finset.range L, oddPrime k ^ L) := rfl
      _ ≤ 2 * (2 ^ L * 2 ^ (L + 2) * 2 ^ (L ^ 2 * (L + 2))) := by
            refine Nat.mul_le_mul_left 2 ?_
            exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hq_le) hprod_le
      _ = 2 ^ (1 + L + (L + 2) + L ^ 2 * (L + 2)) := by
            simp only [pow_add, pow_one]
            ring
      _ ≤ 2 ^ (8 * L ^ 3) := Nat.pow_le_pow_right (by omega) hexp_le
  refine ⟨n, le_trans h2L_le_P hn_ge_P, ?_⟩
  intro k m hnm
  have hm_ne : m ≠ 0 := by
    intro hm0
    rw [hm0, add_zero] at hnm
    have hq2 : q ∣ 2 := (oddPrime_prime L).dvd_of_dvd_pow (hnm ▸ hq_dvd_n)
    have hq_le2 : q ≤ 2 := Nat.le_of_dvd (by omega) hq2
    have hq_ge3 : 3 ≤ q := oddPrime_ge_three L
    omega
  have hm_bounds : 2 ^ L ≤ m ∧ L ≤ Ω m := by
    by_cases hk : k < L
    · have hmod := hn_mod_pk k hk
      rw [hnm] at hmod
      have hm_mod : m ≡ 0 [MOD oddPrime k ^ L] := by
        have h' : 2 ^ k + m ≡ 2 ^ k + 0 [MOD oddPrime k ^ L] := by simpa using hmod
        exact Nat.ModEq.add_left_cancel' (2 ^ k) h'
      have hdvd : oddPrime k ^ L ∣ m := Nat.modEq_zero_iff_dvd.mp hm_mod
      have h2_le_pk : 2 ^ L ≤ oddPrime k ^ L :=
        Nat.pow_le_pow_left (by have := oddPrime_ge_three k; omega) L
      exact ⟨le_trans h2_le_pk (Nat.le_of_dvd (Nat.pos_of_ne_zero hm_ne) hdvd),
        le_omega_of_prime_pow_dvd (oddPrime_prime k) hm_ne hdvd⟩
    · have h2L_dvd_2k : 2 ^ L ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
      have hdvd : 2 ^ L ∣ m := (Nat.dvd_add_right h2L_dvd_2k).mp (hnm ▸ h2L_dvd_n)
      exact ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero hm_ne) hdvd,
        le_omega_of_prime_pow_dvd Nat.prime_two hm_ne hdvd⟩
  refine ⟨hm_bounds.1, hm_bounds.2, ?_⟩
  have hm_le_2P : m ≤ 2 * P := le_trans (Nat.le_add_left m (2 ^ k)) (hnm ▸ hn_lt_2P.le)
  have hm_le_pow : (m : ℝ) ≤ (2 : ℝ) ^ (8 * L ^ 3) := by
    have hnat : m ≤ 2 ^ (8 * L ^ 3) := le_trans hm_le_2P h2P_le
    exact_mod_cast hnat
  have hlog2_le : Real.log 2 ≤ 1 := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2e
      _ = 1 := Real.log_exp 1
  have hm_gt1 : (1 : ℝ) < (m : ℝ) := by
    have h2 : 2 ≤ 2 ^ L := le_trans (by omega : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by omega) (by omega))
    have : 2 ≤ m := le_trans h2 hm_bounds.1
    exact_mod_cast (by omega : 1 < m)
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos hm_gt1
  have hlogm_le : Real.log (m : ℝ) ≤ 8 * (L : ℝ) ^ 3 := by
    calc
      Real.log (m : ℝ) ≤ Real.log ((2 : ℝ) ^ (8 * L ^ 3)) :=
        Real.log_le_log (by linarith) hm_le_pow
      _ = ((8 * L ^ 3 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (8 * L ^ 3)
      _ ≤ ((8 * L ^ 3 : ℕ) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlog2_le (Nat.cast_nonneg _)
      _ = 8 * (L : ℝ) ^ 3 := by push_cast; ring
  have hexp_gt : 8 * (L : ℝ) ^ 3 < Real.exp (L : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg L) 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hsum
    have hL_real : (200 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have hL_nonneg : (0 : ℝ) ≤ (L : ℝ) := by linarith
    have h0 : (0 : ℝ) ≤ (L : ℝ) ^ 0 / 1 := by positivity
    have h1 : (0 : ℝ) ≤ (L : ℝ) ^ 1 / 1 := by positivity
    have h2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 / 2 := by positivity
    have h3 : (0 : ℝ) ≤ (L : ℝ) ^ 3 / 6 := by positivity
    have h4 : 8 * (L : ℝ) ^ 3 < (L : ℝ) ^ 4 / 24 := by
      have : (0 : ℝ) < (L : ℝ) ^ 3 := by positivity
      nlinarith
    norm_num at hsum
    linarith
  have hlog_lt : Real.log (8 * (L : ℝ) ^ 3) < (L : ℝ) := by
    rw [Real.log_lt_iff_lt_exp (by positivity)]
    exact hexp_gt
  exact lt_of_le_of_lt (Real.log_le_log hlogm_pos hlogm_le) hlog_lt

end Erdos205Proof

open Erdos205 Erdos205Proof Filter
open scoped ArithmeticFunction.Omega

theorem OMA.solution : type_of% @Erdos205.erdos_205.parts.i := by
  intro H
  rw [Filter.eventually_atTop] at H
  rcases H with ⟨N0, hN0⟩
  set L : ℕ := max 200 N0
  have hL200 : 200 ≤ L := le_max_left 200 N0
  have hLN0 : N0 ≤ L := le_max_right 200 N0
  rcases exists_bad_n L hL200 with ⟨n, hn_ge, hbad⟩
  have hn_ge_N0 : N0 ≤ n := le_trans (le_trans hLN0 Nat.lt_two_pow_self.le) hn_ge
  rcases hN0 n hn_ge_N0 with ⟨k, m, hnm, hlt⟩
  rcases hbad k m hnm with ⟨_, hΩ, hlog⟩
  have hΩ_real : (L : ℝ) ≤ (Ω m : ℝ) := by exact_mod_cast hΩ
  linarith
