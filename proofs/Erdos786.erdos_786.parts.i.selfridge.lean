import FormalConjectures.ErdosProblems.«786»
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Proof of Erdős Problem 786 (Selfridge's `1 / e` Construction)

We prove `Erdos786.erdos_786.parts.i.selfridge`: for any `ε ∈ (0, 1 / e)` and every sufficiently
large prime `p`, choosing the first `k` such that `∑_{q ∈ S_k} 1/q < 1 < ∑_{q ∈ S_{k+1}} 1/q`
(where `S_k = consecutivePrimesFrom p k`) gives a set
`A = {n | ∑_{q ∈ S_k} n.factorization q = 1}` satisfying:
1. `A.IsMulCardSet` by summing `Nat.factorization_prod` over `q ∈ S_k`.
2. `A` is periodic modulo `M = ∏_{q ∈ S_k} q²`, and by the Chinese Remainder Theorem its exact
   natural density is `δ = (∑_{q ∈ S_k} 1/q) * ∏_{q ∈ S_k} (1 - 1/q)`.
3. Using `1 - x ≥ exp(-x - 2 x²)` on `[0, 1/2]` (directly from `Real.add_one_le_exp`),
   `δ > (1 - 1/p)(1 - 2/p)/e ≥ 1/e - 3/p > 1/e - ε` for all `p ≥ max 3 (⌈3/ε⌉ + 1)`.
-/

-- Problem: Erdős Problem 786 — selfridge
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/786.lean:187 (declaration Erdos786.erdos_786.parts.i.selfridge)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos786SelfridgeProof

open Erdos786 Filter Real
open scoped Topology Classical

private lemma primes_ge_infinite (p : ℕ) : {q : ℕ | q.Prime ∧ p ≤ q}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨q, hq_ge, hq_prime⟩ := Nat.exists_infinite_primes (max p (n + 1))
  exact ⟨q, ⟨hq_prime, le_trans (le_max_left _ _) hq_ge⟩,
    lt_of_lt_of_le (Nat.lt_succ_self n) (le_trans (le_max_right _ _) hq_ge)⟩

private lemma mem_consecutivePrimesFrom_prime {p k q : ℕ} (hq : q ∈ consecutivePrimesFrom p k) :
    q.Prime ∧ p ≤ q := by
  rcases Finset.mem_image.mp hq with ⟨i, _, rfl⟩
  exact Nat.nth_mem_of_infinite (primes_ge_infinite p) i

private lemma consecutivePrimesFrom_succ (p k : ℕ) :
    consecutivePrimesFrom p (k + 1) =
      insert (Nat.nth (fun q => q.Prime ∧ p ≤ q) (k + 1)) (consecutivePrimesFrom p k) := by
  simp only [consecutivePrimesFrom, Finset.range_add_one, Finset.image_insert]

private lemma nth_succ_notMem_consecutivePrimesFrom (p k : ℕ) :
    Nat.nth (fun q => q.Prime ∧ p ≤ q) (k + 1) ∉ consecutivePrimesFrom p k := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨i, hi, heq⟩
  have hmono := Nat.nth_strictMono (primes_ge_infinite p)
  have hi' : i = k + 1 := hmono.injective heq
  rw [Finset.mem_range] at hi
  omega

private lemma sum_one_div_primes_ne_one {T : Finset ℕ} (hT : ∀ q ∈ T, q.Prime) :
    (∑ q ∈ T, (1 : ℝ) / q) ≠ 1 := by
  intro hsum
  by_cases hne : T.Nonempty
  · obtain ⟨r, hrT⟩ := hne
    have hrp : r.Prime := hT r hrT
    let M : ℕ := ∏ q ∈ T.erase r, q
    have hr_not_dvd : ¬ r ∣ M := by
      rw [hrp.prime.dvd_finsetProd_iff]
      rintro ⟨q, hq_er, hdvd⟩
      have hqT : q ∈ T := Finset.mem_of_mem_erase hq_er
      have hqr : q ≠ r := Finset.ne_of_mem_erase hq_er
      have hqp : q.Prime := hT q hqT
      have := (Nat.prime_dvd_prime_iff_eq hrp hqp).mp hdvd
      exact hqr this.symm
    have hmul : (r * M : ℝ) * ∑ q ∈ T, (1 : ℝ) / q = (r * M : ℝ) := by
      rw [hsum, mul_one]
    have hsplit : ∑ q ∈ T, (1 : ℝ) / q = (1 : ℝ) / r + ∑ q ∈ T.erase r, (1 : ℝ) / q := by
      rw [← Finset.add_sum_erase _ _ hrT]
    rw [hsplit, mul_add, Finset.mul_sum] at hmul
    have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hrp.ne_zero
    have hterm_r : (r * M : ℝ) * ((1 : ℝ) / r) = (M : ℝ) := by
      field_simp [hr_ne]
    have hterm_q : ∀ q ∈ T.erase r, (r * M : ℝ) * ((1 : ℝ) / q) = ((r * (M / q) : ℕ) : ℝ) := by
      intro q hq
      have hqp : q.Prime := hT q (Finset.mem_of_mem_erase hq)
      have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hqp.ne_zero
      have hqdvd : q ∣ M := Finset.dvd_prod_of_mem _ hq
      have hcast : ((M / q : ℕ) : ℝ) * (q : ℝ) = (M : ℝ) := by
        exact_mod_cast Nat.div_mul_cancel hqdvd
      rw [Nat.cast_mul]
      field_simp [hq_ne]
      linarith
    rw [hterm_r, Finset.sum_congr rfl hterm_q, ← Nat.cast_sum, ← Nat.cast_add,
      ← Nat.cast_mul] at hmul
    have hnat : M + ∑ q ∈ T.erase r, r * (M / q) = r * M := by exact_mod_cast hmul
    have hdvd_sum : r ∣ ∑ q ∈ T.erase r, r * (M / q) :=
      Finset.dvd_sum fun q _ => dvd_mul_right r _
    have hdvd_rhs : r ∣ r * M := dvd_mul_right r M
    have hdvd_M : r ∣ M := (Nat.dvd_add_left hdvd_sum).mp (hnat ▸ hdvd_rhs)
    exact hr_not_dvd hdvd_M
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp at hsum

private lemma exists_sum_consecutivePrimesFrom_gt_one (p : ℕ) :
    ∃ m : ℕ, 1 < ∑ q ∈ consecutivePrimesFrom p m, (1 : ℝ) / q := by
  let step : ℕ → ℕ := fun a => (4 ^ (a.primesBelow.card + 1)).succ
  have hstep_gt : ∀ a : ℕ, a < step a := by
    intro a
    by_contra hle
    push Not at hle
    have hsub : (step a).primesBelow ⊆ a.primesBelow := by
      intro q hq
      rw [Nat.mem_primesBelow] at hq ⊢
      exact ⟨lt_of_lt_of_le hq.1 hle, hq.2⟩
    have hemp : (step a).primesBelow \ a.primesBelow = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsub
    have hhalf := one_half_le_sum_primes_ge_one_div a
    change (1 / 2 : ℝ) ≤ ∑ q ∈ (step a).primesBelow \ a.primesBelow, (1 / q : ℝ) at hhalf
    rw [hemp, Finset.sum_empty] at hhalf
    linarith
  let k1 := step p
  let k2 := step k1
  let k3 := step k2
  have hk01 : p < k1 := hstep_gt p
  have hk12 : k1 < k2 := hstep_gt k1
  have hk23 : k2 < k3 := hstep_gt k2
  let B1 : Finset ℕ := k1.primesBelow \ p.primesBelow
  let B2 : Finset ℕ := k2.primesBelow \ k1.primesBelow
  let B3 : Finset ℕ := k3.primesBelow \ k2.primesBelow
  have hB1 : (1 / 2 : ℝ) ≤ ∑ q ∈ B1, (1 : ℝ) / q := one_half_le_sum_primes_ge_one_div p
  have hB2 : (1 / 2 : ℝ) ≤ ∑ q ∈ B2, (1 : ℝ) / q := one_half_le_sum_primes_ge_one_div k1
  have hB3 : (1 / 2 : ℝ) ≤ ∑ q ∈ B3, (1 : ℝ) / q := one_half_le_sum_primes_ge_one_div k2
  have hdisj12 : Disjoint B1 B2 := Finset.disjoint_left.mpr fun q h1 h2 => by
    rw [Finset.mem_sdiff] at h1 h2
    exact h2.2 h1.1
  have hdisj13 : Disjoint B1 B3 := Finset.disjoint_left.mpr fun q h1 h3 => by
    rw [Finset.mem_sdiff, Nat.mem_primesBelow] at h1 h3
    exact h3.2 (Nat.mem_primesBelow.mpr ⟨lt_trans h1.1.1 hk12, h1.1.2⟩)
  have hdisj23 : Disjoint B2 B3 := Finset.disjoint_left.mpr fun q h2 h3 => by
    rw [Finset.mem_sdiff] at h2 h3
    exact h3.2 h2.1
  have hsub_all : B1 ∪ B2 ∪ B3 ⊆ consecutivePrimesFrom p k3 := by
    intro q hq
    have hq_mem : q.Prime ∧ p ≤ q ∧ q < k3 := by
      simp only [Finset.mem_union, B1, B2, B3, Finset.mem_sdiff, Nat.mem_primesBelow] at hq
      rcases hq with (⟨⟨hlt, hp⟩, hnp⟩ | ⟨⟨hlt, hp⟩, hnp⟩) | ⟨⟨hlt, hp⟩, hnp⟩
      · have hpq : p ≤ q := by by_contra h; exact hnp ⟨Nat.lt_of_not_ge h, hp⟩
        exact ⟨hp, hpq, lt_trans hlt (lt_trans hk12 hk23)⟩
      · have hk1q : k1 ≤ q := by by_contra h; exact hnp ⟨Nat.lt_of_not_ge h, hp⟩
        exact ⟨hp, le_trans hk01.le hk1q, lt_trans hlt hk23⟩
      · have hk2q : k2 ≤ q := by by_contra h; exact hnp ⟨Nat.lt_of_not_ge h, hp⟩
        exact ⟨hp, le_trans (le_trans hk01.le hk12.le) hk2q, hlt⟩
    rw [consecutivePrimesFrom, Finset.mem_image]
    refine ⟨Nat.count (fun r => r.Prime ∧ p ≤ r) q, ?_,
      Nat.nth_count (p := fun r => r.Prime ∧ p ≤ r) ⟨hq_mem.1, hq_mem.2.1⟩⟩
    rw [Finset.mem_range]
    have hcle : Nat.count (fun r => r.Prime ∧ p ≤ r) q ≤ q := by
      rw [Nat.count_eq_card_filter_range]
      exact (Finset.card_filter_le _ _).trans (by simp)
    omega
  have hsum_ge : (3 / 2 : ℝ) ≤ ∑ q ∈ consecutivePrimesFrom p k3, (1 : ℝ) / q := by
    have h123 : (∑ q ∈ B1 ∪ B2 ∪ B3, (1 : ℝ) / q) =
        (∑ q ∈ B1, (1 : ℝ) / q) + (∑ q ∈ B2, (1 : ℝ) / q) + (∑ q ∈ B3, (1 : ℝ) / q) := by
      rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdisj13, hdisj23⟩),
        Finset.sum_union hdisj12]
    have hle : (∑ q ∈ B1 ∪ B2 ∪ B3, (1 : ℝ) / q) ≤
        ∑ q ∈ consecutivePrimesFrom p k3, (1 : ℝ) / q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub_all fun q _ _ => by positivity
    linarith
  exact ⟨k3, by linarith⟩

private lemma exists_crossing_index {p : ℕ} (hp : p.Prime) :
    ∃ k : ℕ,
      (∑ q ∈ consecutivePrimesFrom p k, (1 : ℝ) / q) < 1 ∧
      1 < (∑ q ∈ consecutivePrimesFrom p (k + 1), (1 : ℝ) / q) ∧
      1 - (1 : ℝ) / p < ∑ q ∈ consecutivePrimesFrom p k, (1 : ℝ) / q := by
  have hex := exists_sum_consecutivePrimesFrom_gt_one p
  let m := Nat.find hex
  have hm_gt : 1 < ∑ q ∈ consecutivePrimesFrom p m, (1 : ℝ) / q := Nat.find_spec hex
  have hm_ne_zero : m ≠ 0 := by
    intro h0
    rw [h0, consecutivePrimesFrom_zero hp, Finset.sum_singleton] at hm_gt
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have : (1 : ℝ) / p ≤ 1 / 2 := by
      rw [one_div_le_one_div (by linarith) (by norm_num)]
      exact hp2
    linarith
  obtain ⟨k, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne_zero
  have hm_gt' : 1 < ∑ q ∈ consecutivePrimesFrom p (k + 1), (1 : ℝ) / q := by
    simpa [hk_eq] using hm_gt
  have hk_not_gt : ¬ 1 < ∑ q ∈ consecutivePrimesFrom p k, (1 : ℝ) / q :=
    Nat.find_min hex (show k < m by omega)
  have hk_ne : (∑ q ∈ consecutivePrimesFrom p k, (1 : ℝ) / q) ≠ 1 :=
    sum_one_div_primes_ne_one fun q hq => (mem_consecutivePrimesFrom_prime hq).1
  have hk_lt : (∑ q ∈ consecutivePrimesFrom p k, (1 : ℝ) / q) < 1 :=
    lt_of_le_of_ne (not_lt.mp hk_not_gt) hk_ne
  refine ⟨k, hk_lt, hm_gt', ?_⟩
  rw [consecutivePrimesFrom_succ,
    Finset.sum_insert (nth_succ_notMem_consecutivePrimesFrom p k)] at hm_gt'
  have hnext := Nat.nth_mem_of_infinite (primes_ge_infinite p) (k + 1)
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hnext_le : (1 : ℝ) / (Nat.nth (fun q => q.Prime ∧ p ≤ q) (k + 1) : ℝ) ≤ (1 : ℝ) / p :=
    one_div_le_one_div_of_le hp_pos (by exact_mod_cast hnext.2)
  linarith

private lemma isMulCardSet_of_sum_factorization_eq_one (T : Finset ℕ) :
    ({n : ℕ | ∑ q ∈ T, n.factorization q = 1}).IsMulCardSet := by
  have hkey : ∀ s : Finset ℕ, (s : Set ℕ) ⊆ {n : ℕ | ∑ q ∈ T, n.factorization q = 1} →
      ∑ q ∈ T, (s.prod id).factorization q = s.card := by
    intro s hs
    have hne0 : ∀ i ∈ s, id i ≠ 0 := fun i hi h0 => by
      have hiA : ∑ q ∈ T, i.factorization q = 1 := hs hi
      simp only [id] at h0
      subst h0
      simp at hiA
    rw [Nat.factorization_prod hne0]
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    have h1 : ∀ i ∈ s, ∑ q ∈ T, (id i).factorization q = 1 := fun i hi => hs hi
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one]
  intro a b ha hb hprod
  rw [← hkey a ha, ← hkey b hb, hprod]

private lemma card_filter_mul_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hP : ∀ n, P (n % a) ↔ P n) (hQ : ∀ n, Q (n % b) ↔ Q n) :
    ((Finset.range (a * b)).filter (fun n => P n ∧ Q n)).card =
      ((Finset.range a).filter P).card * ((Finset.range b).filter Q).card := by
  rw [← Finset.card_product]
  refine Finset.card_bij (fun n _ => (n % a, n % b)) ?_ ?_ ?_
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨_, hPn, hQn⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n ha), (hP n).mpr hPn⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hb), (hQ n).mpr hQn⟩⟩
  · intro n₁ hn₁ n₂ hn₂ heq
    have hn₁' : n₁ < a * b := Finset.mem_range.mp (Finset.mem_filter.mp hn₁).1
    have hn₂' : n₂ < a * b := Finset.mem_range.mp (Finset.mem_filter.mp hn₂).1
    have hma : n₁ ≡ n₂ [MOD a] := congrArg Prod.fst heq
    have hmb : n₁ ≡ n₂ [MOD b] := congrArg Prod.snd heq
    have hmab : n₁ ≡ n₂ [MOD a * b] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hma, hmb⟩
    rw [Nat.ModEq, Nat.mod_eq_of_lt hn₁', Nat.mod_eq_of_lt hn₂'] at hmab
    exact hmab
  · rintro ⟨x, y⟩ hxy
    rcases Finset.mem_product.mp hxy with ⟨hx, hy⟩
    rcases Finset.mem_filter.mp hx with ⟨hx_lt, hPx⟩
    rcases Finset.mem_filter.mp hy with ⟨hy_lt, hQy⟩
    rw [Finset.mem_range] at hx_lt hy_lt
    let cr := Nat.chineseRemainder hcop x y
    let z := cr.1 % (a * b)
    have hz_lt : z < a * b := Nat.mod_lt _ (Nat.mul_pos ha hb)
    have hza : z % a = x := by
      have h1 : z ≡ cr.1 [MOD a] := (Nat.mod_modEq cr.1 (a * b)).of_mul_right b
      have h2 : z ≡ x [MOD a] := h1.trans cr.2.1
      rw [Nat.ModEq, Nat.mod_eq_of_lt hx_lt] at h2
      exact h2
    have hzb : z % b = y := by
      have h1 : z ≡ cr.1 [MOD b] := (Nat.mod_modEq cr.1 (a * b)).of_mul_left a
      have h2 : z ≡ y [MOD b] := h1.trans cr.2.2
      rw [Nat.ModEq, Nat.mod_eq_of_lt hy_lt] at h2
      exact h2
    refine ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hz_lt, ?_, ?_⟩, Prod.ext hza hzb⟩
    · exact (hP z).mp (hza.symm ▸ hPx)
    · exact (hQ z).mp (hzb.symm ▸ hQy)

private lemma card_not_dvd_sq {q : ℕ} (hq : q.Prime) :
    ((Finset.range (q ^ 2)).filter (fun n => ¬ q ∣ n)).card = q * (q - 1) := by
  have hmul_eq : (Finset.range (q ^ 2)).filter (fun n => q ∣ n) =
      (Finset.range q).image (fun j => q * j) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hn, ⟨j, rfl⟩⟩
      refine ⟨j, ?_, rfl⟩
      rw [sq] at hn
      exact (mul_lt_mul_iff_right₀ hq.pos).mp hn
    · rintro ⟨j, hj, rfl⟩
      exact ⟨by rw [sq]; exact (mul_lt_mul_iff_right₀ hq.pos).mpr hj, dvd_mul_right q j⟩
  have hmul_card : ((Finset.range (q ^ 2)).filter (fun n => q ∣ n)).card = q := by
    rw [hmul_eq, Finset.card_image_of_injective _ (mul_right_injective₀ hq.ne_zero), Finset.card_range]
  have hsum : ((Finset.range (q ^ 2)).filter (fun n => q ∣ n)).card +
      ((Finset.range (q ^ 2)).filter (fun n => ¬ q ∣ n)).card = q ^ 2 := by
    have hdisj : Disjoint ((Finset.range (q ^ 2)).filter (fun n => q ∣ n))
        ((Finset.range (q ^ 2)).filter (fun n => ¬ q ∣ n)) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
    have hunion : (Finset.range (q ^ 2)).filter (fun n => q ∣ n) ∪
        (Finset.range (q ^ 2)).filter (fun n => ¬ q ∣ n) = Finset.range (q ^ 2) := by
      ext n
      simp only [Finset.mem_union, Finset.mem_filter]
      tauto
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]
  have hq1 : 1 ≤ q := hq.one_le
  have hmul_sub : q * (q - 1) + q = q ^ 2 := by
    zify [hq1]
    ring
  omega

private lemma card_exact_dvd_sq {q : ℕ} (hq : q.Prime) :
    ((Finset.range (q ^ 2)).filter (fun n => q ∣ n ∧ ¬ q ^ 2 ∣ n)).card = q - 1 := by
  have heq : (Finset.range (q ^ 2)).filter (fun n => q ∣ n ∧ ¬ q ^ 2 ∣ n) =
      (Finset.Ico 1 q).image (fun j => q * j) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨hn, ⟨j, rfl⟩, hndvd⟩
      rw [sq] at hn
      have hj_lt : j < q := (mul_lt_mul_iff_right₀ hq.pos).mp hn
      have hj_pos : 1 ≤ j := by
        by_contra h0
        have hj0 : j = 0 := by omega
        subst hj0
        exact hndvd (dvd_zero _)
      exact ⟨j, ⟨hj_pos, hj_lt⟩, rfl⟩
    · rintro ⟨j, ⟨hj1, hjq⟩, rfl⟩
      refine ⟨by rw [sq]; exact (mul_lt_mul_iff_right₀ hq.pos).mpr hjq, dvd_mul_right q j, ?_⟩
      rintro ⟨c, hc⟩
      have h1 : q * j = q * (q * c) := by rw [sq, mul_assoc] at hc; exact hc
      have h2 : j = q * c := mul_left_cancel₀ hq.ne_zero h1
      rcases c with _ | c
      · simp at h2; omega
      · nlinarith
  rw [heq, Finset.card_image_of_injective _ (mul_right_injective₀ hq.ne_zero), Nat.card_Ico]

private lemma card_none_dvd_prod_sq : ∀ (U : Finset ℕ), (∀ q ∈ U, q.Prime) →
    ((Finset.range (∏ q ∈ U, q ^ 2)).filter (fun n => ∀ q ∈ U, ¬ q ∣ n)).card =
      ∏ q ∈ U, (q * (q - 1)) := by
  intro U
  induction U using Finset.induction with
  | empty =>
    intro _
    simp
  | @insert a U haU ih =>
    intro hprime
    have hap : a.Prime := hprime a (Finset.mem_insert_self a U)
    have hUprime : ∀ q ∈ U, q.Prime := fun q hq => hprime q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert haU, Finset.prod_insert haU]
    have ha2_pos : 0 < a ^ 2 := pow_pos hap.pos 2
    have hU_pos : 0 < ∏ q ∈ U, q ^ 2 :=
      Finset.prod_pos fun q hq => pow_pos (hUprime q hq).pos 2
    have hcop : (a ^ 2).Coprime (∏ q ∈ U, q ^ 2) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hqp : q.Prime := hUprime q hq
      have hne : a ≠ q := fun h => haU (h ▸ hq)
      exact ((Nat.coprime_primes hap hqp).mpr hne).pow 2 2
    have hfilt : (Finset.range (a ^ 2 * ∏ q ∈ U, q ^ 2)).filter
          (fun n => ∀ q ∈ insert a U, ¬ q ∣ n) =
        (Finset.range (a ^ 2 * ∏ q ∈ U, q ^ 2)).filter
          (fun n => (¬ a ∣ n) ∧ (∀ q ∈ U, ¬ q ∣ n)) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp]
    rw [hfilt]
    have hPa : ∀ n, (¬ a ∣ n % a ^ 2) ↔ (¬ a ∣ n) := fun n =>
      not_congr ((Nat.mod_modEq n (a ^ 2)).of_mul_right a |> fun h => by
        have : a ∣ a ^ 2 := dvd_pow_self a (by norm_num)
        exact Nat.dvd_iff_mod_eq_zero.trans <| by
          rw [Nat.mod_mod_of_dvd n this, ← Nat.dvd_iff_mod_eq_zero])
    have hQU : ∀ n, (∀ q ∈ U, ¬ q ∣ n % ∏ r ∈ U, r ^ 2) ↔ (∀ q ∈ U, ¬ q ∣ n) := fun n => by
      refine forall₂_congr fun q hq => not_congr ?_
      have hq_dvd : q ∣ ∏ r ∈ U, r ^ 2 :=
        dvd_trans (dvd_pow_self q (by norm_num)) (Finset.dvd_prod_of_mem _ hq)
      rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd n hq_dvd, ← Nat.dvd_iff_mod_eq_zero]
    rw [card_filter_mul_coprime ha2_pos hU_pos hcop
        (fun n => ¬ a ∣ n) (fun n => ∀ q ∈ U, ¬ q ∣ n) hPa hQU,
      card_not_dvd_sq hap, ih hUprime]

private lemma mem_A_iff_good {T : Finset ℕ} (hT : ∀ q ∈ T, q.Prime) (n : ℕ) :
    (∑ q ∈ T, n.factorization q = 1) ↔
      ∃ r ∈ T, (r ∣ n ∧ ¬ r ^ 2 ∣ n) ∧ ∀ q ∈ T.erase r, ¬ q ∣ n := by
  by_cases hn0 : n = 0
  · subst hn0
    simp only [Nat.factorization_zero, Finsupp.coe_zero, Pi.zero_apply, Finset.sum_const_zero,
      zero_ne_one, false_iff, not_exists]
    intro r ⟨_, ⟨_, hndvd⟩, _⟩
    exact hndvd (dvd_zero _)
  · constructor
    · intro hsum
      have hex : ∃ r ∈ T, n.factorization r ≠ 0 := by
        by_contra hall
        push Not at hall
        rw [Finset.sum_eq_zero hall] at hsum
        exact zero_ne_one hsum
      obtain ⟨r, hrT, hr_ne0⟩ := hex
      have hsplit : n.factorization r + ∑ q ∈ T.erase r, n.factorization q = 1 := by
        rw [Finset.add_sum_erase _ _ hrT, hsum]
      have hrf : n.factorization r = 1 := by omega
      have her0 : ∑ q ∈ T.erase r, n.factorization q = 0 := by omega
      have hrp : r.Prime := hT r hrT
      refine ⟨r, hrT, ⟨?_, ?_⟩, ?_⟩
      · have := (hrp.pow_dvd_iff_le_factorization hn0).mpr (show 1 ≤ n.factorization r by omega)
        simpa using this
      · intro h2
        have := (hrp.pow_dvd_iff_le_factorization hn0).mp h2
        omega
      · intro q hq hdvd
        have hqp : q.Prime := hT q (Finset.mem_of_mem_erase hq)
        have hqf0 : n.factorization q = 0 := (Finset.sum_eq_zero_iff.mp her0) q hq
        have h1 := (hqp.pow_dvd_iff_le_factorization hn0).mp (show q ^ 1 ∣ n by simpa using hdvd)
        omega
    · rintro ⟨r, hrT, ⟨hr1, hr2⟩, hother⟩
      have hrp : r.Prime := hT r hrT
      have hrf1 : 1 ≤ n.factorization r :=
        (hrp.pow_dvd_iff_le_factorization hn0).mp (by simpa using hr1)
      have hrf2 : ¬ 2 ≤ n.factorization r := fun h =>
        hr2 ((hrp.pow_dvd_iff_le_factorization hn0).mpr h)
      have hrf : n.factorization r = 1 := by omega
      have hzero : ∀ q ∈ T.erase r, n.factorization q = 0 := by
        intro q hq
        have hqp : q.Prime := hT q (Finset.mem_of_mem_erase hq)
        by_contra hne
        have hge1 : 1 ≤ n.factorization q := Nat.pos_of_ne_zero hne
        have hdvd : q ^ 1 ∣ n := (hqp.pow_dvd_iff_le_factorization hn0).mpr hge1
        exact hother q hq (by simpa using hdvd)
      rw [← Finset.add_sum_erase _ _ hrT, hrf, Finset.sum_eq_zero hzero, add_zero]

private lemma hasDensity_of_periodic {A : Set ℕ} [DecidablePred (· ∈ A)] {M : ℕ} (hM : 0 < M)
    (hper : ∀ n : ℕ, n % M ∈ A ↔ n ∈ A) :
    A.HasDensity ((((Finset.range M).filter (· ∈ A)).card : ℝ) / (M : ℝ)) := by
  let c : ℕ := ((Finset.range M).filter (· ∈ A)).card
  have hmul : ∀ q : ℕ, ((Finset.range (q * M)).filter (· ∈ A)).card = q * c := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      have hsplit : (Finset.range ((q + 1) * M)).filter (· ∈ A) =
          (Finset.range (q * M)).filter (· ∈ A) ∪
            (Finset.Ico (q * M) ((q + 1) * M)).filter (· ∈ A) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
        constructor
        · rintro ⟨hn, hA⟩
          by_cases hlt : n < q * M
          · exact Or.inl ⟨hlt, hA⟩
          · exact Or.inr ⟨⟨Nat.le_of_not_lt hlt, hn⟩, hA⟩
        · rintro (⟨hlt, hA⟩ | ⟨⟨_, hlt⟩, hA⟩)
          · exact ⟨lt_of_lt_of_le hlt (by nlinarith), hA⟩
          · exact ⟨hlt, hA⟩
      have hdisj : Disjoint ((Finset.range (q * M)).filter (· ∈ A))
          ((Finset.Ico (q * M) ((q + 1) * M)).filter (· ∈ A)) :=
        Finset.disjoint_left.mpr fun n h1 h2 => by
          have h1' := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
          have h2' := (Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).1
          omega
      have hmul_add : (q + 1) * M = q * M + M := by ring
      have hblock : ((Finset.Ico (q * M) ((q + 1) * M)).filter (· ∈ A)).card = c := by
        refine Finset.card_bij (fun n _ => n - q * M) ?_ ?_ ?_
        · intro n hn
          rcases Finset.mem_filter.mp hn with ⟨hIco, hA⟩
          rcases Finset.mem_Ico.mp hIco with ⟨hle, hlt⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
          have hmod : (n - q * M) % M = n % M := by
            have hadd : q * M + (n - q * M) = n := by omega
            rw [← Nat.mul_add_mod_self_right q M (n - q * M), hadd]
          exact (hper (n - q * M)).mp (hmod.symm ▸ (hper n).mpr hA)
        · intro n₁ hn₁ n₂ hn₂ heq
          have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₁).1).1
          have h2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₂).1).1
          omega
        · intro r hr
          rcases Finset.mem_filter.mp hr with ⟨hr_lt, hAr⟩
          rw [Finset.mem_range] at hr_lt
          refine ⟨q * M + r, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩,
            by omega⟩
          have hmod : (q * M + r) % M = r % M := by rw [Nat.mul_add_mod_self_right]
          exact (hper (q * M + r)).mp (hmod.symm ▸ (hper r).mpr hAr)
      rw [hsplit, Finset.card_union_of_disjoint hdisj, ih, hblock]
      ring
  have hcard : ∀ n : ℕ, (A ∩ Set.Iio n).ncard = ((Finset.range n).filter (· ∈ A)).card := by
    intro n
    have hset : A ∩ Set.Iio n = ↑((Finset.range n).filter (· ∈ A)) := by
      ext m
      simp [Set.mem_Iio, and_comm]
    rw [hset, Set.ncard_coe_finset]
  rw [Set.HasDensity]
  have hpd : ∀ n : ℕ, A.partialDensity Set.univ n =
      (((Finset.range n).filter (· ∈ A)).card : ℝ) / (n : ℝ) := by
    intro n
    rw [Set.partialDensity, Set.inter_univ, Set.univ_inter, hcard, Nat.ncard_Iio]
  simp only [hpd]
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hbdd : ∀ n : ℕ, 1 ≤ n →
      (c : ℝ) / (M : ℝ) - (c : ℝ) * (1 / (n : ℝ)) ≤
        (((Finset.range n).filter (· ∈ A)).card : ℝ) / (n : ℝ) ∧
      (((Finset.range n).filter (· ∈ A)).card : ℝ) / (n : ℝ) ≤
        (c : ℝ) / (M : ℝ) + (c : ℝ) * (1 / (n : ℝ)) := by
    intro n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    let q := n / M
    have hq_le : q * M ≤ n := Nat.div_mul_le_self n M
    have hq_lt : n < (q + 1) * M := by
      have h1 : q * M + n % M = n := by
        dsimp only [q]
        rw [mul_comm]
        exact Nat.div_add_mod n M
      have h2 := Nat.mod_lt n hM
      nlinarith
    have hlo_nat : q * c ≤ ((Finset.range n).filter (· ∈ A)).card := by
      rw [← hmul q]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hq_le))
    have hhi_nat : ((Finset.range n).filter (· ∈ A)).card ≤ (q + 1) * c := by
      rw [← hmul (q + 1)]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hq_lt.le))
    have hlo : (q : ℝ) * (c : ℝ) ≤ (((Finset.range n).filter (· ∈ A)).card : ℝ) := by
      exact_mod_cast hlo_nat
    have hhi : (((Finset.range n).filter (· ∈ A)).card : ℝ) ≤ ((q : ℝ) + 1) * (c : ℝ) := by
      exact_mod_cast hhi_nat
    have hqM_le : (q : ℝ) * (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hq_le
    have hqM_gt : (n : ℝ) < ((q : ℝ) + 1) * (M : ℝ) := by exact_mod_cast hq_lt
    have hc_nonneg : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
    constructor
    · rw [le_div_iff₀ hn_pos]
      have h1 : ((c : ℝ) / (M : ℝ) - (c : ℝ) * (1 / (n : ℝ))) * (n : ℝ) * (M : ℝ) =
          (c : ℝ) * ((n : ℝ) - (M : ℝ)) := by
        field_simp [hM_pos.ne', hn_pos.ne']
      have h2 : (c : ℝ) * ((n : ℝ) - (M : ℝ)) ≤ (q : ℝ) * (c : ℝ) * (M : ℝ) := by nlinarith
      nlinarith
    · rw [div_le_iff₀ hn_pos]
      have h1 : ((c : ℝ) / (M : ℝ) + (c : ℝ) * (1 / (n : ℝ))) * (n : ℝ) * (M : ℝ) =
          (c : ℝ) * ((n : ℝ) + (M : ℝ)) := by
        field_simp [hM_pos.ne', hn_pos.ne']
      have h2 : ((q : ℝ) + 1) * (c : ℝ) * (M : ℝ) ≤ (c : ℝ) * ((n : ℝ) + (M : ℝ)) := by nlinarith
      nlinarith
  have hlim : ∀ s : ℝ, Tendsto (fun n : ℕ => (c : ℝ) / (M : ℝ) + s * (1 / (n : ℝ)))
      atTop (𝓝 ((c : ℝ) / (M : ℝ))) := fun s => by
    simpa using Tendsto.const_add ((c : ℝ) / (M : ℝ))
      (Tendsto.const_mul s tendsto_one_div_atTop_nhds_zero_nat)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa [sub_eq_add_neg, neg_mul] using hlim (-(c : ℝ)))
    (hlim (c : ℝ))
    (eventually_atTop.mpr ⟨1, fun n hn => by simpa [sub_eq_add_neg, neg_mul] using (hbdd n hn).1⟩)
    (eventually_atTop.mpr ⟨1, fun n hn => (hbdd n hn).2⟩)

private lemma hasDensity_selfridge_set {T : Finset ℕ} (hT : ∀ q ∈ T, q.Prime) :
    ({n : ℕ | ∑ q ∈ T, n.factorization q = 1}).HasDensity
      ((∑ r ∈ T, (1 : ℝ) / r) * ∏ q ∈ T, (1 - (1 : ℝ) / q)) := by
  let A : Set ℕ := {n : ℕ | ∑ q ∈ T, n.factorization q = 1}
  let M : ℕ := ∏ q ∈ T, q ^ 2
  have hM_pos : 0 < M := Finset.prod_pos fun q hq => pow_pos (hT q hq).pos 2
  have hper : ∀ n : ℕ, n % M ∈ A ↔ n ∈ A := by
    intro n
    simp only [A, Set.mem_ofPred_eq, mem_A_iff_good hT]
    refine exists_congr fun r => and_congr_right fun hrT => ?_
    have hr2_dvd : r ^ 2 ∣ M := Finset.dvd_prod_of_mem _ hrT
    have hr_dvd : r ∣ M := dvd_trans (dvd_pow_self r (by norm_num)) hr2_dvd
    have hr1 : r ∣ n % M ↔ r ∣ n := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd n hr_dvd, ← Nat.dvd_iff_mod_eq_zero]
    have hr2 : r ^ 2 ∣ n % M ↔ r ^ 2 ∣ n := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd n hr2_dvd, ← Nat.dvd_iff_mod_eq_zero]
    have hother : (∀ q ∈ T.erase r, ¬ q ∣ n % M) ↔ (∀ q ∈ T.erase r, ¬ q ∣ n) := by
      refine forall₂_congr fun q hq => not_congr ?_
      have hq_dvd : q ∣ M := dvd_trans (dvd_pow_self q (by norm_num))
        (Finset.dvd_prod_of_mem _ (Finset.mem_of_mem_erase hq))
      rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd n hq_dvd, ← Nat.dvd_iff_mod_eq_zero]
    rw [hr1, hr2, hother]
  have hcount : ((Finset.range M).filter (· ∈ A)).card =
      ∑ r ∈ T, (r - 1) * ∏ q ∈ T.erase r, (q * (q - 1)) := by
    let B : ℕ → Finset ℕ := fun r =>
      (Finset.range M).filter (fun n => (r ∣ n ∧ ¬ r ^ 2 ∣ n) ∧ ∀ q ∈ T.erase r, ¬ q ∣ n)
    have hfilt_eq : (Finset.range M).filter (· ∈ A) = T.biUnion B := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_biUnion, B, A, Set.mem_ofPred_eq,
        mem_A_iff_good hT]
      constructor
      · rintro ⟨hn, r, hrT, h1, h2⟩
        exact ⟨r, hrT, hn, h1, h2⟩
      · rintro ⟨r, hrT, hn, h1, h2⟩
        exact ⟨hn, r, hrT, h1, h2⟩
    have hdisj : (T : Set ℕ).PairwiseDisjoint B := by
      intro r₁ hr₁ r₂ hr₂ hne
      refine Finset.disjoint_left.mpr fun n h1 h2 => ?_
      have h1' := (Finset.mem_filter.mp h1).2
      have h2' := (Finset.mem_filter.mp h2).2
      exact h2'.2 r₁ (Finset.mem_erase.mpr ⟨hne, hr₁⟩) h1'.1.1
    rw [hfilt_eq, Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun r hrT => ?_
    have hrp : r.Prime := hT r hrT
    have hM_eq : M = r ^ 2 * ∏ q ∈ T.erase r, q ^ 2 := (Finset.mul_prod_erase T _ hrT).symm
    have hr2_pos : 0 < r ^ 2 := pow_pos hrp.pos 2
    have hU_pos : 0 < ∏ q ∈ T.erase r, q ^ 2 :=
      Finset.prod_pos fun q hq => pow_pos (hT q (Finset.mem_of_mem_erase hq)).pos 2
    have hcop : (r ^ 2).Coprime (∏ q ∈ T.erase r, q ^ 2) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hqp : q.Prime := hT q (Finset.mem_of_mem_erase hq)
      have hne : r ≠ q := (Finset.ne_of_mem_erase hq).symm
      exact ((Nat.coprime_primes hrp hqp).mpr hne).pow 2 2
    have hPr : ∀ n, (r ∣ n % r ^ 2 ∧ ¬ r ^ 2 ∣ n % r ^ 2) ↔ (r ∣ n ∧ ¬ r ^ 2 ∣ n) := fun n => by
      have hr_dvd : r ∣ r ^ 2 := dvd_pow_self r (by norm_num)
      have h1 : r ∣ n % r ^ 2 ↔ r ∣ n := by
        rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd n hr_dvd, ← Nat.dvd_iff_mod_eq_zero]
      have h2 : r ^ 2 ∣ n % r ^ 2 ↔ r ^ 2 ∣ n := by
        rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod, ← Nat.dvd_iff_mod_eq_zero]
      rw [h1, h2]
    have hQU : ∀ n, (∀ q ∈ T.erase r, ¬ q ∣ n % ∏ s ∈ T.erase r, s ^ 2) ↔
        (∀ q ∈ T.erase r, ¬ q ∣ n) := fun n => by
      refine forall₂_congr fun q hq => not_congr ?_
      have hq_dvd : q ∣ ∏ s ∈ T.erase r, s ^ 2 :=
        dvd_trans (dvd_pow_self q (by norm_num)) (Finset.dvd_prod_of_mem _ hq)
      rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd n hq_dvd, ← Nat.dvd_iff_mod_eq_zero]
    dsimp only [B]
    rw [hM_eq, card_filter_mul_coprime hr2_pos hU_pos hcop
        (fun n => r ∣ n ∧ ¬ r ^ 2 ∣ n) (fun n => ∀ q ∈ T.erase r, ¬ q ∣ n) hPr hQU,
      card_exact_dvd_sq hrp,
      card_none_dvd_prod_sq (T.erase r) fun q hq => hT q (Finset.mem_of_mem_erase hq)]
  have hdens_eq : ((((Finset.range M).filter (· ∈ A)).card : ℝ) / (M : ℝ)) =
      (∑ r ∈ T, (1 : ℝ) / r) * ∏ q ∈ T, (1 - (1 : ℝ) / q) := by
    rw [hcount, Finset.sum_mul, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun r hrT => ?_
    have hrp : r.Prime := hT r hrT
    have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hrp.ne_zero
    have hM_real : (M : ℝ) = (r : ℝ) ^ 2 * ∏ q ∈ T.erase r, (q : ℝ) ^ 2 := by
      have h1 : M = r ^ 2 * ∏ q ∈ T.erase r, q ^ 2 := (Finset.mul_prod_erase T _ hrT).symm
      have := congrArg (Nat.cast (R := ℝ)) h1
      push_cast at this
      exact this
    have hprod_split : ∏ q ∈ T, (1 - (1 : ℝ) / q) =
        (1 - (1 : ℝ) / r) * ∏ q ∈ T.erase r, (1 - (1 : ℝ) / q) :=
      (Finset.mul_prod_erase T _ hrT).symm
    have hnum_cast : (((r - 1) * ∏ q ∈ T.erase r, (q * (q - 1)) : ℕ) : ℝ) =
        ((r : ℝ) - 1) * ∏ q ∈ T.erase r, ((q : ℝ) * ((q : ℝ) - 1)) := by
      rw [Nat.cast_mul, Nat.cast_sub hrp.one_le, Nat.cast_one, Nat.cast_prod]
      congr 1
      refine Finset.prod_congr rfl fun q hq => ?_
      have hqp : q.Prime := hT q (Finset.mem_of_mem_erase hq)
      rw [Nat.cast_mul, Nat.cast_sub hqp.one_le, Nat.cast_one]
    have hratio_prod : (∏ q ∈ T.erase r, ((q : ℝ) * ((q : ℝ) - 1))) /
        (∏ q ∈ T.erase r, (q : ℝ) ^ 2) = ∏ q ∈ T.erase r, (1 - (1 : ℝ) / q) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun q hq => ?_
      have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hT q (Finset.mem_of_mem_erase hq)).ne_zero
      field_simp [hq_ne]
    rw [hnum_cast, hM_real, hprod_split, mul_div_mul_comm, hratio_prod, ← mul_assoc]
    congr 1
    field_simp [hr_ne]
  rw [← hdens_eq]
  exact hasDensity_of_periodic hM_pos hper

private lemma exp_neg_sub_two_sq_le_one_sub {x : ℝ} (hx1 : x ≤ 1 / 2) :
    Real.exp (-x - 2 * x ^ 2) ≤ 1 - x := by
  have h1 : (1 : ℝ) ≤ (1 - x) * (1 + x + 2 * x ^ 2) := by nlinarith
  have h2 : 1 + x + 2 * x ^ 2 ≤ Real.exp (x + 2 * x ^ 2) := by
    linarith [Real.add_one_le_exp (x + 2 * x ^ 2)]
  have h3 : (1 : ℝ) ≤ (1 - x) * Real.exp (x + 2 * x ^ 2) :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 (by linarith))
  have hexp_pos : 0 < Real.exp (-x - 2 * x ^ 2) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right h3 hexp_pos.le
  rw [one_mul, mul_assoc, ← Real.exp_add] at hmul
  have hzero : x + 2 * x ^ 2 + (-x - 2 * x ^ 2) = 0 := by ring
  rw [hzero, Real.exp_zero, mul_one] at hmul
  exact hmul

private lemma selfridge_main (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / rexp 1) :
    ∀ᶠ (p : ℕ) in atTop, p.Prime → ∃ k,
      ∑ q ∈ consecutivePrimesFrom p k, (1 : ℝ) / q < 1 ∧
        1 < ∑ q ∈ consecutivePrimesFrom p (k + 1), (1 : ℝ) / q ∧
          letI A := { n | ∑ q ∈ consecutivePrimesFrom p k, (n : ℕ).factorization q = 1 }
          ∃ δ, 1 / rexp 1 - ε < δ ∧ A.HasDensity δ ∧ A.IsMulCardSet := by
  let P0 : ℕ := max 3 (Nat.ceil (3 / ε) + 1)
  rw [Filter.eventually_atTop]
  refine ⟨P0, fun p hp_ge hp => ?_⟩
  obtain ⟨k, hk_lt, hk_gt, hk_lower⟩ := exists_crossing_index hp
  let T := consecutivePrimesFrom p k
  have hT_prime : ∀ q ∈ T, q.Prime := fun q hq => (mem_consecutivePrimesFrom_prime hq).1
  have hT_ge : ∀ q ∈ T, p ≤ q := fun q hq => (mem_consecutivePrimesFrom_prime hq).2
  let s : ℝ := ∑ q ∈ T, (1 : ℝ) / q
  let δ : ℝ := s * ∏ q ∈ T, (1 - (1 : ℝ) / q)
  refine ⟨k, hk_lt, hk_gt, δ, ?_, hasDensity_selfridge_set hT_prime,
    isMulCardSet_of_sum_factorization_eq_one T⟩
  have hp3 : 3 ≤ p := le_trans (le_max_left _ _) hp_ge
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hp_gt_ratio : 3 / ε < (p : ℝ) := by
    have h1 : Nat.ceil (3 / ε) + 1 ≤ p := le_trans (le_max_right _ _) hp_ge
    have h2 : (Nat.ceil (3 / ε) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast h1
    linarith [Nat.le_ceil (3 / ε)]
  have h3_div_p_lt : (3 : ℝ) / p < ε := by
    rw [div_lt_iff₀ hp_pos]
    have := (div_lt_iff₀ hε.1).mp hp_gt_ratio
    linarith
  have hprod_ge : Real.exp (-(1 + 2 / (p : ℝ)) * s) ≤ ∏ q ∈ T, (1 - (1 : ℝ) / q) := by
    have hexp_sum : Real.exp (-(1 + 2 / (p : ℝ)) * s) =
        ∏ q ∈ T, Real.exp (-(1 + 2 / (p : ℝ)) * ((1 : ℝ) / q)) := by
      dsimp only [s]
      rw [Finset.mul_sum, Real.exp_sum]
    rw [hexp_sum]
    refine Finset.prod_le_prod (fun q _ => (Real.exp_pos _).le) fun q hq => ?_
    have hq_ge_p : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hT_ge q hq
    have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
    have hxq0 : 0 ≤ (1 : ℝ) / q := by positivity
    have hxq_le_p : (1 : ℝ) / q ≤ (1 : ℝ) / p := one_div_le_one_div_of_le hp_pos hq_ge_p
    have hxq_half : (1 : ℝ) / q ≤ 1 / 2 := by
      have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have hsq_le : ((1 : ℝ) / q) ^ 2 ≤ ((1 : ℝ) / p) * ((1 : ℝ) / q) := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hxq_le_p hxq0
    have hexp_mono : Real.exp (-(1 + 2 / (p : ℝ)) * ((1 : ℝ) / q)) ≤
        Real.exp (-((1 : ℝ) / q) - 2 * ((1 : ℝ) / q) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have : -(1 + 2 / (p : ℝ)) * ((1 : ℝ) / q) =
          -((1 : ℝ) / q) - 2 * (((1 : ℝ) / p) * ((1 : ℝ) / q)) := by ring
      linarith
    exact le_trans hexp_mono (exp_neg_sub_two_sq_le_one_sub hxq_half)
  have hprod_ge2 : (1 / rexp 1) * (1 - 2 / (p : ℝ)) ≤ ∏ q ∈ T, (1 - (1 : ℝ) / q) := by
    have h1 : Real.exp (-1 - 2 / (p : ℝ)) ≤ Real.exp (-(1 + 2 / (p : ℝ)) * s) := by
      apply Real.exp_le_exp.mpr
      have hpos : 0 < 1 + 2 / (p : ℝ) := by positivity
      nlinarith [hk_lt]
    have h2 : Real.exp (-1 - 2 / (p : ℝ)) = (1 / rexp 1) * Real.exp (-(2 / (p : ℝ))) := by
      rw [show (-1 - 2 / (p : ℝ)) = (-1) + (-(2 / (p : ℝ))) by ring, Real.exp_add, Real.exp_neg,
        one_div]
    have h3 : 1 - 2 / (p : ℝ) ≤ Real.exp (-(2 / (p : ℝ))) := by
      linarith [Real.add_one_le_exp (-(2 / (p : ℝ)))]
    have he_pos : 0 < 1 / rexp 1 := by positivity
    calc
      (1 / rexp 1) * (1 - 2 / (p : ℝ)) ≤ (1 / rexp 1) * Real.exp (-(2 / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left h3 he_pos.le
      _ = Real.exp (-1 - 2 / (p : ℝ)) := h2.symm
      _ ≤ Real.exp (-(1 + 2 / (p : ℝ)) * s) := h1
      _ ≤ ∏ q ∈ T, (1 - (1 : ℝ) / q) := hprod_ge
  have h1m2_pos : 0 < 1 - 2 / (p : ℝ) := by
    have : 2 / (p : ℝ) ≤ 2 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp_real
    linarith
  have h1m1_pos : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp_real
    linarith
  have hprod_pos : 0 < (1 / rexp 1) * (1 - 2 / (p : ℝ)) := by positivity
  have hδ_gt : (1 - 1 / (p : ℝ)) * ((1 / rexp 1) * (1 - 2 / (p : ℝ))) < δ := by
    dsimp only [δ]
    calc
      (1 - 1 / (p : ℝ)) * ((1 / rexp 1) * (1 - 2 / (p : ℝ)))
          < s * ((1 / rexp 1) * (1 - 2 / (p : ℝ))) :=
            mul_lt_mul_of_pos_right hk_lower hprod_pos
      _ ≤ s * ∏ q ∈ T, (1 - (1 : ℝ) / q) :=
            mul_le_mul_of_nonneg_left hprod_ge2 (by linarith)
  have hpoly : (1 / rexp 1) * (1 - 3 / (p : ℝ)) ≤
      (1 - 1 / (p : ℝ)) * ((1 / rexp 1) * (1 - 2 / (p : ℝ))) := by
    have he_nonneg : 0 ≤ 1 / rexp 1 := by positivity
    have hsq : (1 - 3 / (p : ℝ)) ≤ (1 - 1 / (p : ℝ)) * (1 - 2 / (p : ℝ)) := by
      have : (1 - 1 / (p : ℝ)) * (1 - 2 / (p : ℝ)) - (1 - 3 / (p : ℝ)) = 2 / (p : ℝ) ^ 2 := by
        field_simp [hp_pos.ne']
        ring
      have hpos2 : 0 ≤ 2 / (p : ℝ) ^ 2 := by positivity
      linarith
    have := mul_le_mul_of_nonneg_left hsq he_nonneg
    linarith
  have he_ge_one : (1 : ℝ) ≤ rexp 1 := Real.one_le_exp (by norm_num)
  have hinv_e_le : 1 / rexp 1 ≤ 1 := by
    rw [div_le_one (Real.exp_pos 1)]
    exact he_ge_one
  have h3_e : (1 / rexp 1) * (3 / (p : ℝ)) ≤ 3 / (p : ℝ) := by
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 3) hp_pos.le]
  linarith

end Erdos786SelfridgeProof

theorem OMA.solution : type_of% @Erdos786.erdos_786.parts.i.selfridge :=
  Erdos786SelfridgeProof.selfridge_main
