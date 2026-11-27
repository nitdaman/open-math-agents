import FormalConjectures.ErdosProblems.«416»
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Nat.Squarefree

/-! # Density of Euler totient values -/

open Filter Finset
open scoped BigOperators Topology

namespace OMA.Pillai

private theorem totientReal (n : ℕ) :
    (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  exact h

-- A finite set of primes outside any prescribed set can have arbitrarily small
-- product of the factors 1 - 1/p, by divergence of the prime reciprocal sum.
private theorem smallTotient (excluded : Finset ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ q : ℕ, 0 < q ∧ (∀ p ∈ q.primeFactors, p ∉ excluded) ∧
      (q.totient : ℝ) < c * q := by
  classical
  let primeRecip (p : ℕ) : ℝ := if p.Prime then (p : ℝ)⁻¹ else 0
  let remaining (p : ℕ) : ℝ := if p.Prime ∧ p ∉ excluded then (p : ℝ)⁻¹ else 0
  let discarded (p : ℕ) : ℝ := if p ∈ excluded then primeRecip p else 0
  have hdiscard : Summable discarded :=
    summable_of_ne_finset_zero (s := excluded) fun p hp => by simp [discarded, hp]
  have hnot : ¬ Summable remaining := by
    intro h
    apply not_summable_one_div_on_primes
    convert h.add hdiscard using 1
    funext p
    by_cases hpr : p.Prime <;> by_cases hp : p ∈ excluded <;>
      simp [remaining, discarded, primeRecip, Set.indicator, hpr, hp, one_div]
  obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, -Real.log c < ∑ p ∈ s, remaining p := by
    by_contra! h
    exact hnot (summable_of_sum_le (fun p => by
      dsimp [remaining]
      split <;> positivity) h)
  let primes := s.filter fun p => p.Prime ∧ p ∉ excluded
  have hprime (p : ℕ) (hp : p ∈ primes) : p.Prime := (mem_filter.mp hp).2.1
  have hsum : -Real.log c < ∑ p ∈ primes, (p : ℝ)⁻¹ := by
    simpa only [primes, sum_filter, remaining] using hs
  let q := ∏ p ∈ primes, p
  have hq : 0 < q := prod_pos (fun p hp => (hprime p hp).pos)
  have hqf : q.primeFactors = primes := Nat.primeFactors_prod hprime
  refine ⟨q, hq, ?_, ?_⟩
  · rw [hqf]
    exact fun p hp => (mem_filter.mp hp).2.2
  · have bound : ∏ p ∈ primes, (1 - (p : ℝ)⁻¹) < c := by
      calc
        _ ≤ ∏ p ∈ primes, Real.exp (-(p : ℝ)⁻¹) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).one_lt.le
            exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp')
          · intro p hp
            simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(p : ℝ)⁻¹)
        _ = Real.exp (-(∑ p ∈ primes, (p : ℝ)⁻¹)) := by
          rw [← Real.exp_sum, Finset.sum_neg_distrib]
        _ < c := by
          rw [← Real.exp_log hc]
          exact Real.exp_lt_exp.mpr (by linarith)
    rw [totientReal, hqf, mul_comm c]
    exact mul_lt_mul_of_pos_left bound (by exact_mod_cast hq)

private def coprimeUpTo (q x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun n => q.Coprime n

private theorem cardCoprimeUpTo {q : ℕ} (hq : 0 < q) (x : ℕ) :
    (coprimeUpTo q x).card ≤ (x / q + 1) * q.totient := by
  let residues := (range q).filter fun r => q.Coprime r
  have hres : residues.card = q.totient := (Nat.totient_eq_card_coprime q).symm
  rw [← hres, ← card_range (x / q + 1), ← card_product]
  apply card_le_card_of_injOn (fun n => (n / q, n % q))
  · intro n hn
    have hn' := mem_filter.mp (show n ∈ coprimeUpTo q x from hn)
    have hx : n ≤ x := (mem_Icc.mp hn'.1).2
    have hr : q.Coprime (n % q) := by
      change q.gcd (n % q) = 1
      rw [Nat.gcd_comm q (n % q), ← Nat.gcd_rec q n]
      exact hn'.2
    exact mem_product.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hx)),
       mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hq), hr⟩⟩
  · intro a ha b hb e
    have e₁ := congrArg Prod.fst e
    have e₂ := congrArg Prod.snd e
    change a / q = b / q at e₁
    change a % q = b % q at e₂
    simpa only [Nat.mod_add_div] using congrArg₂ (fun d r => r + q * d) e₁ e₂

private theorem eventuallyCoprime {q : ℕ} (hq : 0 < q) {c : ℝ} (hc : 0 < c)
    (ht : (q.totient : ℝ) ≤ (c / 2) * q) :
    ∀ᶠ x : ℕ in atTop, ((coprimeUpTo q x).card : ℝ) ≤ c * x := by
  filter_upwards [eventually_ge_atTop q] with x hx
  have hbound : (x / q + 1) * q ≤ 2 * x := by
    rw [add_mul, one_mul, two_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self x q) hx
  calc
    _ ≤ ((x / q + 1 : ℕ) : ℝ) * (q.totient : ℝ) := by
      exact_mod_cast cardCoprimeUpTo hq x
    _ ≤ ((x / q + 1 : ℕ) : ℝ) * ((c / 2) * q) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (c / 2) * (((x / q + 1 : ℕ) : ℝ) * q) := by ring
    _ ≤ (c / 2) * (2 * x) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hbound) (by positivity)
    _ = c * x := by ring

private def fewPrimeFactors (k : ℕ) (excluded : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun n => (n.primeFactors \ excluded).card ≤ k

private theorem commonPrime {q n : ℕ} (hq : q ≠ 0) (hn : n ≠ 0) (h : ¬ q.Coprime n) :
    ∃ p ∈ q.primeFactors, p ∈ n.primeFactors := by
  obtain ⟨p, hp, hpq, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpq, hq⟩, Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩⟩

-- In each induction step the coprime numbers are sparse. The remaining numbers
-- use at least one prime of q, which can be added to the excluded set.
private theorem eventuallyFewPrimeFactors (k : ℕ) (excluded : Finset ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ((fewPrimeFactors k excluded x).card : ℝ) ≤ c * x := by
  induction k generalizing excluded c with
  | zero =>
    obtain ⟨q, hq, hdis, ht⟩ := smallTotient excluded (half_pos hc)
    filter_upwards [eventuallyCoprime hq hc ht.le] with x hx
    apply le_trans _ hx
    apply Nat.cast_le.mpr
    apply card_le_card
    intro n hn
    have hn' := mem_filter.mp (show n ∈ fewPrimeFactors 0 excluded x from hn)
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn'.1).1; omega
    refine mem_filter.mpr ⟨hn'.1, ?_⟩
    by_contra hcop
    obtain ⟨p, hpq, hpn⟩ := commonPrime hq.ne' hn0 hcop
    have hp : p ∈ n.primeFactors \ excluded := mem_sdiff.mpr ⟨hpn, hdis p hpq⟩
    have := card_pos.mpr ⟨p, hp⟩
    omega
  | succ k ih =>
    obtain ⟨q, hq, hdis, ht⟩ := smallTotient excluded (half_pos (half_pos hc))
    filter_upwards [eventuallyCoprime hq (half_pos hc) ht.le,
      ih (excluded ∪ q.primeFactors) (half_pos hc)] with x hcop hfew
    have hsubset : fewPrimeFactors (k + 1) excluded x ⊆
        coprimeUpTo q x ∪ fewPrimeFactors k (excluded ∪ q.primeFactors) x := by
      intro n hn
      have hn' := mem_filter.mp (show n ∈ fewPrimeFactors (k + 1) excluded x from hn)
      by_cases h : q.Coprime n
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hn'.1, h⟩))
      · have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn'.1).1; omega
        obtain ⟨p, hpq, hpn⟩ := commonPrime hq.ne' hn0 h
        have hlt : (n.primeFactors \ (excluded ∪ q.primeFactors)).card <
            (n.primeFactors \ excluded).card := by
          apply card_lt_card
          apply ssubset_iff_subset_ne.mpr
          refine ⟨?_, ?_⟩
          · intro a ha
            rcases mem_sdiff.mp ha with ⟨ha₁, ha₂⟩
            exact mem_sdiff.mpr ⟨ha₁, fun ha₃ => ha₂ (mem_union_left _ ha₃)⟩
          · intro heq
            have hp : p ∈ n.primeFactors \ (excluded ∪ q.primeFactors) :=
              heq.symm ▸ mem_sdiff.mpr ⟨hpn, hdis p hpq⟩
            exact (mem_sdiff.mp hp).2 (mem_union_right _ hpq)
        exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hn'.1, by omega⟩))
    have hcard := (card_le_card hsubset).trans (card_union_le _ _)
    calc
      _ ≤ ((coprimeUpTo q x).card : ℝ) +
          ((fewPrimeFactors k (excluded ∪ q.primeFactors) x).card : ℝ) := by
        exact_mod_cast hcard
      _ ≤ (c / 2) * x + (c / 2) * x := add_le_add hcop hfew
      _ = c * x := by ring

private theorem twoPowDvdTotient {k n : ℕ} (hn : k < n.primeFactors.card) :
    2 ^ k ∣ n.totient := by
  let oddPrimes := n.primeFactors.erase 2
  have hk : k ≤ oddPrimes.card := by
    by_cases h : 2 ∈ n.primeFactors
    · rw [show oddPrimes.card = n.primeFactors.card - 1 from card_erase_of_mem h]
      omega
    · simpa [oddPrimes, erase_eq_of_notMem h] using hn.le
  have hprod : 2 ^ oddPrimes.card ∣ ∏ p ∈ oddPrimes, (p - 1) := by
    rw [← Finset.prod_const]
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    exact ((Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2).even_sub_one
      (mem_erase.mp hp).1).two_dvd
  have hfactor : (∏ p ∈ oddPrimes, (p - 1)) ∣ n.totient := by
    rw [Nat.totient_eq_div_primeFactors_mul]
    exact (Finset.prod_dvd_prod_of_subset _ _ _ (erase_subset _ _)).trans (Nat.dvd_mul_left _ _)
  exact (Nat.pow_dvd_pow 2 hk).trans (hprod.trans hfactor)

private theorem leTwoPowTotient {k n : ℕ} (hk : n.primeFactors.card ≤ k) :
    n ≤ 2 ^ k * n.totient := by
  have hprod : (1 / 2 : ℝ) ^ n.primeFactors.card ≤
      ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => by norm_num)
    intro p hp
    have h₂ : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 2) h₂
    linarith
  have h : (n : ℝ) * (1 / 2 : ℝ) ^ k ≤ (n.totient : ℝ) := by
    rw [totientReal]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk).trans hprod
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ (2 : ℝ) ^ k by positivity)
  rw [mul_left_comm ((2 : ℝ) ^ k)] at hmul
  rw [← mul_pow] at hmul
  norm_num at hmul
  exact_mod_cast hmul

private theorem cardMultiples {d : ℕ} (hd : 0 < d) (x : ℕ) :
    ((Icc 1 x).filter fun n => d ∣ n).card ≤ x / d := by
  have hquot : (Icc 1 (x / d)).card = x / d := by simp [Nat.card_Icc]
  rw [← hquot]
  apply card_le_card_of_injOn (fun n => n / d)
  · intro n hn
    obtain ⟨hnI, hnD⟩ := mem_filter.mp (show n ∈ (Icc 1 x).filter (fun j => d ∣ j) from hn)
    have hnP : 0 < n := (mem_Icc.mp hnI).1
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hnP hnD) hd,
      Nat.div_le_div_right (mem_Icc.mp hnI).2⟩
  · intro a ha b hb h
    have haD := (mem_filter.mp (show a ∈ (Icc 1 x).filter (fun j => d ∣ j) from ha)).2
    have hbD := (mem_filter.mp (show b ∈ (Icc 1 x).filter (fun j => d ∣ j) from hb)).2
    simpa only [Nat.div_mul_cancel haD, Nat.div_mul_cancel hbD] using congrArg (· * d) h

open scoped Classical in
private theorem countTotients (x k : ℕ) :
    let values := (Icc 1 x).filter fun n => ∃ m : ℕ, m.totient = n
    values.card ≤ x / 2 ^ k + (fewPrimeFactors k ∅ (2 ^ k * x)).card := by
  classical
  dsimp only
  let values := (Icc 1 x).filter fun n => ∃ m : ℕ, m.totient = n
  let multiples := (Icc 1 x).filter fun n => 2 ^ k ∣ n
  let sparse := fewPrimeFactors k ∅ (2 ^ k * x)
  have hs : values ⊆ multiples ∪ sparse.image Nat.totient := by
    intro v hv
    obtain ⟨hvI, n, rfl⟩ := mem_filter.mp hv
    by_cases hn : k < n.primeFactors.card
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hvI, twoPowDvdTotient hn⟩))
    · have hn0 : 1 ≤ n := (mem_Icc.mp hvI).1.trans (Nat.totient_le n)
      have hnX : n ≤ 2 ^ k * x :=
        (leTwoPowTotient (Nat.le_of_not_gt hn)).trans (Nat.mul_le_mul_left _ (mem_Icc.mp hvI).2)
      exact mem_union.mpr (Or.inr (mem_image.mpr ⟨n,
        mem_filter.mpr ⟨mem_Icc.mpr ⟨hn0, hnX⟩, by simpa using Nat.le_of_not_gt hn⟩, rfl⟩))
  exact (card_le_card hs).trans ((card_union_le _ _).trans
    (Nat.add_le_add (cardMultiples (by positivity) x) card_image_le))

end OMA.Pillai

open OMA.Pillai

theorem OMA.solution : type_of% @Erdos416.erdos_416.variants.Pillai := by
  change Erdos416.V =o[atTop] (id : ℝ → ℝ)
  classical
  refine Asymptotics.isLittleO_iff.mpr ?_
  intro c hc
  have hpow : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨k, hk⟩ := (hpow.eventually_ge_atTop (2 / c)).exists
  let d : ℕ := 2 ^ k
  have hd : 0 < d := by dsimp [d]; positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdc : (1 : ℝ) / d ≤ c / 2 := by
    apply (div_le_iff₀ hdR).mpr
    have h := (div_le_iff₀ hc).mp hk
    push_cast [d]
    linarith
  have hxlim : Tendsto (fun x : ℝ => d * ⌊x⌋₊) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_nat_floor_atTop
    intro x
    exact Nat.le_mul_of_pos_left _ hd
  have hfew := hxlim.eventually (eventuallyFewPrimeFactors k ∅
    (c := c / (2 * d)) (by positivity))
  filter_upwards [hfew, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have hV : 0 ≤ Erdos416.V x := by positivity
  rw [Real.norm_of_nonneg hV, id_eq, Real.norm_of_nonneg hx0]
  have hc₁ : (⌊x⌋₊ / d : ℕ) * d ≤ ⌊x⌋₊ := Nat.div_mul_le_self _ _
  have hc₂ : ((⌊x⌋₊ / d : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) / d :=
    (le_div_iff₀ hdR).mpr (by exact_mod_cast hc₁)
  have hcount : Erdos416.V x ≤ ((⌊x⌋₊ / d : ℕ) : ℝ) +
      ((fewPrimeFactors k ∅ (d * ⌊x⌋₊)).card : ℝ) := by
    exact_mod_cast countTotients ⌊x⌋₊ k
  calc
    _ ≤ ((⌊x⌋₊ / d : ℕ) : ℝ) + ((fewPrimeFactors k ∅ (d * ⌊x⌋₊)).card : ℝ) := hcount
    _ ≤ (⌊x⌋₊ : ℝ) / d + c / (2 * d) * ((d * ⌊x⌋₊ : ℕ) : ℝ) := add_le_add hc₂ hx
    _ = ((1 : ℝ) / d) * (⌊x⌋₊ : ℝ) + (c / 2) * (⌊x⌋₊ : ℝ) := by
      push_cast
      field_simp
      <;> ring
    _ ≤ (c / 2) * (⌊x⌋₊ : ℝ) + (c / 2) * (⌊x⌋₊ : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_right hdc (by positivity)) le_rfl
    _ = c * (⌊x⌋₊ : ℝ) := by ring
    _ ≤ c * x := mul_le_mul_of_nonneg_left (Nat.floor_le hx0) hc.le
