import OMAReductions.R_Erdos1052_erdos_1052_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1
-- Credit: @adammcarter
-- Splits step H2 of Erdos1052.erdos_1052.R1 (the 2-adic valuation is bounded over the unitary
-- perfect numbers whose odd part is not squarefree) into two sub-families.  Each H becomes its
-- own step once this file is accepted; proving both proves the step.
--
-- Notation: n unitary perfect, a = padicValNat 2 n, S = the set of odd primes p with p^2 | n
-- (the non-simple odd primes; S is nonempty exactly when the odd part is not squarefree).
-- A finite set N of primes is ADMISSIBLE when every z in N satisfies z >= 128 and
-- z >= N.card + 3, and the product over N of (z + 1) / (z - 2 - N.card) is at most 2101/2097.
--
-- PROVED BELOW, no hypothesis needed (two_adic_le_nine_of_sparse_nonsimple): Graham's 1989
-- argument for squarefree odd part (S. W. Graham, Fibonacci Quart. 27 (1989), 317-322),
-- extended to a sparse set of large non-simple primes.  If N is admissible and contains S, then
-- a <= 9 unless n is in the RESIDUE for N:
--   4 | a,  3 | n,  some z in N with z = 2 mod 3 divides 2^a + 1,  and every z in N with
--   z = 2 mod 3 has even exponent in n.
-- (N = {} gives back the a >= 10 half of Graham's theorem.  By hand arithmetic N = {z} with z prime
-- is admissible exactly when z >= 2100; that any N whose primes are all >= 600 * (N.card + 2)^2 is
-- admissible is proved in the round-2 working file, not repeated here.)
-- Also proved: admissible_of_subset, a subset of an admissible set is admissible, so S is
-- admissible exactly when some admissible N contains S.
--
-- H1 (OPEN, small or dense kernel): a is bounded over the n whose set S is NOT admissible,
--    i.e. some non-simple odd prime is below 128 or below S.card + 3, or the product over S of
--    (z + 1) / (z - 2 - S.card) exceeds 2101/2097.  For one non-simple prime z this says z < 2100
--    (hand arithmetic).
--    It contains the known examples 90 = 2 * 3^2 * 5 (S = {3}) and Wall's 2^18 * 3 * 5^4 * ...
--    (S = {5}, a = 18); even the case S = {3} is open.
-- H2 (OPEN, residue): a is bounded over the n whose set S IS admissible but which are in the
--    residue for every admissible N containing S (in particular 4 | a and 3 | n).  N may contain
--    simple primes too; by admissible_of_subset this says (hand argument): the residue holds for
--    N = S, and no simple prime of n that is = 2 mod 3 can be added to S keeping it admissible.
--    No known unitary perfect number is in this family.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1

-- The 2-adic valuation is bounded over the unitary perfect numbers with non-squarefree odd part
-- whose set S of non-simple odd primes is not admissible.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    padicValNat 2 n ≤ A

-- The 2-adic valuation is bounded over the unitary perfect numbers with non-squarefree odd part
-- whose set S is admissible, with 4 | a and 3 | n, such that every admissible set N of primes
-- containing S has a prime z = 2 mod 3 dividing 2^a + 1 and gives an even exponent to every
-- z = 2 mod 3 in N.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    padicValNat 2 n ≤ A

-- Section 0 onwards: lemmas repeated from Erdos1052OpenCore2.lean (round 2).

-- Section 0. Product formula for the unitary divisor sum.

theorem mem_udiv {n d : ℕ} :
    d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors ↔ d ∣ n ∧ n ≠ 0 ∧ d.Coprime (n / d) := by
  simp [and_assoc]

theorem self_mem_udiv {n : ℕ} (hn : n ≠ 0) :
    n ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors := by
  rw [mem_udiv, Nat.div_self (Nat.pos_of_ne_zero hn)]
  exact ⟨dvd_rfl, hn, Nat.coprime_one_right n⟩

theorem proper_eq_erase (n : ℕ) :
    Erdos1052.properUnitaryDivisors n = (Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors).erase n := by
  ext d
  simp only [Erdos1052.properUnitaryDivisors, Finset.mem_filter, Finset.mem_Ico, Finset.mem_erase,
    Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd, hc⟩
    exact ⟨h2.ne, ⟨hd, by omega⟩, hc⟩
  · rintro ⟨hne, ⟨hd, hn⟩, hc⟩
    have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
    exact ⟨⟨Nat.pos_of_ne_zero hd0,
      lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hne⟩, hd, hc⟩

theorem sum_udiv_eq_sum_proper_add {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d =
      (∑ i ∈ Erdos1052.properUnitaryDivisors n, i) + n := by
  rw [proper_eq_erase, Finset.sum_erase_add _ _ (self_mem_udiv hn)]

-- A unitary perfect number is positive and its unitary divisor sum equals 2 * n.
theorem sum_udiv_of_isUnitaryPerfect {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    0 < n ∧ ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d = 2 * n := by
  obtain ⟨hs, hpos⟩ := h
  refine ⟨hpos, ?_⟩
  rw [sum_udiv_eq_sum_proper_add hpos.ne', hs]
  ring

theorem factorization_of_mem_udiv {n d : ℕ}
    (h : d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors) (p : ℕ) :
    d.factorization p = if p ∈ d.primeFactors then n.factorization p else 0 := by
  obtain ⟨hd, hn, hc⟩ := mem_udiv.mp h
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  have hq : n / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) (Nat.pos_of_ne_zero hd0)).ne'
  have hmul : n = d * (n / d) := (Nat.mul_div_cancel' hd).symm
  split_ifs with hp
  · have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hnd : ¬ p ∣ n / d := by
      intro h'
      have := Nat.dvd_gcd hpd h'
      rw [hc.gcd_eq_one] at this
      exact hpp.not_dvd_one this
    conv_rhs => rw [hmul]
    rw [Nat.factorization_mul hd0 hq, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
  · by_contra h'
    exact hp (Nat.support_factorization d ▸ Finsupp.mem_support_iff.mpr h')

theorem ppart_ne_zero {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    ∏ p ∈ S, p ^ n.factorization p ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero

theorem factorization_ppart {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) (q : ℕ) :
    (∏ p ∈ S, p ^ n.factorization p).factorization q = if q ∈ S then n.factorization q else 0 := by
  rw [Nat.factorization_prod (fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by
    rw [(Nat.prime_of_mem_primeFactors (hS hp)).factorization_pow, Finsupp.single_apply])]
  exact Finset.sum_ite_eq' S q _

theorem primeFactors_ppart {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p).primeFactors = S := by
  ext q
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_ppart hS]
  split_ifs with h
  · simp only [h, iff_true]
    exact Finsupp.mem_support_iff.mp (by rw [Nat.support_factorization]; exact hS h)
  · simp [h]

theorem ppart_mem_udiv {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p) ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors := by
  have h0 := ppart_ne_zero hS
  have hdvd : (∏ p ∈ S, p ^ n.factorization p) ∣ n := by
    rw [← Nat.factorization_le_iff_dvd h0 hn]
    intro q
    rw [factorization_ppart hS]
    split_ifs <;> simp
  refine mem_udiv.mpr ⟨hdvd, hn, Nat.coprime_of_dvd fun p hp h1 h2 => ?_⟩
  have hq : n / (∏ p ∈ S, p ^ n.factorization p) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero h0)).ne'
  have e1 := (hp.dvd_iff_one_le_factorization h0).mp h1
  have e2 := (hp.dvd_iff_one_le_factorization hq).mp h2
  rw [factorization_ppart hS] at e1
  rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, factorization_ppart hS] at e2
  split_ifs at e1 e2 <;> omega

theorem eq_ppart_of_mem_udiv {n d : ℕ}
    (h : d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors) :
    d = ∏ p ∈ d.primeFactors, p ^ n.factorization p := by
  obtain ⟨hd, hn, -⟩ := mem_udiv.mp h
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  have hsub := Nat.primeFactors_mono hd hn
  exact Nat.eq_of_factorization_eq hd0 (ppart_ne_zero hsub) fun q => by
    rw [factorization_of_mem_udiv h, factorization_ppart hsub]

-- Product formula: the unitary divisor sum of n is the product of (1 + p^a) over p^a || n.
theorem sum_udiv_eq_prod {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d =
      ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
  rw [Finset.prod_one_add]
  exact Finset.sum_nbij' (fun d => d.primeFactors) (fun S => ∏ p ∈ S, p ^ n.factorization p)
    (fun d hd => Finset.mem_powerset.mpr (Nat.primeFactors_mono (mem_udiv.mp hd).1 hn))
    (fun S hS => ppart_mem_udiv hn (Finset.mem_powerset.mp hS))
    (fun d hd => (eq_ppart_of_mem_udiv hd).symm)
    (fun S hS => primeFactors_ppart (Finset.mem_powerset.mp hS))
    (fun d hd => eq_ppart_of_mem_udiv hd)

theorem prod_primeFactors_pow_self {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
  (eq_ppart_of_mem_udiv (self_mem_udiv hn)).symm

-- Balance equation: for a unitary perfect n the product of (1 + p^a) over p^a || n is 2 * n.
theorem prod_eq_two_mul {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) = 2 * n := by
  obtain ⟨hpos, hs⟩ := sum_udiv_of_isUnitaryPerfect h
  rw [← sum_udiv_eq_prod hpos.ne']
  exact hs

-- Section 1. Telescoping bounds.

theorem B_step {c p : ℕ} (hc : 2 ≤ c) (hp : 2 * c ≤ p + 1) :
    (1 + 1 / (c : ℚ)) * (((p : ℚ) + 1) / ((p : ℚ) - 1)) ≤ ((c : ℚ) + 1) / ((c : ℚ) - 1) := by
  have hc' : (2 : ℚ) ≤ c := by exact_mod_cast hc
  have hp' : 2 * (c : ℚ) ≤ p + 1 := by exact_mod_cast hp
  have h1 : (0 : ℚ) < c - 1 := by linarith
  have h2 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have h3 : (0 : ℚ) < c := by linarith
  have e : (1 + 1 / (c : ℚ)) = ((c : ℚ) + 1) / c := by field_simp
  rw [e, div_mul_div_comm, div_le_div_iff₀ (mul_pos h3 h2) h1]
  nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ (c : ℚ) + 1) (by linarith : (0 : ℚ) ≤ (p : ℚ) + 1 - 2 * c)]

theorem B_anti {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ((b : ℚ) + 1) / ((b : ℚ) - 1) ≤ ((a : ℚ) + 1) / ((a : ℚ) - 1) := by
  have ha' : (2 : ℚ) ≤ a := by exact_mod_cast ha
  have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem one_add_le_B {p : ℕ} (hp : 2 ≤ p) :
    1 + 1 / (p : ℚ) ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
  have hp' : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have e : (1 + 1 / (p : ℚ)) = ((p : ℚ) + 1) / p := by field_simp
  rw [e, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem path_bound (g : ℕ → ℕ) (β : ℕ → ℚ) : ∀ (n : ℕ) (P : Finset ℕ), P.card = n →
    (∀ p ∈ P, 0 < p) →
    (∀ p ∈ P, g p ∈ P → g p < p) →
    (∀ p ∈ P, ∀ p' ∈ P, g p ∈ P → g p = g p' → p = p') →
    (∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p) →
    (∀ p ∈ P, g p ∈ P → (1 + 1 / ((g p : ℕ) : ℚ)) * β p ≤ β (g p)) →
    ∏ p ∈ P, (1 + 1 / (p : ℚ)) ≤ ∏ q ∈ P.filter (fun q => g q ∉ P), β q := by
  intro n
  induction n with
  | zero =>
    intro P hP _ _ _ _ _
    rw [Finset.card_eq_zero.mp hP]
    simp
  | succ n ih =>
    intro P hcard hpos hlt hinj hβ hstep
    have hne : P.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, hqP, hqmin⟩ : ∃ q ∈ P, ∀ p ∈ P, q ≤ p :=
      ⟨P.min' hne, Finset.min'_mem P hne, fun p hp => Finset.min'_le P p hp⟩
    have hgq : g q ∉ P := fun h => absurd (hqmin _ h) (not_le.mpr (hlt q hqP h))
    have hβpos : ∀ p ∈ P, 0 < β p := fun p hp => by
      have h0 : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
      linarith [hβ p hp]
    have hmem : ∀ x, x ∈ P.erase q → x ∈ P := fun x hx => Finset.mem_of_mem_erase hx
    have ih' := ih (P.erase q) (by rw [Finset.card_erase_of_mem hqP, hcard]; rfl)
      (fun p hp => hpos p (hmem p hp))
      (fun p hp hg => hlt p (hmem p hp) (hmem _ hg))
      (fun p hp p' hp' hg he => hinj p (hmem p hp) p' (hmem p' hp') (hmem _ hg) he)
      (fun p hp => hβ p (hmem p hp))
      (fun p hp hg => hstep p (hmem p hp) (hmem _ hg))
    have hqL : q ∈ P.filter (fun q => g q ∉ P) := Finset.mem_filter.mpr ⟨hqP, hgq⟩
    have hrest0 : 0 ≤ ∏ x ∈ (P.filter (fun q => g q ∉ P)).erase q, β x :=
      Finset.prod_nonneg fun x hx =>
        (hβpos x (Finset.mem_filter.mp (Finset.mem_of_mem_erase hx)).1).le
    have hq0 : (0 : ℚ) ≤ 1 + 1 / (q : ℚ) := by positivity
    have key : (1 + 1 / (q : ℚ)) * ∏ x ∈ (P.erase q).filter (fun x => g x ∉ P.erase q), β x ≤
        β q * ∏ x ∈ (P.filter (fun q => g q ∉ P)).erase q, β x := by
      by_cases hpar : ∃ p ∈ P, g p = q
      · obtain ⟨p, hpP, hpq⟩ := hpar
        have hpne : p ≠ q := by
          intro h
          have := hlt p hpP (hpq ▸ hqP)
          omega
        have hset : (P.erase q).filter (fun x => g x ∉ P.erase q) =
            insert p ((P.filter (fun q => g q ∉ P)).erase q) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_insert, not_and]
          constructor
          · rintro ⟨⟨hxq, hxP⟩, hx⟩
            by_cases hgx : g x = q
            · left
              exact (hinj p hpP x hxP (hpq ▸ hqP) (hpq.trans hgx.symm)).symm
            · right
              exact ⟨hxq, hxP, fun h => hx hgx h⟩
          · rintro (rfl | ⟨hxq, hxP, hx⟩)
            · exact ⟨⟨hpne, hpP⟩, fun h => absurd hpq h⟩
            · exact ⟨⟨hxq, hxP⟩, fun _ h => hx h⟩
        have hnotin : p ∉ (P.filter (fun q => g q ∉ P)).erase q := by
          intro h
          exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).2 (hpq ▸ hqP)
        rw [hset, Finset.prod_insert hnotin, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ hrest0
        have := hstep p hpP (hpq ▸ hqP)
        rwa [hpq] at this
      · have hset : (P.erase q).filter (fun x => g x ∉ P.erase q) =
            (P.filter (fun q => g q ∉ P)).erase q := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_erase, not_and]
          constructor
          · rintro ⟨⟨hxq, hxP⟩, hx⟩
            exact ⟨hxq, hxP, fun h => hx (fun hgx => hpar ⟨x, hxP, hgx⟩) h⟩
          · rintro ⟨hxq, hxP, hx⟩
            exact ⟨⟨hxq, hxP⟩, fun _ h => hx h⟩
        rw [hset]
        exact mul_le_mul_of_nonneg_right (hβ q hqP) hrest0
    calc ∏ p ∈ P, (1 + 1 / (p : ℚ))
        = (1 + 1 / (q : ℚ)) * ∏ p ∈ P.erase q, (1 + 1 / (p : ℚ)) :=
          (Finset.mul_prod_erase P (fun p : ℕ => (1 + 1 / (p : ℚ))) hqP).symm
      _ ≤ (1 + 1 / (q : ℚ)) * ∏ x ∈ (P.erase q).filter (fun x => g x ∉ P.erase q), β x :=
          mul_le_mul_of_nonneg_left ih' hq0
      _ ≤ β q * ∏ x ∈ (P.filter (fun q => g q ∉ P)).erase q, β x := key
      _ = ∏ q ∈ P.filter (fun q => g q ∉ P), β q := Finset.mul_prod_erase _ β hqL

theorem tail_bound : ∀ (n : ℕ) (Q : Finset ℕ) (a : ℕ), Q.card = n → 4 ≤ a → (∀ q ∈ Q, a ≤ q) →
    (∀ q ∈ Q, ∀ q' ∈ Q, q < q' → 2 * q + 1 ≤ q') →
    ∏ q ∈ Q, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ ((a : ℚ) + 1) / ((a : ℚ) - 3) := by
  intro n
  induction n with
  | zero =>
    intro Q a hQ ha _ _
    have ha' : (4 : ℚ) ≤ a := by exact_mod_cast ha
    rw [Finset.card_eq_zero.mp hQ, Finset.prod_empty, le_div_iff₀ (by linarith)]
    linarith
  | succ n ih =>
    intro Q a hcard ha hge hdbl
    have hne : Q.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, hqQ, hqmin⟩ : ∃ q ∈ Q, ∀ p ∈ Q, q ≤ p :=
      ⟨Q.min' hne, Finset.min'_mem Q hne, fun p hp => Finset.min'_le Q p hp⟩
    have haq : a ≤ q := hge q hqQ
    have ih' := ih (Q.erase q) (2 * q + 1) (by rw [Finset.card_erase_of_mem hqQ, hcard]; rfl)
      (by omega)
      (fun x hx => hdbl q hqQ x (Finset.mem_of_mem_erase hx)
        (lt_of_le_of_ne (hqmin x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx).symm))
      (fun x hx y hy => hdbl x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy))
    have ha' : (4 : ℚ) ≤ a := by exact_mod_cast ha
    have haq' : (a : ℚ) ≤ q := by exact_mod_cast haq
    have hB0 : (0 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := div_nonneg (by linarith) (by linarith)
    rw [← Finset.mul_prod_erase Q _ hqQ]
    calc ((q : ℚ) + 1) / ((q : ℚ) - 1) * ∏ x ∈ Q.erase q, (((x : ℚ) + 1) / ((x : ℚ) - 1))
        ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) * ((((2 * q + 1 : ℕ) : ℚ) + 1) / (((2 * q + 1 : ℕ) : ℚ) - 3)) :=
          mul_le_mul_of_nonneg_left ih' hB0
      _ ≤ ((q : ℚ) + 1) / ((q : ℚ) - 3) := by
          push_cast
          rw [div_mul_div_comm, div_le_div_iff₀ (by nlinarith) (by linarith)]
          nlinarith
      _ ≤ ((a : ℚ) + 1) / ((a : ℚ) - 3) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith

theorem mersenne_small {q k : ℕ} (hq : q.Prime) (hk : q + 1 = 2 ^ k) (hlt : q < 8191) :
    q = 3 ∨ q = 7 ∨ q = 31 ∨ q = 127 := by
  have hk13 : k < 13 := by
    by_contra h
    have : 2 ^ 13 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp at hk <;> subst hk <;> first | omega | (norm_num at hq)

theorem two_mul_le {c p : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : c ∣ p + 1) : 2 * c ≤ p + 1 := by
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcop : Nat.Coprime 2 c := (Nat.coprime_primes Nat.prime_two hc).mpr (Ne.symm hc2)
  exact Nat.le_of_dvd (by omega) (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 hd)

-- new: the child function that ignores the exceptional primes (the set N).
theorem exists_child (N : Finset ℕ) : ∃ g : ℕ → ℕ, ∀ p : ℕ, g p ∣ p + 1 ∧
    (g p = 1 → ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ p + 1 → c ∈ N) ∧
    (g p ≠ 1 → (g p).Prime ∧ g p ≠ 2 ∧ g p ∉ N) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ p + 1 → g p ≤ c) := by
  have key : ∀ p : ℕ, ∃ x : ℕ, x ∣ p + 1 ∧
      (x = 1 → ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ p + 1 → c ∈ N) ∧
      (x ≠ 1 → x.Prime ∧ x ≠ 2 ∧ x ∉ N) ∧
      (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ p + 1 → x ≤ c) := by
    intro p
    by_cases h : ∃ c : ℕ, c.Prime ∧ c ≠ 2 ∧ c ∉ N ∧ c ∣ p + 1
    · classical
      refine ⟨Nat.find h, (Nat.find_spec h).2.2.2, fun h1 => ?_,
        fun _ => ⟨(Nat.find_spec h).1, (Nat.find_spec h).2.1, (Nat.find_spec h).2.2.1⟩,
        fun c hc hc2 hcN hcd => Nat.find_min' h ⟨hc, hc2, hcN, hcd⟩⟩
      exact absurd (h1 ▸ (Nat.find_spec h).1) Nat.not_prime_one
    · refine ⟨1, one_dvd _, fun _ c hc hc2 hcd => ?_, fun h1 => absurd rfl h1,
        fun c hc hc2 hcN hcd => absurd ⟨c, hc, hc2, hcN, hcd⟩ h⟩
      by_contra hcN
      exact h ⟨c, hc, hc2, hcN, hcd⟩
  exact ⟨fun p => (key p).choose, fun p => (key p).choose_spec⟩

-- new: product of x / (x - c) over x = v * z^j with distinct exponents j ≥ i.
theorem geom_bound {z c v : ℕ} (hz : c + 1 ≤ z) : ∀ (n : ℕ) (T : Finset ℕ) (i : ℕ), T.card = n →
    c + 2 ≤ v * z ^ i → (∀ j ∈ T, i ≤ j) →
    ∏ j ∈ T, (((v : ℚ) * (z : ℚ) ^ j) / ((v : ℚ) * (z : ℚ) ^ j - (c : ℚ))) ≤
      ((v : ℚ) * (z : ℚ) ^ i) / ((v : ℚ) * (z : ℚ) ^ i - ((c : ℚ) + 1)) := by
  have hc0 : (0 : ℚ) ≤ c := Nat.cast_nonneg c
  have hzq : (c : ℚ) + 1 ≤ z := by exact_mod_cast hz
  have hz1 : (1 : ℚ) ≤ z := by linarith
  have hv0 : (0 : ℚ) ≤ v := Nat.cast_nonneg v
  intro n
  induction n with
  | zero =>
    intro T i hT hi _
    have hY : (c : ℚ) + 2 ≤ (v : ℚ) * (z : ℚ) ^ i := by exact_mod_cast hi
    rw [Finset.card_eq_zero.mp hT, Finset.prod_empty, le_div_iff₀ (by linarith)]
    linarith
  | succ n ih =>
    intro T i hcard hi hge
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j0, hj0T, hj0min⟩ : ∃ q ∈ T, ∀ p ∈ T, q ≤ p :=
      ⟨T.min' hne, Finset.min'_mem T hne, fun p hp => Finset.min'_le T p hp⟩
    have hij0 : i ≤ j0 := hge j0 hj0T
    have hzpos : 0 < z := by omega
    have hi' : c + 2 ≤ v * z ^ (j0 + 1) :=
      hi.trans (Nat.mul_le_mul_left v (Nat.pow_le_pow_right hzpos (by omega)))
    have ih' := ih (T.erase j0) (j0 + 1) (by rw [Finset.card_erase_of_mem hj0T, hcard]; rfl)
      hi'
      (fun x hx => by
        have h1 := hj0min x (Finset.mem_of_mem_erase hx)
        have h2 := Finset.ne_of_mem_erase hx
        omega)
    have hY : (c : ℚ) + 2 ≤ (v : ℚ) * (z : ℚ) ^ i := by exact_mod_cast hi
    have hYX : (v : ℚ) * (z : ℚ) ^ i ≤ (v : ℚ) * (z : ℚ) ^ j0 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz1 hij0) hv0
    have e : (v : ℚ) * (z : ℚ) ^ (j0 + 1) = (v : ℚ) * (z : ℚ) ^ j0 * z := by ring
    rw [← Finset.mul_prod_erase T _ hj0T]
    rw [e] at ih'
    generalize (v : ℚ) * (z : ℚ) ^ j0 = X at ih' hYX ⊢
    generalize (v : ℚ) * (z : ℚ) ^ i = Y at hY hYX ⊢
    have hX0 : (0 : ℚ) ≤ X := by linarith
    have hB0 : (0 : ℚ) ≤ X / (X - c) := div_nonneg hX0 (by linarith)
    have hXz : X ≤ X * z := by nlinarith
    calc X / (X - c) * ∏ x ∈ T.erase j0, ((v : ℚ) * (z : ℚ) ^ x / ((v : ℚ) * (z : ℚ) ^ x - c))
        ≤ X / (X - c) * (X * z / (X * z - (c + 1))) := mul_le_mul_of_nonneg_left ih' hB0
      _ ≤ X / (X - (c + 1)) := by
          rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (by linarith)]
          nlinarith [mul_nonneg (mul_nonneg hX0 hX0) (by linarith : (0 : ℚ) ≤ (z : ℚ) - c - 1),
            mul_nonneg hX0 (mul_nonneg hc0 (by linarith : (0 : ℚ) ≤ (c : ℚ) + 1))]
      _ ≤ Y / (Y - (c + 1)) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith [mul_le_mul_of_nonneg_left hYX (by linarith : (0 : ℚ) ≤ (c : ℚ) + 1)]

-- new: for a fixed odd part u, the numbers 2^k * u - 1 at least double.
theorem fiber_bound {u : ℕ} (hu : 3 ≤ u) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, ∃ k, 1 ≤ k ∧ q + 1 = 2 ^ k * u) :
    ∏ q ∈ Q, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ (u : ℚ) / ((u : ℚ) - 2) := by
  obtain ⟨a, ha⟩ : ∃ a, a + 1 = 2 * u := ⟨2 * u - 1, by omega⟩
  have htb := tail_bound Q.card Q a rfl (by omega)
    (fun q hq => by
      obtain ⟨k, hk, he⟩ := hQ q hq
      have h2k : 2 ≤ 2 ^ k := by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hk
        simpa using this
      have : 2 * u ≤ 2 ^ k * u := Nat.mul_le_mul_right _ h2k
      omega)
    (fun q hq q' hq' hlt => by
      obtain ⟨k, hk, he⟩ := hQ q hq
      obtain ⟨k', hk', he'⟩ := hQ q' hq'
      have hkk : k < k' := by
        by_contra hcon
        have : 2 ^ k' ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2 ^ k' * u ≤ 2 ^ k * u := Nat.mul_le_mul_right _ this
        omega
      have : 2 ^ (k + 1) ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ (k + 1) * u ≤ 2 ^ k' * u := Nat.mul_le_mul_right _ this
      rw [pow_succ] at this
      linarith)
  refine htb.trans ?_
  have haq : (a : ℚ) + 1 = 2 * (u : ℚ) := by exact_mod_cast ha
  have huq : (3 : ℚ) ≤ (u : ℚ) := by exact_mod_cast hu
  have e : (a : ℚ) = 2 * (u : ℚ) - 1 := by linarith
  rw [e, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

-- new: product of u / (u - c) over distinct numbers u > 1 all of whose primes lie in N.
theorem smooth_bound : ∀ (N : Finset ℕ) (c : ℕ), (∀ z ∈ N, z.Prime ∧ c + N.card + 1 ≤ z) →
    ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
    ∏ u ∈ U, ((u : ℚ) / ((u : ℚ) - (c : ℚ))) ≤
      ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - (c : ℚ) - (N.card : ℚ))) := by
  intro N
  induction N using Finset.induction_on with
  | empty =>
    intro c _ U hU
    have hUe : U = ∅ := by
      by_contra hne
      obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨h0, h1, hr⟩ := hU u hu
      exact absurd (hr _ (Nat.minFac_prime h1) (Nat.minFac_dvd u)) (Finset.notMem_empty _)
    rw [hUe]
    simp
  | insert z N0 hzN0 ih =>
    intro c hN U hU
    have hcard : (insert z N0).card = N0.card + 1 := Finset.card_insert_of_notMem hzN0
    obtain ⟨hzp, hzge⟩ := hN z (Finset.mem_insert_self z N0)
    rw [hcard] at hzge
    have hN0 : ∀ z' ∈ N0, z'.Prime ∧ (c + 1) + N0.card + 1 ≤ z' := fun z' h' => by
      obtain ⟨h1, h2⟩ := hN z' (Finset.mem_insert_of_mem h')
      rw [hcard] at h2
      exact ⟨h1, by omega⟩
    have hφ : ∀ u ∈ U, u / z ^ u.factorization z ≠ 0 ∧
        ∀ r : ℕ, r.Prime → r ∣ u / z ^ u.factorization z → r ∈ N0 := fun u hu => by
      obtain ⟨h0, h1, hr⟩ := hU u hu
      refine ⟨(Nat.ordCompl_pos z h0).ne', fun r hrp hrd => ?_⟩
      rcases Finset.mem_insert.mp (hr r hrp (hrd.trans (Nat.ordCompl_dvd u z))) with rfl | h
      · exact absurd hrd (Nat.not_dvd_ordCompl hrp h0)
      · exact h
    have hmul : ∀ u : ℕ, z ^ u.factorization z * (u / z ^ u.factorization z) = u := fun u =>
      Nat.ordProj_mul_ordCompl_eq_self u z
    have hvge : ∀ v : ℕ, v ≠ 0 → v ≠ 1 → (∀ r : ℕ, r.Prime → r ∣ v → r ∈ N0) → c + 2 ≤ v :=
      fun v hv0 hv1 hvr => by
        have hmem := hvr _ (Nat.minFac_prime hv1) (Nat.minFac_dvd v)
        have h1 := (hN0 _ hmem).2
        have h2 := Nat.minFac_le (Nat.pos_of_ne_zero hv0)
        omega
    have hz1 : c + 1 ≤ z := by omega
    obtain ⟨V, hV⟩ : ∃ V : Finset ℕ, V = U.image (fun u => u / z ^ u.factorization z) := ⟨_, rfl⟩
    have hVmem : ∀ v ∈ V, ∃ u0 ∈ U, u0 / z ^ u0.factorization z = v := fun v hv => by
      rw [hV] at hv
      exact Finset.mem_image.mp hv
    have hmaps : ∀ u ∈ U, u / z ^ u.factorization z ∈ V := fun u hu => by
      rw [hV]
      exact Finset.mem_image_of_mem _ hu
    have hfib : ∀ v ∈ V,
        ∏ u ∈ U.filter (fun u => u / z ^ u.factorization z = v),
          ((u : ℚ) / ((u : ℚ) - (c : ℚ))) ≤
        if v = 1 then (z : ℚ) / ((z : ℚ) - ((c : ℚ) + 1))
        else (v : ℚ) / ((v : ℚ) - ((c : ℚ) + 1)) := by
      intro v hv
      obtain ⟨u0, hu0, hv0⟩ := hVmem v hv
      have hv0' : v ≠ 0 := hv0 ▸ (hφ u0 hu0).1
      have hvr : ∀ r : ℕ, r.Prime → r ∣ v → r ∈ N0 := hv0 ▸ (hφ u0 hu0).2
      have hinj : ∀ u1 ∈ U.filter (fun u => u / z ^ u.factorization z = v),
          ∀ u2 ∈ U.filter (fun u => u / z ^ u.factorization z = v),
          u1.factorization z = u2.factorization z → u1 = u2 := fun u1 h1 u2 h2 he => by
        have e1 := hmul u1
        have e2 := hmul u2
        rw [(Finset.mem_filter.mp h1).2] at e1
        rw [(Finset.mem_filter.mp h2).2, ← he] at e2
        exact e1.symm.trans e2
      have hrew : ∏ u ∈ U.filter (fun u => u / z ^ u.factorization z = v),
            ((u : ℚ) / ((u : ℚ) - (c : ℚ))) =
          ∏ j ∈ (U.filter (fun u => u / z ^ u.factorization z = v)).image
              (fun u => u.factorization z),
            (((v : ℚ) * (z : ℚ) ^ j) / ((v : ℚ) * (z : ℚ) ^ j - (c : ℚ))) := by
        rw [Finset.prod_image hinj]
        refine Finset.prod_congr rfl fun u hu => ?_
        have e1 := hmul u
        rw [(Finset.mem_filter.mp hu).2] at e1
        have e2 : (u : ℚ) = (v : ℚ) * (z : ℚ) ^ u.factorization z := by
          have := congrArg (Nat.cast : ℕ → ℚ) e1
          push_cast at this
          rw [← this]; ring
        rw [e2]
      rw [hrew]
      by_cases hv1 : v = 1
      · rw [if_pos hv1]
        have h := geom_bound (v := v) hz1 _
          ((U.filter (fun u => u / z ^ u.factorization z = v)).image (fun u => u.factorization z))
          1 rfl (by rw [hv1, one_mul, pow_one]; omega)
          (fun j hj => by
            obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
            by_contra hlt
            have hj0 : u.factorization z = 0 := by omega
            have e1 := hmul u
            rw [(Finset.mem_filter.mp hu).2, hj0, pow_zero, one_mul, hv1] at e1
            exact (hU u (Finset.mem_filter.mp hu).1).2.1 e1.symm)
        rw [pow_one] at h
        rw [hv1, Nat.cast_one, one_mul] at h
        simpa [hv1] using h
      · rw [if_neg hv1]
        have h := geom_bound (v := v) hz1 _
          ((U.filter (fun u => u / z ^ u.factorization z = v)).image (fun u => u.factorization z))
          0 rfl (by rw [pow_zero, mul_one]; exact hvge v hv0' hv1 hvr) (fun j _ => Nat.zero_le j)
        rw [pow_zero, mul_one] at h
        exact h
    rw [← Finset.prod_fiberwise_of_maps_to (g := fun u => u / z ^ u.factorization z) (t := V) hmaps]
    have hcq : (0 : ℚ) ≤ c := Nat.cast_nonneg c
    have hsq : (0 : ℚ) ≤ (N0.card : ℚ) := Nat.cast_nonneg _
    have hzq : (c : ℚ) + (N0.card : ℚ) + 2 ≤ z := by
      exact_mod_cast (by omega : c + N0.card + 2 ≤ z)
    have hA1 : (1 : ℚ) ≤ (z : ℚ) / ((z : ℚ) - ((c : ℚ) + 1)) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have hV' : ∀ v ∈ V.erase 1,
        v ≠ 0 ∧ v ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ v → r ∈ N0 := fun v hv => by
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hv
      obtain ⟨u0, hu0, rfl⟩ := hVmem v hmem
      exact ⟨(hφ u0 hu0).1, hne, (hφ u0 hu0).2⟩
    have hIH := ih (c + 1) hN0 _ hV'
    push_cast at hIH
    have hT0 : ∀ v : ℕ, v ∈ V.erase 1 → (0 : ℚ) ≤ (v : ℚ) / ((v : ℚ) - ((c : ℚ) + 1)) :=
      fun v hv => by
        obtain ⟨h0, h1, hr⟩ := hV' v hv
        have hge : (c : ℚ) + 2 ≤ v := by exact_mod_cast hvge v h0 h1 hr
        exact div_nonneg (by linarith) (by linarith)
    have hstep1 : ∏ v ∈ V,
        (if v = 1 then (z : ℚ) / ((z : ℚ) - ((c : ℚ) + 1))
          else (v : ℚ) / ((v : ℚ) - ((c : ℚ) + 1))) ≤
        (z : ℚ) / ((z : ℚ) - ((c : ℚ) + 1)) *
          ∏ v ∈ V.erase 1, ((v : ℚ) / ((v : ℚ) - ((c : ℚ) + 1))) := by
      by_cases h1 : 1 ∈ V
      · rw [← Finset.mul_prod_erase _ _ h1, if_pos rfl]
        refine mul_le_mul_of_nonneg_left (le_of_eq (Finset.prod_congr rfl fun v hv => ?_))
          (by linarith)
        exact if_neg (Finset.ne_of_mem_erase hv)
      · rw [Finset.erase_eq_of_notMem h1]
        have e : ∏ v ∈ V,
            (if v = 1 then (z : ℚ) / ((z : ℚ) - ((c : ℚ) + 1))
              else (v : ℚ) / ((v : ℚ) - ((c : ℚ) + 1))) =
            ∏ v ∈ V, ((v : ℚ) / ((v : ℚ) - ((c : ℚ) + 1))) :=
          Finset.prod_congr rfl fun v hv => if_neg (fun h : v = 1 => h1 (h ▸ hv))
        rw [e]
        have hnn : (0 : ℚ) ≤ ∏ v ∈ V, ((v : ℚ) / ((v : ℚ) - ((c : ℚ) + 1))) :=
          Finset.prod_nonneg fun v hv => hT0 v (by rw [Finset.erase_eq_of_notMem h1]; exact hv)
        calc ∏ v ∈ V, ((v : ℚ) / ((v : ℚ) - ((c : ℚ) + 1)))
            = 1 * ∏ v ∈ V, ((v : ℚ) / ((v : ℚ) - ((c : ℚ) + 1))) := (one_mul _).symm
          _ ≤ (z : ℚ) / ((z : ℚ) - ((c : ℚ) + 1)) *
              ∏ v ∈ V, ((v : ℚ) / ((v : ℚ) - ((c : ℚ) + 1))) :=
            mul_le_mul_of_nonneg_right hA1 hnn
    have hzA : (z : ℚ) / ((z : ℚ) - ((c : ℚ) + 1)) ≤
        (z : ℚ) / ((z : ℚ) - (c : ℚ) - ((N0.card : ℚ) + 1)) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have hIH' : ∏ v ∈ V.erase 1, ((v : ℚ) / ((v : ℚ) - ((c : ℚ) + 1))) ≤
        ∏ z' ∈ N0, ((z' : ℚ) / ((z' : ℚ) - (c : ℚ) - ((N0.card : ℚ) + 1))) := by
      refine hIH.trans (le_of_eq (Finset.prod_congr rfl fun z' _ => ?_))
      congr 1
      ring
    rw [Finset.prod_insert hzN0, hcard]
    push_cast
    refine (Finset.prod_le_prod (fun v _ => Finset.prod_nonneg fun u hu => ?_) hfib).trans
      (hstep1.trans (mul_le_mul hzA hIH' (Finset.prod_nonneg hT0) (by linarith [hA1.trans hzA])))
    obtain ⟨h0, h1, hr⟩ := hU u (Finset.mem_filter.mp hu).1
    have hmem := hr _ (Nat.minFac_prime h1) (Nat.minFac_dvd u)
    have h2 := (hN _ hmem).2
    have h3 := Nat.minFac_le (Nat.pos_of_ne_zero h0)
    have hge : (c : ℚ) + 1 ≤ u := by exact_mod_cast (by omega : c + 1 ≤ u)
    exact div_nonneg (by linarith) (by linarith)

-- new: the N-leaves (primes q with q + 1 = 2^k * u, u > 1 a product of primes of N) have bounded
-- total weight, independently of how many there are and of the exponents.
theorem nleaf_bound {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ N.card + 3 ≤ z) (L : Finset ℕ)
    (hL : ∀ q ∈ L, 2 ∣ q + 1 ∧ (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1 ∧
      ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) :
    ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) := by
  have hu : ∀ q ∈ L, (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 0 ∧
      ¬ 2 ∣ (q + 1) / 2 ^ (q + 1).factorization 2 ∧ 1 ≤ (q + 1).factorization 2 ∧
      q + 1 = 2 ^ (q + 1).factorization 2 * ((q + 1) / 2 ^ (q + 1).factorization 2) :=
    fun q hq => by
      obtain ⟨h2, _, _⟩ := hL q hq
      have hN0 : q + 1 ≠ 0 := by omega
      exact ⟨(Nat.ordCompl_pos 2 hN0).ne', Nat.not_dvd_ordCompl Nat.prime_two hN0,
        Nat.prime_two.factorization_pos_of_dvd hN0 h2,
        (Nat.ordProj_mul_ordCompl_eq_self (q + 1) 2).symm⟩
  rw [← Finset.prod_fiberwise_of_maps_to (g := fun q => (q + 1) / 2 ^ (q + 1).factorization 2)
    (t := L.image (fun q => (q + 1) / 2 ^ (q + 1).factorization 2))
    (fun x hx => Finset.mem_image_of_mem _ hx)]
  have h3 : ∀ u ∈ L.image (fun q => (q + 1) / 2 ^ (q + 1).factorization 2), 3 ≤ u ∧
      (u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) := fun u hu' => by
    obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp hu'
    obtain ⟨h0, hodd, hk, he⟩ := hu q hq
    obtain ⟨h2, hne1, hc⟩ := hL q hq
    have hdvd : u ∣ q + 1 := hqu ▸ Nat.ordCompl_dvd (q + 1) 2
    rw [hqu] at h0 hodd hne1
    refine ⟨by omega, h0, hne1, fun r hr hrd => ?_⟩
    exact hc r hr (fun h2' => hodd (h2' ▸ hrd)) (hrd.trans hdvd)
  refine (Finset.prod_le_prod (g := fun u : ℕ => (u : ℚ) / ((u : ℚ) - 2))
    (fun u _ => Finset.prod_nonneg fun x hx => ?_) (fun u hu' => ?_)).trans ?_
  · obtain ⟨h2, _, _⟩ := hL x (Finset.mem_filter.mp hx).1
    have hx1 : 1 ≤ x := by omega
    have hx1q : (1 : ℚ) ≤ x := by exact_mod_cast hx1
    exact div_nonneg (by linarith) (by linarith)
  · exact fiber_bound (h3 u hu').1 _ (fun q hq => by
      obtain ⟨hqL, hqu⟩ := Finset.mem_filter.mp hq
      obtain ⟨h0, hodd, hk, he⟩ := hu q hqL
      exact ⟨_, hk, by rw [← hqu]; exact he⟩)
  · have h := smooth_bound N 2 (fun z hz => ⟨(hN z hz).1, by have := (hN z hz).2; omega⟩)
      (L.image (fun q => (q + 1) / 2 ^ (q + 1).factorization 2)) (fun u hu' => (h3 u hu').2)
    push_cast at h
    exact h
-- The Mersenne leaves: weights at 3, 7, 31, 127 and the tail from 8191 on.
theorem mersenne_bound (β : ℕ → ℚ) (L : Finset ℕ) (hLp : ∀ q ∈ L, q.Prime)
    (hLm : ∀ q ∈ L, ∃ k, q + 1 = 2 ^ k)
    (hLβ : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1))
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127) :
    ∏ q ∈ L, β q ≤ (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not L (fun q => q < 8191) β
  have hsmall : ∏ q ∈ L.filter (fun q => q < 8191), β q ≤ β 3 * β 7 * β 31 * β 127 := by
    have hsub : L.filter (fun q => q < 8191) ⊆ ({3, 7, 31, 127} : Finset ℕ) := by
      intro q hq
      obtain ⟨hqL, hlt⟩ := Finset.mem_filter.mp hq
      obtain ⟨k, hk⟩ := hLm q hqL
      have := mersenne_small (hLp q hqL) hk hlt
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have h := Finset.prod_le_prod_of_subset_of_one_le (f := β) hsub
      (fun i hi => (hLβ i (Finset.mem_filter.mp hi).1).1.le) (fun i hi _ => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact h1.1
      · exact h1.2.1
      · exact h1.2.2.1
      · exact h1.2.2.2)
    have e : ∏ q ∈ ({3, 7, 31, 127} : Finset ℕ), β q = β 3 * β 7 * β 31 * β 127 := by
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
      ring
    rwa [e] at h
  have htail : ∏ q ∈ L.filter (fun q => ¬ q < 8191), β q ≤ 2048 / 2047 := by
    have hmemT : ∀ q ∈ L.filter (fun q => ¬ q < 8191), q ∈ L ∧ 8191 ≤ q := fun q hq => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
      exact ⟨h1, by omega⟩
    have hle : ∏ q ∈ L.filter (fun q => ¬ q < 8191), β q ≤
        ∏ q ∈ L.filter (fun q => ¬ q < 8191), (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
      Finset.prod_le_prod (fun q hq => (hLβ q (hmemT q hq).1).1.le)
        (fun q hq => (hLβ q (hmemT q hq).1).2)
    have htb := tail_bound _ _ 8191 rfl (by norm_num) (fun q hq => (hmemT q hq).2)
      (fun q hq q' hq' hlt => by
        obtain ⟨k, hk⟩ := hLm q (hmemT q hq).1
        obtain ⟨k', hk'⟩ := hLm q' (hmemT q' hq').1
        have hkk : k < k' := by
          by_contra hcon
          have : 2 ^ k' ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have : 2 ^ (k + 1) ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at this
        omega)
    refine hle.trans (htb.trans ?_)
    norm_num
  rw [← hsplit]
  refine mul_le_mul hsmall htail ?_ ?_
  · exact Finset.prod_nonneg fun q hq => (hLβ q (Finset.mem_filter.mp hq).1).1.le
  · obtain ⟨a, b, c, d⟩ := h1
    have h3 : (0 : ℚ) ≤ β 3 := by linarith
    have h7 : (0 : ℚ) ≤ β 7 := by linarith
    have h31 : (0 : ℚ) ≤ β 31 := by linarith
    have h127 : (0 : ℚ) ≤ β 127 := by linarith
    positivity

-- Section 2. Structure of the balance equation (E) with a kernel K supported on N.

theorem K_pos {K : ℕ} {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) : 0 < K := by
  rcases Nat.eq_zero_or_pos K with h | h
  · have := (hN 2 (hK 2 Nat.prime_two (h ▸ dvd_zero 2))).2.1
    omega
  · exact h

theorem small_notMem {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) {c : ℕ}
    (hc : c < 128) : c ∉ N := fun h => by
  have := (hN c h).2.1
  omega

theorem S_mem {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hcz : c ∉ N)
    (hd : c ∣ (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1)) : c ∈ P := by
  rw [E] at hd
  rcases (Nat.Prime.dvd_mul hc).mp hd with h | h
  · rcases (Nat.Prime.dvd_mul hc).mp h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_two).mp (hc.dvd_of_dvd_pow h)) hc2
    · exact absurd (hK c hc h) hcz
  · obtain ⟨p, hp, hcp⟩ := (Prime.dvd_finsetProd_iff hc.prime _).mp h
    rwa [(Nat.prime_dvd_prime_iff_eq hc (hP p hp).1).mp hcp]

theorem S_sq {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hcz : c ∉ N) :
    ¬ c * c ∣ (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) := by
  intro hd
  have hcP : c ∈ P := S_mem hP hK E hc hc2 hcz ((dvd_mul_right c c).trans hd)
  rw [E, ← Finset.mul_prod_erase P (fun p => p) hcP, mul_left_comm] at hd
  have h1 : c ∣ 2 ^ (m + 1) * K * ∏ p ∈ P.erase c, p := Nat.dvd_of_mul_dvd_mul_left hc.pos hd
  rcases (Nat.Prime.dvd_mul hc).mp h1 with h | h
  · rcases (Nat.Prime.dvd_mul hc).mp h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_two).mp (hc.dvd_of_dvd_pow h)) hc2
    · exact absurd (hK c hc h) hcz
  · obtain ⟨p, hp, hcp⟩ := (Prime.dvd_finsetProd_iff hc.prime _).mp h
    have := (Nat.prime_dvd_prime_iff_eq hc (hP p (Finset.mem_of_mem_erase hp)).1).mp hcp
    exact (Finset.ne_of_mem_erase hp) this.symm

-- Every odd prime c outside N has exactly one source on the left of (E).
theorem facts {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) :
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → ∀ p ∈ P, c ∣ p + 1 → c ∈ P) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ 2 ^ m + 1 → c ∈ P) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → ∀ p ∈ P, ∀ p' ∈ P, c ∣ p + 1 → c ∣ p' + 1 → p = p') ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ 2 ^ m + 1 → ∀ p ∈ P, ¬ c ∣ p + 1) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → ¬ c * c ∣ 2 ^ m + 1) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → ∀ p ∈ P, ¬ c * c ∣ p + 1) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ K' → c ∈ P) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ K' → ∀ p ∈ P, ¬ c ∣ p + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc hc2 hcz p hp hd
    exact S_mem hP hK E hc hc2 hcz
      ((hd.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp)).mul_left _)
  · intro c hc hc2 hcz hd
    exact S_mem hP hK E hc hc2 hcz ((hd.mul_right _).mul_right _)
  · intro c hc hc2 hcz p hp p' hp' hd hd'
    by_contra hne
    apply S_sq hP hK E hc hc2 hcz
    have hsub : ({p, p'} : Finset ℕ) ⊆ P := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp
      · rw [Finset.mem_singleton.mp hx]; exact hp'
    have h1 : (p + 1) * (p' + 1) ∣ ∏ x ∈ P, (x + 1) := by
      have := Finset.prod_dvd_prod_of_subset _ _ (fun x => x + 1) hsub
      rwa [Finset.prod_pair hne] at this
    exact ((mul_dvd_mul hd hd').trans h1).mul_left _
  · intro c hc hc2 hcz hd p hp hd'
    apply S_sq hP hK E hc hc2 hcz
    have h := (mul_dvd_mul hd (hd'.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp))).mul_left K'
    have e : K' * ((2 ^ m + 1) * ∏ p ∈ P, (p + 1)) = (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) := by ring
    rwa [e] at h
  · intro c hc hc2 hcz hd
    exact S_sq hP hK E hc hc2 hcz ((hd.mul_right _).mul_right _)
  · intro c hc hc2 hcz p hp hd
    exact S_sq hP hK E hc hc2 hcz
      ((hd.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp)).mul_left _)
  · intro c hc hc2 hcz hd
    exact S_mem hP hK E hc hc2 hcz ((hd.mul_left _).mul_right _)
  · intro c hc hc2 hcz hd p hp hd'
    apply S_sq hP hK E hc hc2 hcz
    have h := (mul_dvd_mul hd (hd'.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp))).mul_left
      (2 ^ m + 1)
    rwa [← mul_assoc] at h

theorem S_abund {m K K' : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK0 : 0 < K) (hKK : K ≤ K')
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    {A : Finset ℕ} (hA : A ⊆ P) : ∏ p ∈ A, (p + 1) < 2 * ∏ p ∈ A, p := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  rw [← Finset.prod_sdiff hA, ← Finset.prod_sdiff hA (f := fun p => p)] at E
  have hle : ∏ p ∈ P \ A, p ≤ ∏ p ∈ P \ A, (p + 1) :=
    Finset.prod_le_prod' fun p _ => Nat.le_succ p
  have hYD : 0 < ∏ p ∈ P \ A, p :=
    Finset.prod_pos fun p hp => hpos p (Finset.mem_sdiff.mp hp).1
  by_contra hcon
  rw [not_lt] at hcon
  have hXA : 0 < ∏ p ∈ A, (p + 1) := Finset.prod_pos fun p _ => Nat.succ_pos p
  have hK'0 : 0 < K' := lt_of_lt_of_le hK0 hKK
  have h1 : 2 ^ (m + 1) * K * ((∏ p ∈ P \ A, p) * ∏ p ∈ A, p) ≤
      2 ^ m * K' * ((∏ p ∈ P \ A, (p + 1)) * ∏ p ∈ A, (p + 1)) := by
    rw [pow_succ]
    calc 2 ^ m * 2 * K * ((∏ p ∈ P \ A, p) * ∏ p ∈ A, p)
        = 2 ^ m * K * ((∏ p ∈ P \ A, p) * (2 * ∏ p ∈ A, p)) := by ring
      _ ≤ 2 ^ m * K' * ((∏ p ∈ P \ A, (p + 1)) * ∏ p ∈ A, (p + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hKK) (Nat.mul_le_mul hle hcon)
  have h2 : 2 ^ m * K' * ((∏ p ∈ P \ A, (p + 1)) * ∏ p ∈ A, (p + 1)) <
      (2 ^ m + 1) * K' * ((∏ p ∈ P \ A, (p + 1)) * ∏ p ∈ A, (p + 1)) :=
    Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hK'0)
      (Nat.mul_pos (lt_of_lt_of_le hYD hle) hXA)
  omega

-- Section 3. The master inequality.

theorem master {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 10 ≤ m)
    (β : ℕ → ℚ)
    (hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
        (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → c ≤ c') →
        β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c)
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127)
    (hfin : 1025 / 1024 * (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) * (2101 / 2097) < 2) :
    False := by
  obtain ⟨S1, -, S2, -, -, -, -, -⟩ := facts hP hK E
  obtain ⟨g, hg⟩ := exists_child N
  have hK0 : 0 < K := K_pos hN hK
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  have hβpos : ∀ p ∈ P, 0 < β p := fun p hp => by
    have h0 : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
    linarith [(hB p hp).1]
  have hg1 : ∀ p ∈ P, g p ∈ P → g p ≠ 1 := fun p _ h h1 => by
    have := (hP _ h).1
    rw [h1] at this
    exact Nat.not_prime_one this
  have hgP : ∀ p ∈ P, g p ≠ 1 → g p ∈ P := fun p hp h =>
    S1 _ ((hg p).2.2.1 h).1 ((hg p).2.2.1 h).2.1 ((hg p).2.2.1 h).2.2 p hp (hg p).1
  have hpath := path_bound g β P.card P rfl hpos
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      have := two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1
      have := hc.1.two_le
      omega)
    (fun p hp p' hp' h he => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      exact S2 _ hc.1 hc.2.1 hc.2.2 p hp p' hp' (hg p).1 (he ▸ (hg p').1))
    (fun p hp => (hB p hp).1)
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      by_cases hsp : β (g p) = (((g p : ℕ) : ℚ) + 1) / (((g p : ℕ) : ℚ) - 1)
      · rw [hsp]
        have h0 : (0 : ℚ) ≤ 1 + 1 / ((g p : ℕ) : ℚ) := by positivity
        exact (mul_le_mul_of_nonneg_left (hB p hp).2 h0).trans
          (B_step hc.1.two_le (two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1))
      · exact h4 p hp (g p) h (hg p).1 (hg p).2.2.2 hsp)
  -- a path starts at a prime q such that every odd prime factor of q + 1 lies in N
  have hleaf : ∀ q ∈ P.filter (fun q => g q ∉ P),
      ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N := fun q hq => by
    obtain ⟨hqP, hgq⟩ := Finset.mem_filter.mp hq
    by_cases h : g q = 1
    · exact (hg q).2.1 h
    · exact absurd (hgP q hqP h) hgq
  have hLP : ∀ q ∈ P.filter (fun q => g q ∉ P), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hsplit := Finset.prod_filter_mul_prod_filter_not (P.filter (fun q => g q ∉ P))
    (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1) β
  have hs0 : (0 : ℚ) ≤ (N.card : ℚ) := Nat.cast_nonneg _
  have hzleaves : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
        (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1), β q ≤
      ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) := by
    refine (Finset.prod_le_prod
      (fun q hq => (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le)
      (fun q hq => (hB q (hLP q (Finset.mem_filter.mp hq).1)).2)).trans ?_
    refine nleaf_bound (fun z hz => ⟨(hN z hz).1, (hN z hz).2.2⟩) _ (fun q hq => ?_)
    obtain ⟨hqL, hne⟩ := Finset.mem_filter.mp hq
    have hqP := hP q (hLP q hqL)
    refine ⟨?_, hne, hleaf q hqL⟩
    rcases hqP.1.eq_two_or_odd with h | h
    · exact absurd h hqP.2
    · omega
  have hmleaves : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
        (fun q => ¬ (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    refine mersenne_bound β _ (fun q hq => (hP q (hLP q (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => ?_)
      (fun q hq => ⟨hβpos q (hLP q (Finset.mem_filter.mp hq).1),
        (hB q (hLP q (Finset.mem_filter.mp hq).1)).2⟩) h1
    obtain ⟨hqL, hzd⟩ := Finset.mem_filter.mp hq
    have h1' : (q + 1) / 2 ^ (q + 1).factorization 2 = 1 := not_not.mp hzd
    have hmul := Nat.ordProj_mul_ordCompl_eq_self (q + 1) 2
    rw [h1', mul_one] at hmul
    exact ⟨(q + 1).factorization 2, hmul.symm⟩
  have hM0 : (0 : ℚ) ≤ (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    obtain ⟨a, b, c, d⟩ := h1
    have h3 : (0 : ℚ) ≤ β 3 := by linarith
    have h7 : (0 : ℚ) ≤ β 7 := by linarith
    have h31 : (0 : ℚ) ≤ β 31 := by linarith
    have h127 : (0 : ℚ) ≤ β 127 := by linarith
    positivity
  have hΛ0 : (0 : ℚ) ≤ ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) :=
    Finset.prod_nonneg fun z hz => by
      have h3 : (N.card : ℚ) + 3 ≤ z := by exact_mod_cast (hN z hz).2.2
      exact div_nonneg (by linarith) (by linarith)
  have hprodL : ∏ q ∈ P.filter (fun q => g q ∉ P), β q ≤
      (∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ)))) *
        ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047)) := by
    rw [← hsplit]
    refine mul_le_mul hzleaves hmleaves ?_ hΛ0
    exact Finset.prod_nonneg fun q hq =>
      (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le
  -- the equation over ℚ
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK0
  have hEq : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
    have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) :=
      Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
    have hcast : ((2 : ℚ) ^ m + 1) * K' * ∏ p ∈ P, ((p : ℚ) + 1) =
        2 ^ (m + 1) * K * ∏ p ∈ P, (p : ℚ) := by
      have h := congrArg (Nat.cast : ℕ → ℚ) E
      push_cast at h
      exact h
    have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
      field_simp
    have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
    rw [e]
    field_simp
    rw [pow_succ] at hcast
    linarith
  have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 1025 / 1024 := by
    have h2 : (2 : ℚ) ^ 10 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 10 := one_div_le_one_div_of_le (by positivity) h2
    norm_num at this ⊢
    linarith
  have hKr0 : (0 : ℚ) ≤ (K' : ℚ) / K := div_nonneg (Nat.cast_nonneg _) hKq.le
  have hA : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) ≤ 1025 / 1024 * ((K' : ℚ) / K) :=
    mul_le_mul_of_nonneg_right hT hKr0
  have hC := mul_le_mul hA (hpath.trans hprodL)
    (Finset.prod_nonneg fun p _ => by positivity) (mul_nonneg (by norm_num) hKr0)
  have hD : (K' : ℚ) / K * (∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ)))) *
      ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047)) ≤
      2101 / 2097 * ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047)) :=
    mul_le_mul_of_nonneg_right hKK.2 hM0
  have hfinal : (2 : ℚ) ≤
      1025 / 1024 * (2101 / 2097 * ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) := by
    calc (2 : ℚ) = (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) := hEq.symm
      _ ≤ 1025 / 1024 * ((K' : ℚ) / K) *
          ((∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ)))) *
            ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) := hC
      _ = 1025 / 1024 * ((K' : ℚ) / K * (∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ)))) *
          ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) := by ring
      _ ≤ 1025 / 1024 * (2101 / 2097 * ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) :=
          mul_le_mul_of_nonneg_left hD (by norm_num)
  linarith

-- Section 4. Lower bounds for the parent of a least odd prime child; modular facts.

theorem child_cases {N c : ℕ} (hN0 : N ≠ 0) (hN : 2 ∣ N) (hc : c.Prime) (hc2 : c ≠ 2)
    (hcN : c ∣ N) (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ N → c ≤ c') :
    (∃ i, N = c * 2 ^ i) ∨ 2 * c * c ≤ N := by
  obtain ⟨k, rfl⟩ := hcN
  have hk0 : k ≠ 0 := by rintro rfl; simp at hN0
  have hmul := Nat.ordProj_mul_ordCompl_eq_self k 2
  by_cases ho1 : k / 2 ^ k.factorization 2 = 1
  · left
    refine ⟨k.factorization 2, ?_⟩
    rw [ho1, mul_one] at hmul
    rw [hmul]
  · right
    have hq := Nat.minFac_prime ho1
    have hqo : (k / 2 ^ k.factorization 2).minFac ∣ k / 2 ^ k.factorization 2 := Nat.minFac_dvd _
    have hodd : ¬ 2 ∣ k / 2 ^ k.factorization 2 := Nat.not_dvd_ordCompl Nat.prime_two hk0
    have hq2 : (k / 2 ^ k.factorization 2).minFac ≠ 2 := fun h => by
      have h' := hqo
      rw [h] at h'
      exact hodd h'
    have hok : k / 2 ^ k.factorization 2 ∣ k := Dvd.intro_left _ hmul
    have hopos : 0 < k / 2 ^ k.factorization 2 :=
      Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hmul; exact hk0 hmul.symm
    have hcq : c ≤ (k / 2 ^ k.factorization 2).minFac :=
      hmin _ hq hq2 ((hqo.trans hok).mul_left c)
    have hco : c ≤ k / 2 ^ k.factorization 2 := hcq.trans (Nat.minFac_le hopos)
    have hcop2c : Nat.Coprime 2 c := (Nat.coprime_primes Nat.prime_two hc).mpr (Ne.symm hc2)
    have h2k : 2 ∣ k := (Nat.Coprime.dvd_mul_left hcop2c).mp hN
    have hcop : Nat.Coprime 2 (k / 2 ^ k.factorization 2) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    have h2o : 2 * (k / 2 ^ k.factorization 2) ≤ k :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2k hok)
    calc 2 * c * c = c * (2 * c) := by ring
      _ ≤ c * (2 * (k / 2 ^ k.factorization 2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hco)
      _ ≤ c * k := Nat.mul_le_mul_left _ h2o

theorem R127 {p : ℕ} (hp : p.Prime) (hd : 127 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → 127 ≤ c') : 32257 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases (by omega) h2 (by norm_num) (by norm_num) hd hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 8 := by
      by_contra hcon
      have : 2 ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> (obtain rfl : p = _ := Nat.succ_injective hi) <;> norm_num at hp
  · omega

theorem R103 {p : ℕ} (hp : p.Prime) (hd : 103 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → 103 ≤ c') : 823 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases (by omega) h2 (by norm_num) (by norm_num) hd hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 3 := by
      by_contra hcon
      have : 2 ^ 3 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> (obtain rfl : p = _ := Nat.succ_injective hi) <;> norm_num at hp
  · omega

theorem R7 {p : ℕ} (hp : p.Prime) (h7 : 7 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1) (h5 : ¬ 5 ∣ p + 1)
    (h13 : ¬ 13 ∣ p + 1) (h49 : ¬ 7 * 7 ∣ p + 1) (hne : p ≠ 13) : 223 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have h14 : 14 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := h14
  have hj16 : j < 16 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 14 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

theorem R13 {p : ℕ} (hp : p.Prime) (h13 : 13 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1) (h5 : ¬ 5 ∣ p + 1)
    (h7 : ¬ 7 ∣ p + 1) (h11 : ¬ 11 ∣ p + 1) (h17 : ¬ 17 ∣ p + 1) (h43 : ¬ 43 ∣ p + 1)
    (h169 : ¬ 13 * 13 ∣ p + 1) (hne : p ≠ 103) : 1663 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have h26 : 26 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := h26
  have hj64 : j < 64 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 26 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

theorem exists_prime_mod3 : ∀ N : ℕ, N % 3 = 2 → ∃ p, p.Prime ∧ p ∣ N ∧ p % 3 = 2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    have hN1 : N ≠ 1 := by omega
    have hq := Nat.minFac_prime hN1
    have hqd := Nat.minFac_dvd N
    have h3 : N.minFac % 3 ≠ 0 := by
      intro h
      have : 3 ∣ N := (Nat.dvd_of_mod_eq_zero h).trans hqd
      omega
    by_cases h2 : N.minFac % 3 = 2
    · exact ⟨_, hq, hqd, h2⟩
    · have h1 : N.minFac % 3 = 1 := by omega
      obtain ⟨k, hk⟩ := hqd
      have hk2 : k % 3 = 2 := by
        have : (N.minFac * k) % 3 = 2 := by rw [← hk]; exact hN
        rw [Nat.mul_mod, h1] at this
        omega
      have hklt : k < N := by
        have := hq.two_le
        have hk0 : 0 < k := by omega
        calc k < N.minFac * k := by nlinarith
          _ = N := hk.symm
      obtain ⟨p, hp, hpd, hp2⟩ := ih k hklt hk2
      exact ⟨p, hp, hpd.trans (Dvd.intro_left _ hk.symm), hp2⟩

theorem not_dvd_fourth_11 (x : ℕ) : ¬ 11 ∣ x ^ 4 + 1 := by
  intro h
  have h' := (ZMod.natCast_eq_zero_iff (x ^ 4 + 1) 11).mpr h
  push_cast at h'
  exact (by decide : ∀ y : ZMod 11, y ^ 4 + 1 ≠ 0) _ h'

theorem not_dvd_fourth_23 (x : ℕ) : ¬ 23 ∣ x ^ 4 + 1 := by
  intro h
  have h' := (ZMod.natCast_eq_zero_iff (x ^ 4 + 1) 23).mpr h
  push_cast at h'
  exact (by decide : ∀ y : ZMod 23, y ^ 4 + 1 ≠ 0) _ h'

theorem not_dvd_fourth_5 (x : ℕ) : ¬ 5 ∣ x ^ 4 + 1 := by
  intro h
  have h' := (ZMod.natCast_eq_zero_iff (x ^ 4 + 1) 5).mpr h
  push_cast at h'
  exact (by decide : ∀ y : ZMod 5, y ^ 4 + 1 ≠ 0) _ h'

-- Section 5. The cases with m at least 10.

theorem step_ge {c t p : ℕ} {x y : ℚ} (ht : 2 ≤ t) (hpt : t ≤ p)
    (hx : x ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (hy : (1 + 1 / (c : ℚ)) * (((t : ℚ) + 1) / ((t : ℚ) - 1)) ≤ y) :
    (1 + 1 / (c : ℚ)) * x ≤ y :=
  (mul_le_mul_of_nonneg_left (hx.trans (B_anti ht hpt)) (by positivity)).trans hy

-- If no prime of P has 3 as a child, the weight of 3 is at most 4/3 and the inequality fails.
theorem case_top3 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h3 : ∀ p ∈ P, ¬ 3 ∣ p + 1) : False := by
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 4 / 3 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 := by rw [hβ]; norm_num
  have b7 : β 7 = 4 / 3 := by rw [hβ]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [hβ]; norm_num
  have b127 : β 127 = 64 / 63 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) := fun c e3 => by
    rw [hβ, if_neg e3]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    rw [bd p e3]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3; exact absurd hd (h3 p hp)
    exact absurd (bd c e3) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

theorem case_odd {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (hodd : m % 2 = 1) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h3d : 3 ∣ 2 ^ m + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow 2 1 (Nat.odd_iff.mpr hodd)
    simpa using h
  exact case_top3 hP hN hK hKK E hm (S3 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h3d)

-- 4 ∣ m.  The hypothesis hres removes the one situation the method does not reach: some prime
-- of N that is 2 mod 3 divides 2 ^ m + 1, 3 is in P, and 3 does not divide K'.
theorem case_zero_mod_four {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h4 : m % 4 = 0)
    (hres : (∃ z ∈ N, z ∣ 2 ^ m + 1 ∧ z % 3 = 2) → 3 ∈ P → 3 ∣ K') : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨k, rfl⟩ : ∃ k, m = k * 4 := ⟨m / 4, by omega⟩
  have hmod : (2 ^ (k * 4) + 1) % 3 = 2 := by
    rw [mul_comm, pow_mul, Nat.add_mod, Nat.pow_mod]; norm_num
  obtain ⟨p0, hp0, hp0d, hp03⟩ := exists_prime_mod3 _ hmod
  by_cases hp0z : p0 ∈ N
  · by_cases h3P : 3 ∈ P
    · exact case_top3 hP hN hK hKK E hm
        (S7 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) (hres ⟨p0, hp0z, hp0d, hp03⟩ h3P))
    · exact case_top3 hP hN hK hKK E hm
        (fun p hp hd => h3P (S1 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp hd))
  have hx : 2 ^ (k * 4) + 1 = (2 ^ k) ^ 4 + 1 := by rw [pow_mul]
  have hp02 : p0 ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega))).mp hp0d
    omega
  have hp0P : p0 ∈ P := S5 p0 hp0 hp02 hp0z hp0d
  have h3d : 3 ∣ p0 + 1 := by omega
  have h3P : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p0 hp0P h3d
  have hp029 : 29 ≤ p0 := by
    by_contra hlt
    have hlt' : p0 < 29 := by omega
    have h2le := hp0.two_le
    rw [hx] at hp0d
    interval_cases p0 <;> first
      | omega
      | (norm_num at hp0; done)
      | exact not_dvd_fourth_5 _ hp0d
      | exact not_dvd_fourth_11 _ hp0d
      | exact not_dvd_fourth_23 _ hp0d
      | exact S4b 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 17 hp0P (by norm_num)
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 4 / 3 * (1 + 1 / (p0 : ℚ)) else
      if p = p0 then 1 + 1 / (p0 : ℚ) else ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hp0q : (29 : ℚ) ≤ p0 := by exact_mod_cast hp029
  have hinv0 : 0 < 1 / (p0 : ℚ) := by positivity
  have hinv : 1 / (p0 : ℚ) ≤ 1 / 29 := one_div_le_one_div_of_le (by norm_num) hp0q
  have hp0ne3 : p0 ≠ 3 := by omega
  have b3 : β 3 = 4 / 3 * (1 + 1 / (p0 : ℚ)) := by rw [hβ, if_pos rfl]
  have bp0 : β p0 = 1 + 1 / (p0 : ℚ) := by rw [hβ, if_neg hp0ne3, if_pos rfl]
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ p0 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) := fun c e3 e0 => by
    rw [hβ, if_neg e3, if_neg e0]
  have b7 : β 7 = 4 / 3 := by rw [bd 7 (by norm_num) (by omega)]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [bd 31 (by norm_num) (by omega)]; norm_num
  have b127 : β 127 = 64 / 63 := by rw [bd 127 (by norm_num) (by omega)]; norm_num
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3
      rw [b3]
      have e1 : (1 : ℚ) + 1 / ((3 : ℕ) : ℚ) = 4 / 3 := by norm_num
      have e2 : (((3 : ℕ) : ℚ) + 1) / (((3 : ℕ) : ℚ) - 1) = 2 := by norm_num
      rw [e1, e2]
      constructor <;> linarith
    by_cases e0 : p = p0
    · subst e0; rw [bp0]; exact ⟨le_refl _, one_add_le_B hp0.two_le⟩
    rw [bd p e3 e0]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = p0 := S2 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp p0 hp0P hd h3d
      rw [b3, bp0]; norm_num
    by_cases e0 : c = p0
    · subst e0; exact absurd hd (S3 c hp0 hp02 hp0z hp0d p hp)
    exact absurd (bd c e3 e0) hne
  · rw [b3, b7, b31, b127]
    refine ⟨by linarith, by norm_num, by norm_num, by norm_num⟩
  · rw [b3, b7, b31, b127]
    linarith

theorem case3_pre {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (h4 : m % 4 = 2) :
    5 ∈ P ∧ 3 ∈ P ∧ (∀ p ∈ P, 3 ∣ p + 1 → p = 5) ∧ (∀ p ∈ P, ¬ 5 ∣ p + 1) := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h5d : 5 ∣ 2 ^ m + 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + 2 := ⟨m / 4, by omega⟩
    apply Nat.dvd_of_mod_eq_zero
    rw [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]; norm_num
  have h5 : 5 ∈ P := S5 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h5d
  have h3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 5 h5 (by norm_num)
  exact ⟨h5, h3, fun p hp hd => S2 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 5 h5 hd (by norm_num),
    fun p hp => S3 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h5d p hp⟩

theorem case3_ii {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h4 : m % 4 = 2) (h13 : 13 ∉ P) : False := by
  obtain ⟨h5, h3, T3, T5⟩ := case3_pre hP hN hK E h4
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 8 / 5 else if p = 5 then 6 / 5 else
      if p = 7 then 8 / 7 * (224 / 222) else if p = 127 then 128 / 127 * (32258 / 32256) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 8 / 5 := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 222) := by rw [hβ]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (32258 / 32256) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 127 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e127 => by rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e127 : p = 127
    · subst e127; rw [b127]; norm_num
    rw [bd p e3 e5 e7 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5; exact absurd hd (T5 p hp)
    by_cases e7 : c = 7
    · subst e7
      have hge : 223 ≤ p := R7 (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => h13 (S1 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h))
        (S4b 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp)
        (fun h => h13 (h ▸ hp))
      rw [b7]
      exact step_ge (t := 223) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      have hge : 32257 ≤ p := R127 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
      rw [b127]
      exact step_ge (t := 32257) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e7 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

theorem case3_iii {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h4 : m % 4 = 2) (h7 : 7 ∈ P) (h13 : 13 ∈ P)
    (h103 : 103 ∉ P) : False := by
  obtain ⟨h5, h3, T3, T5⟩ := case3_pre hP hN hK E h4
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h31 : 31 ∉ P := by
    intro h31
    have hsub : ({3, 5, 7, 13, 31} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h31
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  have h11 : 11 ∉ P := fun h => by
    have := T3 11 h (by norm_num)
    omega
  have h17 : 17 ∉ P := fun h => by
    have := T3 17 h (by norm_num)
    omega
  have h43 : 43 ∉ P := fun h => h11 (S1 11 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 43 h (by norm_num))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 8 / 5 else if p = 5 then 6 / 5 else
      if p = 7 then 8 / 7 * (14 / 13 * (1664 / 1662)) else
      if p = 13 then 14 / 13 * (1664 / 1662) else if p = 31 then 1 else
      if p = 127 then 128 / 127 * (32258 / 32256) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 8 / 5 := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (1664 / 1662)) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (1664 / 1662) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (32258 / 32256) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 13 → c ≠ 31 → c ≠ 127 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e13 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e13, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; rw [b127]; norm_num
    rw [bd p e3 e5 e7 e13 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5; exact absurd hd (T5 p hp)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 13 := S2 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 13 h13 hd (by norm_num)
      rw [b7, b13]; norm_num
    by_cases e13 : c = 13
    · subst e13
      have hge : 1663 ≤ p := R13 (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 11 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => h17 (S1 17 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h))
        (fun h => h43 (S1 43 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h))
        (S4b 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp)
        (fun h => h103 (h ▸ hp))
      rw [b13]
      exact step_ge (t := 1663) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31; exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127
      have hge : 32257 ≤ p := R127 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
      rw [b127]
      exact step_ge (t := 32257) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e7 e13 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

theorem case3_iv {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h4 : m % 4 = 2) (h7 : 7 ∈ P) (h13 : 13 ∈ P)
    (h103 : 103 ∈ P) : False := by
  obtain ⟨h5, h3, T3, T5⟩ := case3_pre hP hN hK E h4
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h31 : 31 ∉ P := by
    intro h31
    have hsub : ({3, 5, 7, 13, 31} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h31
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  have h127 : 127 ∉ P := by
    intro h127
    have hsub : ({3, 5, 7, 13, 103, 127} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h103
      · exact h127
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 8 / 5 else if p = 5 then 6 / 5 else
      if p = 7 then 8 / 7 * (14 / 13 * (104 / 103 * (824 / 822))) else
      if p = 13 then 14 / 13 * (104 / 103 * (824 / 822)) else
      if p = 103 then 104 / 103 * (824 / 822) else if p = 31 then 1 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 8 / 5 := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (104 / 103 * (824 / 822))) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (104 / 103 * (824 / 822)) := by rw [hβ]; norm_num
  have b103 : β 103 = 104 / 103 * (824 / 822) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 13 → c ≠ 103 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e13 e103 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e13, if_neg e103, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    by_cases e103 : p = 103
    · subst e103; rw [b103]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e7 e13 e103 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5; exact absurd hd (T5 p hp)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 13 := S2 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 13 h13 hd (by norm_num)
      rw [b7, b13]; norm_num
    by_cases e13 : c = 13
    · subst e13
      obtain rfl : p = 103 := S2 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 103 h103 hd (by norm_num)
      rw [b13, b103]; norm_num
    by_cases e103 : c = 103
    · subst e103
      have hge : 823 ≤ p := R103 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
      rw [b103]
      exact step_ge (t := 823) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31; exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127; exact absurd hc h127
    exact absurd (bd c e3 e5 e7 e13 e103 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

theorem big {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (hres : m % 4 = 0 → (∃ z ∈ N, z ∣ 2 ^ m + 1 ∧ z % 3 = 2) → 3 ∈ P → 3 ∣ K') :
    False := by
  have h : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases h with h | h | h | h
  · exact case_zero_mod_four hP hN hK hKK E hm h (hres h)
  · exact case_odd hP hN hK hKK E hm (by omega)
  · by_cases h13 : 13 ∈ P
    · have h7 : 7 ∈ P := (facts hP hK E).1 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 13 h13 (by norm_num)
      by_cases h103 : 103 ∈ P
      · exact case3_iv hP hN hK hKK E hm h h7 h13 h103
      · exact case3_iii hP hN hK hKK E hm h h7 h13 h103
    · exact case3_ii hP hN hK hKK E hm h h13
  · exact case_odd hP hN hK hKK E hm (by omega)


-- Section 6. From a unitary perfect n to the equation (E), and the theorems.

theorem kernel_balance {n : ℕ} {N : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n) (h2 : 2 ∣ n)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ N → n.factorization r = 1) :
    (2 ^ n.factorization 2 + 1) *
        (∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), (1 + z ^ n.factorization z)) *
        ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), (p + 1) =
      2 ^ (n.factorization 2 + 1) *
        (∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), z ^ n.factorization z) *
        ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), p := by
  have hn0 : n ≠ 0 := h.2.ne'
  have hprod := prod_eq_two_mul h
  have hself := prod_primeFactors_pow_self hn0
  have h2mem : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hn0⟩
  rw [← Finset.mul_prod_erase _ _ h2mem,
    ← Finset.prod_filter_mul_prod_filter_not (n.primeFactors.erase 2) (fun r => r ∈ N)] at hprod hself
  have hPs : ∀ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), n.factorization p = 1 :=
    fun p hp => by
      obtain ⟨h1, hpN⟩ := Finset.mem_filter.mp hp
      exact hs p (Finset.mem_of_mem_erase h1) (Finset.ne_of_mem_erase h1) hpN
  have e1 : ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), (1 + p ^ n.factorization p) =
      ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), (p + 1) :=
    Finset.prod_congr rfl fun p hp => by rw [hPs p hp, pow_one, add_comm]
  have e2 : ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), p ^ n.factorization p =
      ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), p :=
    Finset.prod_congr rfl fun p hp => by rw [hPs p hp, pow_one]
  rw [e1] at hprod
  rw [e2] at hself
  rw [pow_succ]
  linarith

/-- **Graham's theorem with a sparse set of large exceptional primes.**  Let n be unitary perfect
and N a finite set of primes such that every odd prime of n outside N divides n exactly once
(the primes of N may divide n to any power, or not at all).  Assume every z in N is at least 128
and at least N.card + 3, and that the product over N of (z + 1) / (z - 2 - N.card) is at most
2101/2097.  Then, outside the residue family
  4 ∣ a,  some z in N with z ≡ 2 mod 3 divides 2 ^ a + 1,  3 ∣ n,  and no z in N with
  z ≡ 2 mod 3 has odd exponent in n                                   (a = padicValNat 2 n),
the 2-adic valuation of n is at most 9.  For N empty this is the m ≥ 10 part of Graham's theorem. -/
theorem two_adic_le_nine_of_sparse_nonsimple {n : ℕ} {N : Finset ℕ}
    (h : Erdos1052.IsUnitaryPerfect n)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hΛ : ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ N → n.factorization r = 1)
    (hres : 4 ∣ padicValNat 2 n → (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) → 3 ∣ n →
      ∃ z ∈ N, z % 3 = 2 ∧ Odd (n.factorization z)) :
    padicValNat 2 n ≤ 9 := by
  by_contra hcon
  have hn0 : n ≠ 0 := h.2.ne'
  have hfac : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  rw [← hfac] at hcon hres
  have hm : 10 ≤ n.factorization 2 := by omega
  have h2 : 2 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have E := kernel_balance h h2 hs
  have hP : ∀ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), p.Prime ∧ p ≠ 2 :=
    fun p hp => by
      have h1 := (Finset.mem_filter.mp hp).1
      exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h1), Finset.ne_of_mem_erase h1⟩
  have hMmem : ∀ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N),
      z.Prime ∧ z ∈ N ∧ 1 ≤ n.factorization z := fun z hz => by
    obtain ⟨h1, hzN⟩ := Finset.mem_filter.mp hz
    have hzpf := Finset.mem_of_mem_erase h1
    exact ⟨Nat.prime_of_mem_primeFactors hzpf, hzN,
      (Nat.prime_of_mem_primeFactors hzpf).factorization_pos_of_dvd hn0
        (Nat.dvd_of_mem_primeFactors hzpf)⟩
  have hK : ∀ c : ℕ, c.Prime →
      c ∣ ∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), z ^ n.factorization z →
      c ∈ N := fun c hc hd => by
    obtain ⟨z, hz, hcz⟩ := (Prime.dvd_finsetProd_iff hc.prime _).mp hd
    obtain ⟨hzp, hzN, _⟩ := hMmem z hz
    rw [(Nat.prime_dvd_prime_iff_eq hc hzp).mp (hc.dvd_of_dvd_pow hcz)]
    exact hzN
  have hK1 : ∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), z ^ n.factorization z ≤
      ∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), (1 + z ^ n.factorization z) :=
    Finset.prod_le_prod' fun z _ => Nat.le_add_left _ _
  have hs0 : (0 : ℚ) ≤ (N.card : ℚ) := Nat.cast_nonneg _
  have hNq : ∀ z ∈ N, (N.card : ℚ) + 3 ≤ z := fun z hz => by exact_mod_cast (hN z hz).2.2
  have hK2 : ((∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N),
        (1 + z ^ n.factorization z) : ℕ) : ℚ) /
      ((∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), z ^ n.factorization z : ℕ) : ℚ) *
      ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 := by
    have hΛ0 : (0 : ℚ) ≤ ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) :=
      Finset.prod_nonneg fun z hz => by
        have := hNq z hz
        exact div_nonneg (by linarith) (by linarith)
    have hratio : ((∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N),
          (1 + z ^ n.factorization z) : ℕ) : ℚ) /
        ((∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), z ^ n.factorization z : ℕ) : ℚ) ≤
        ∏ z ∈ N, (1 + 1 / (z : ℚ)) := by
      push_cast
      rw [← Finset.prod_div_distrib]
      refine (Finset.prod_le_prod (fun z hz => ?_) (fun z hz => ?_)).trans
        (Finset.prod_le_prod_of_subset_of_one_le (fun z hz => (hMmem z hz).2.1)
          (fun z _ => by positivity)
          (fun z _ _ => by
            have : (0 : ℚ) ≤ 1 / (z : ℚ) := by positivity
            linarith))
      · positivity
      · obtain ⟨hzp, hzN, he⟩ := hMmem z hz
        have hz1 : (1 : ℚ) ≤ z := by exact_mod_cast hzp.one_lt.le
        have hpow : (z : ℚ) ≤ (z : ℚ) ^ n.factorization z := by
          calc (z : ℚ) = (z : ℚ) ^ 1 := (pow_one _).symm
            _ ≤ (z : ℚ) ^ n.factorization z := pow_le_pow_right₀ hz1 he
        have hzpos : (0 : ℚ) < z := by linarith
        rw [div_le_iff₀ (by linarith)]
        have : 1 / (z : ℚ) * (z : ℚ) ^ n.factorization z ≥ 1 := by
          rw [ge_iff_le, one_div, ← div_eq_inv_mul, le_div_iff₀ hzpos]
          linarith
        nlinarith
    calc _ ≤ (∏ z ∈ N, (1 + 1 / (z : ℚ))) * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) :=
          mul_le_mul_of_nonneg_right hratio hΛ0
      _ = ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun z hz => ?_
          have := hNq z hz
          have hzpos : (z : ℚ) ≠ 0 := by linarith
          have hden : (z : ℚ) - 2 - (N.card : ℚ) ≠ 0 := by linarith
          field_simp
      _ ≤ 2101 / 2097 := hΛ
  refine big hP hN hK ⟨hK1, hK2⟩ E hm (fun h4 hex h3P => ?_)
  have h3n : 3 ∣ n :=
    Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_filter.mp h3P).1)
  obtain ⟨z, hzN, hz3, hodd⟩ := hres (by omega) hex h3n
  have hzp := (hN z hzN).1
  have hz128 := (hN z hzN).2.1
  have hzn : z ∣ n := Nat.dvd_of_factorization_pos (fun h0 => by
    rw [h0] at hodd
    exact absurd hodd (by decide))
  have hzM : z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N) :=
    Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by omega, Nat.mem_primeFactors.mpr ⟨hzp, hzn, hn0⟩⟩,
      hzN⟩
  have hdvd := Odd.nat_add_dvd_pow_add_pow z 1 hodd
  rw [one_pow] at hdvd
  have h3 : 3 ∣ z + 1 := by omega
  have h3z : 3 ∣ 1 + z ^ n.factorization z := by rw [add_comm]; exact h3.trans hdvd
  exact h3z.trans (Finset.dvd_prod_of_mem (fun z => 1 + z ^ n.factorization z) hzM)

-- A subset of an admissible set is admissible (so H1 is exactly: no admissible N contains S).
theorem admissible_of_subset {M N : Finset ℕ} (hMN : M ⊆ N)
    (hN : (∀ z ∈ N, 128 ≤ z ∧ N.card + 3 ≤ z))
    (hΛ : ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097) :
    (∀ z ∈ M, 128 ≤ z ∧ M.card + 3 ≤ z) ∧
      ∏ z ∈ M, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (M.card : ℚ))) ≤ 2101 / 2097 := by
  have hcard := Finset.card_le_card hMN
  refine ⟨fun z hz => ⟨(hN z (hMN hz)).1, by have := (hN z (hMN hz)).2; omega⟩, ?_⟩
  calc ∏ z ∈ M, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (M.card : ℚ)))
      ≤ ∏ z ∈ M, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) := by
        refine Finset.prod_le_prod (fun z hz => ?_) (fun z hz => ?_)
        · have hNz : (N.card : ℚ) + 3 ≤ z := by exact_mod_cast (hN z (hMN hz)).2
          have hc : (M.card : ℚ) ≤ N.card := by exact_mod_cast hcard
          exact div_nonneg (by positivity) (by linarith)
        · have hNz : (N.card : ℚ) + 3 ≤ z := by exact_mod_cast (hN z (hMN hz)).2
          have hc : (M.card : ℚ) ≤ N.card := by exact_mod_cast hcard
          exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
    _ ≤ ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) := by
        refine Finset.prod_le_prod_of_subset_of_one_le hMN (fun z hz => ?_) (fun z hz _ => ?_)
        · have hNz : (N.card : ℚ) + 3 ≤ z := by exact_mod_cast (hN z (hMN hz)).2
          exact div_nonneg (by positivity) (by linarith)
        · have hNz : (N.card : ℚ) + 3 ≤ z := by exact_mod_cast (hN z hz).2
          rw [le_div_iff₀ (by linarith)]
          linarith
    _ ≤ 2101 / 2097 := hΛ

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max (max A1 A2) 9, fun n h hsq => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  set S : Finset ℕ := {p ∈ n.primeFactors | p ≠ 2 ∧ 2 ≤ n.factorization p} with hSdef
  have hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n := by
    intro p
    simp only [hSdef, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, -, -⟩, h2', he⟩
      exact ⟨hp, h2', (hp.pow_dvd_iff_le_factorization hn0).mpr he⟩
    · rintro ⟨hp, h2', hd⟩
      exact ⟨⟨hp, (dvd_pow_self p two_ne_zero).trans hd, hn0⟩, h2',
        (hp.pow_dvd_iff_le_factorization hn0).mp hd⟩
  have hsN : ∀ N : Finset ℕ, S ⊆ N →
      ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ N → n.factorization r = 1 := by
    intro N hSN r hr hr2 hrN
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hrN (hSN ((hS r).mpr ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩))
    omega
  by_cases hadm : (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097
  swap
  · exact (h1 n h hsq S hS hadm).trans ((le_max_left _ _).trans (le_max_left _ _))
  obtain ⟨hadm1, hadm2⟩ := hadm
  have hNS : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z :=
    fun z hz => ⟨((hS z).mp hz).1, hadm1 z hz⟩
  by_cases h43 : 4 ∣ padicValNat 2 n ∧ 3 ∣ n
  swap
  · exact (two_adic_le_nine_of_sparse_nonsimple h hNS hadm2 (hsN S subset_rfl)
      (fun h4 _ h3 => absurd ⟨h4, h3⟩ h43)).trans (le_max_right _ _)
  obtain ⟨h4, h3⟩ := h43
  by_cases hall : ∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)
  · exact (h2 n h hsq S hS hadm1 hadm2 h4 h3 hall).trans ((le_max_right _ _).trans (le_max_left _ _))
  · simp only [not_forall] at hall
    obtain ⟨N, hSN, hN, hΛ, hnot⟩ := hall
    refine (two_adic_le_nine_of_sparse_nonsimple h hN hΛ (hsN N hSN)
      (fun _ hex _ => ?_)).trans (le_max_right _ _)
    by_contra hno
    refine hnot ⟨hex, fun z hz hz3 => ?_⟩
    by_contra hodd
    exact hno ⟨z, hz, hz3, Nat.not_even_iff_odd.mp hodd⟩

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1
