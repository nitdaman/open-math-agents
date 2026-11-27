import FormalConjectures.Wikipedia.GaussCircleProblem

/-!
# Gauss circle problem — exact floor formula

We prove `GaussCircleProblem.exact_form_floor`: for every `r ≥ 0`,
`N r = 1 + 4 * ∑' i : ℕ, (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)`.

## Proof outline
1. With `M = ⌊r ^ 2⌋₊`, the lattice points in `Metric.closedBall (0 : ℝ²) r` are exactly the pairs
   `(a, b) : ℤ × ℤ` with `a.natAbs ^ 2 + b.natAbs ^ 2 ≤ M`, giving `N r = 1 + ∑ n ∈ Icc 1 M, r2 n`.
2. Identifying `(a, b)` with `z = ⟨a, b⟩ : GaussianInt` of norm `n`, every nonzero `z` has a unique
   associate in the first quadrant `{w | 0 < w.re ∧ 0 ≤ w.im}`, so `r2 n = 4 * q n` for `n ≥ 1`.
3. Using `EuclideanDomain.gcd` on `GaussianInt`, we prove `q` is multiplicative on coprime
   arguments and agrees with `D n = ∑ d ∈ n.divisors, χ4 d` on prime powers (`p = 2`, `p ≡ 1`,
   `p ≡ 3 (mod 4)`), establishing Jacobi's two-squares formula `r2 n = 4 * ∑ d ∈ n.divisors, χ4 d`.
4. Swapping finite sums yields `∑ n ∈ Icc 1 M, D n = ∑ d ∈ Icc 1 M, (M / d) * χ4 d`, and
   `⌊r ^ 2 / d⌋ = M / d` together with `tsum_eq_sum` closes the exact floor identity.
-/

-- Problem: Gauss circle problem — exact form floor
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/GaussCircleProblem.lean:104 (declaration GaussCircleProblem.exact_form_floor)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace GaussCircleFloorProof

open scoped EuclideanGeometry

/- ### Character modulo 4 and divisor sum -/

private def chi4 (d : ℕ) : ℤ :=
  if d % 4 = 1 then 1 else if d % 4 = 3 then -1 else 0

private lemma chi4_one : chi4 1 = 1 := by decide

private lemma chi4_mul (a b : ℕ) : chi4 (a * b) = chi4 a * chi4 b := by
  have ha := Nat.mod_lt a (by omega : 0 < 4)
  have hb := Nat.mod_lt b (by omega : 0 < 4)
  unfold chi4
  rw [Nat.mul_mod]
  interval_cases (a % 4) <;> interval_cases (b % 4) <;> decide

private lemma chi4_pow (p k : ℕ) : chi4 (p ^ k) = (chi4 p) ^ k := by
  induction k with
  | zero => simp [chi4_one]
  | succ k ih => rw [pow_succ, chi4_mul, ih, pow_succ]

private def divSumChi4 (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi4 d

private lemma divSumChi4_one : divSumChi4 1 = 1 := by
  simp [divSumChi4, chi4_one]

private lemma divSumChi4_mul {m n : ℕ} (hmn : Nat.Coprime m n) :
    divSumChi4 (m * n) = divSumChi4 m * divSumChi4 n := by
  simp only [divSumChi4]
  rw [hmn.divisors_mul, Finset.sum_map]
  change ∑ p ∈ (m.divisors ×ˢ n.divisors).attach, chi4 (p.1.1 * p.1.2) = _
  rw [Finset.sum_attach (s := m.divisors ×ˢ n.divisors) (f := fun p => chi4 (p.1 * p.2)),
    Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact chi4_mul a b

private lemma divSumChi4_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    divSumChi4 (p ^ k) = ∑ j ∈ Finset.range (k + 1), (chi4 p) ^ j := by
  rw [divSumChi4, Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  simpa using chi4_pow p j

/- ### Gaussian integers: units, first-quadrant canonical form, norm -/

private def giNorm (z : GaussianInt) : ℕ := z.norm.natAbs

private lemma giNorm_eq (z : GaussianInt) :
    giNorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  simpa [giNorm, sq] using GaussianInt.natAbs_norm_eq z

private lemma giNorm_mul (z w : GaussianInt) : giNorm (z * w) = giNorm z * giNorm w := by
  simp [giNorm, Zsqrtd.norm_mul, Int.natAbs_mul]

private lemma giNorm_pow (z : GaussianInt) (k : ℕ) : giNorm (z ^ k) = (giNorm z) ^ k := by
  induction k with
  | zero => simp [giNorm]
  | succ k ih => rw [pow_succ, giNorm_mul, ih, pow_succ]

private lemma giNorm_star (z : GaussianInt) : giNorm (star z) = giNorm z := by
  simp [giNorm, Zsqrtd.norm_conj]

private lemma giNorm_natCast (n : ℕ) : giNorm (n : GaussianInt) = n ^ 2 := by
  simp [giNorm, Zsqrtd.norm_natCast, Int.natAbs_mul, sq]

private lemma giNorm_eq_one_iff (z : GaussianInt) : giNorm z = 1 ↔ IsUnit z :=
  Zsqrtd.norm_eq_one_iff

private lemma giNorm_eq_zero_iff (z : GaussianInt) : giNorm z = 0 ↔ z = 0 := by
  simp only [giNorm, Int.natAbs_eq_zero]
  exact Zsqrtd.norm_eq_zero_iff (d := -1) (by norm_num) z

private lemma giNorm_eq_of_associated {z w : GaussianInt} (h : Associated z w) :
    giNorm z = giNorm w := by
  rcases h with ⟨u, rfl⟩
  rw [giNorm_mul, (giNorm_eq_one_iff (u : GaussianInt)).mpr u.isUnit, mul_one]

private lemma giNorm_dvd_of_dvd {z w : GaussianInt} (h : z ∣ w) : giNorm z ∣ giNorm w := by
  rcases h with ⟨c, rfl⟩
  rw [giNorm_mul]
  exact dvd_mul_right _ _

private lemma gi_mul_star (z : GaussianInt) : z * star z = (giNorm z : GaussianInt) := by
  have h1 : (z.norm : GaussianInt) = z * star z := Zsqrtd.norm_eq_mul_conj z
  have h2 : (giNorm z : GaussianInt) = (z.norm : GaussianInt) := by
    simp [giNorm]
  exact h1.symm.trans h2.symm

private def giI : GaussianInt := ⟨0, 1⟩

private def giUnits : Finset GaussianInt := {1, -1, giI, -giI}

private lemma giUnits_card : giUnits.card = 4 := by decide

private lemma mem_giUnits_iff (u : GaussianInt) : u ∈ giUnits ↔ IsUnit u := by
  constructor
  · intro hu
    rw [← giNorm_eq_one_iff]
    simp only [giUnits, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> decide
  · intro hu
    have hnorm : u.re.natAbs ^ 2 + u.im.natAbs ^ 2 = 1 := by
      rw [← giNorm_eq, (giNorm_eq_one_iff u).mpr hu]
    have ha : u.re.natAbs ≤ 1 := by nlinarith
    have hb : u.im.natAbs ≤ 1 := by nlinarith
    have hcases : (u.re = 1 ∧ u.im = 0) ∨ (u.re = -1 ∧ u.im = 0) ∨
        (u.re = 0 ∧ u.im = 1) ∨ (u.re = 0 ∧ u.im = -1) := by
      interval_cases ha' : u.re.natAbs <;> interval_cases hb' : u.im.natAbs <;>
        omega
    simp only [giUnits, Finset.mem_insert, Finset.mem_singleton]
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; ext <;> simp [h1, h2]
    · right; left; ext <;> simp [h1, h2]
    · right; right; left; ext <;> simp [giI, h1, h2]
    · right; right; right; ext <;> simp [giI, h1, h2]

private def InQ1 (z : GaussianInt) : Prop := 0 < z.re ∧ 0 ≤ z.im

private instance : DecidablePred InQ1 := fun z => inferInstanceAs (Decidable (0 < z.re ∧ 0 ≤ z.im))

private def canon (z : GaussianInt) : GaussianInt :=
  if 0 < z.re ∧ 0 ≤ z.im then z
  else if z.re ≤ 0 ∧ 0 < z.im then -giI * z
  else if z.re < 0 ∧ z.im ≤ 0 then -z
  else giI * z

private lemma canon_associated (z : GaussianInt) : Associated z (canon z) := by
  have h2 : IsUnit (-1 : GaussianInt) := (mem_giUnits_iff (-1)).mp (by decide)
  have h3 : IsUnit giI := (mem_giUnits_iff giI).mp (by decide)
  have h4 : IsUnit (-giI) := (mem_giUnits_iff (-giI)).mp (by decide)
  unfold canon
  split_ifs
  · exact Associated.refl z
  · rcases h4 with ⟨u, hu⟩
    exact ⟨u, by rw [hu, mul_comm]⟩
  · rcases h2 with ⟨u, hu⟩
    exact ⟨u, by rw [hu]; ring⟩
  · rcases h3 with ⟨u, hu⟩
    exact ⟨u, by rw [hu, mul_comm]⟩

private lemma canon_inQ1 {z : GaussianInt} (hz : z ≠ 0) : InQ1 (canon z) := by
  have hne : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (by ext <;> simp [h.1, h.2])
  unfold canon InQ1
  split_ifs with h1 h2 h3
  · exact h1
  · constructor <;> simp [giI] <;> omega
  · constructor <;> simp <;> omega
  · constructor <;> simp [giI] <;> omega

private lemma eq_of_associated_inQ1 {z w : GaussianInt}
    (hz : InQ1 z) (hw : InQ1 w) (h : Associated z w) : z = w := by
  rcases h with ⟨u, hu⟩
  have hmem : (u : GaussianInt) ∈ giUnits := (mem_giUnits_iff u).mpr u.isUnit
  simp only [giUnits, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1 | h1 | h1
  · rw [h1, mul_one] at hu; exact hu
  · rw [h1] at hu
    have hre : w.re = -z.re := by rw [← hu]; simp
    have : 0 < z.re := hz.1
    have : 0 < w.re := hw.1
    omega
  · rw [h1] at hu
    have hre : w.re = -z.im := by rw [← hu]; simp [giI]
    have : 0 ≤ z.im := hz.2
    have : 0 < w.re := hw.1
    omega
  · rw [h1] at hu
    have him : w.im = -z.re := by rw [← hu]; simp [giI]
    have : 0 < z.re := hz.1
    have : 0 ≤ w.im := hw.2
    omega

private lemma canon_eq_iff_associated {z w : GaussianInt} (hz : z ≠ 0) (hw : w ≠ 0) :
    canon z = canon w ↔ Associated z w := by
  constructor
  · intro h
    exact (canon_associated z).trans (h ▸ (canon_associated w).symm)
  · intro h
    have hass : Associated (canon z) (canon w) :=
      (canon_associated z).symm.trans (h.trans (canon_associated w))
    exact eq_of_associated_inQ1 (canon_inQ1 hz) (canon_inQ1 hw) hass

private lemma canon_eq_self {z : GaussianInt} (hz : InQ1 z) : canon z = z := by
  have hz0 : z ≠ 0 := by
    intro h0; subst h0; exact lt_irrefl 0 hz.1
  exact eq_of_associated_inQ1 (canon_inQ1 hz0) hz (canon_associated z).symm

private lemma giNorm_canon (z : GaussianInt) : giNorm (canon z) = giNorm z :=
  giNorm_eq_of_associated (canon_associated z).symm

/- ### Finite sets of Gaussian integers of norm `n` -/

private def giOfNorm (n : ℕ) : Finset GaussianInt :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).image fun p => (⟨p.1, p.2⟩ : GaussianInt)).filter
    fun z => giNorm z = n

private lemma mem_giOfNorm_iff {n : ℕ} {z : GaussianInt} :
    z ∈ giOfNorm n ↔ giNorm z = n := by
  simp only [giOfNorm, Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro hn
    refine ⟨⟨(z.re, z.im), ⟨?_, ?_⟩, by ext <;> rfl⟩, hn⟩
    · have hle : z.re.natAbs ≤ n := by
        have hsq : z.re.natAbs ≤ z.re.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
        have := giNorm_eq z
        omega
      omega
    · have hle : z.im.natAbs ≤ n := by
        have hsq : z.im.natAbs ≤ z.im.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
        have := giNorm_eq z
        omega
      omega

private def Q1Set (n : ℕ) : Finset GaussianInt :=
  (giOfNorm n).filter InQ1

private lemma mem_Q1Set_iff {n : ℕ} {z : GaussianInt} :
    z ∈ Q1Set n ↔ giNorm z = n ∧ InQ1 z := by
  simp [Q1Set, mem_giOfNorm_iff]

private lemma card_giOfNorm_eq_four_mul {n : ℕ} (hn : 1 ≤ n) :
    (giOfNorm n).card = 4 * (Q1Set n).card := by
  have hbij : (giUnits ×ˢ Q1Set n).card = (giOfNorm n).card := by
    refine Finset.card_bij (fun p _ => p.1 * p.2) ?_ ?_ ?_
    · intro p hp
      rcases Finset.mem_product.mp hp with ⟨hu, hw⟩
      rw [mem_giOfNorm_iff, giNorm_mul]
      rw [(giNorm_eq_one_iff p.1).mpr ((mem_giUnits_iff p.1).mp hu), one_mul]
      exact (mem_Q1Set_iff.mp hw).1
    · intro p₁ hp₁ p₂ hp₂ heq
      rcases Finset.mem_product.mp hp₁ with ⟨hu₁, hw₁⟩
      rcases Finset.mem_product.mp hp₂ with ⟨hu₂, hw₂⟩
      rcases (mem_giUnits_iff p₁.1).mp hu₁ with ⟨u₁, hu₁'⟩
      rcases (mem_giUnits_iff p₂.1).mp hu₂ with ⟨u₂, hu₂'⟩
      have hass : Associated p₁.2 p₂.2 := by
        refine ⟨u₁ * u₂⁻¹, ?_⟩
        calc
          p₁.2 * ((u₁ * u₂⁻¹ : GaussianIntˣ) : GaussianInt)
            = (p₁.1 * p₁.2) * (u₂⁻¹ : GaussianIntˣ) := by
                rw [← hu₁', Units.val_mul]; ring
          _ = (p₂.1 * p₂.2) * (u₂⁻¹ : GaussianIntˣ) := by rw [heq]
          _ = p₂.2 * ((u₂ : GaussianInt) * (u₂⁻¹ : GaussianIntˣ)) := by
                rw [← hu₂']; ring
          _ = p₂.2 := by simp
      have hw_eq : p₁.2 = p₂.2 :=
        eq_of_associated_inQ1 (mem_Q1Set_iff.mp hw₁).2 (mem_Q1Set_iff.mp hw₂).2 hass
      have hw_ne : p₁.2 ≠ 0 := by
        intro h0
        have := (mem_Q1Set_iff.mp hw₁).1
        rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at this
        omega
      rw [hw_eq] at heq
      have hu_eq : p₁.1 = p₂.1 := mul_right_cancel₀ (hw_eq ▸ hw_ne) heq
      exact Prod.ext hu_eq hw_eq
    · intro z hz
      have hzn : giNorm z = n := mem_giOfNorm_iff.mp hz
      have hz0 : z ≠ 0 := by
        intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hzn; omega
      rcases (canon_associated z).symm with ⟨u, hu⟩
      refine ⟨((u : GaussianInt), canon z), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact (mem_giUnits_iff u).mpr u.isUnit
      · exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, hzn], canon_inQ1 hz0⟩
      · simpa [mul_comm] using hu
  rw [← hbij, Finset.card_product, giUnits_card]

/- ### Multiplicativity of `(Q1Set n).card` -/

private lemma isCoprime_natCast {m n : ℕ} (hmn : Nat.Coprime m n) :
    IsCoprime (m : GaussianInt) (n : GaussianInt) := by
  have hbez := Nat.gcd_eq_gcd_ab m n
  rw [hmn.gcd_eq_one] at hbez
  refine ⟨(Nat.gcdA m n : GaussianInt), (Nat.gcdB m n : GaussianInt), ?_⟩
  have hcast : ((1 : ℤ) : GaussianInt) =
      ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n : ℤ) := by
    exact_mod_cast hbez
  push_cast at hcast
  linear_combination -hcast

private lemma isCoprime_of_dvd {a b c d : GaussianInt}
    (h : IsCoprime a b) (hc : c ∣ a) (hd : d ∣ b) : IsCoprime c d := by
  rcases h with ⟨x, y, hxy⟩
  rcases hc with ⟨u, rfl⟩
  rcases hd with ⟨v, rfl⟩
  exact ⟨x * u, y * v, by linear_combination hxy⟩

private lemma isCoprime_of_coprime_giNorm {a b : GaussianInt}
    (h : Nat.Coprime (giNorm a) (giNorm b)) : IsCoprime a b := by
  have hmn : IsCoprime (giNorm a : GaussianInt) (giNorm b : GaussianInt) := isCoprime_natCast h
  have ha : a ∣ (giNorm a : GaussianInt) := ⟨star a, (gi_mul_star a).symm⟩
  have hb : b ∣ (giNorm b : GaussianInt) := ⟨star b, (gi_mul_star b).symm⟩
  exact isCoprime_of_dvd hmn ha hb

private lemma card_Q1Set_mul {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : Nat.Coprime m n) :
    (Q1Set (m * n)).card = (Q1Set m).card * (Q1Set n).card := by
  rw [← Finset.card_product]
  symm
  refine Finset.card_bij (fun p _ => canon (p.1 * p.2)) ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hu, hv⟩
    have hum := (mem_Q1Set_iff.mp hu).1
    have hvn := (mem_Q1Set_iff.mp hv).1
    have huv0 : p.1 * p.2 ≠ 0 := by
      intro h0
      have := giNorm_mul p.1 p.2
      rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hum, hvn] at this
      nlinarith
    exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, giNorm_mul, hum, hvn], canon_inQ1 huv0⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    rcases Finset.mem_product.mp hp₁ with ⟨hu₁, hv₁⟩
    rcases Finset.mem_product.mp hp₂ with ⟨hu₂, hv₂⟩
    have hum₁ := (mem_Q1Set_iff.mp hu₁).1
    have hvn₁ := (mem_Q1Set_iff.mp hv₁).1
    have hum₂ := (mem_Q1Set_iff.mp hu₂).1
    have hvn₂ := (mem_Q1Set_iff.mp hv₂).1
    have hne₁ : p₁.1 * p₁.2 ≠ 0 := by
      intro h0
      have := giNorm_mul p₁.1 p₁.2
      rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hum₁, hvn₁] at this
      nlinarith
    have hne₂ : p₂.1 * p₂.2 ≠ 0 := by
      intro h0
      have := giNorm_mul p₂.1 p₂.2
      rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hum₂, hvn₂] at this
      nlinarith
    have hass : Associated (p₁.1 * p₁.2) (p₂.1 * p₂.2) :=
      (canon_eq_iff_associated hne₁ hne₂).mp heq
    have hdvd1 : p₁.1 ∣ p₂.1 * p₂.2 := (dvd_mul_right p₁.1 p₁.2).trans hass.dvd
    have hdvd2 : p₂.1 ∣ p₁.1 * p₁.2 := (dvd_mul_right p₂.1 p₂.2).trans hass.symm.dvd
    have hcop12 : IsCoprime p₁.1 p₂.2 := isCoprime_of_coprime_giNorm (by rwa [hum₁, hvn₂])
    have hcop21 : IsCoprime p₂.1 p₁.2 := isCoprime_of_coprime_giNorm (by rwa [hum₂, hvn₁])
    have hu_ass : Associated p₁.1 p₂.1 :=
      associated_of_dvd_dvd (hcop12.dvd_of_dvd_mul_right hdvd1) (hcop21.dvd_of_dvd_mul_right hdvd2)
    have hu_eq : p₁.1 = p₂.1 :=
      eq_of_associated_inQ1 (mem_Q1Set_iff.mp hu₁).2 (mem_Q1Set_iff.mp hu₂).2 hu_ass
    have hv_dvd1 : p₁.2 ∣ p₂.2 := by
      have h1 : p₁.2 ∣ p₂.1 * p₂.2 := (dvd_mul_left p₁.2 p₁.1).trans hass.dvd
      exact hcop21.symm.dvd_of_dvd_mul_left h1
    have hv_dvd2 : p₂.2 ∣ p₁.2 := by
      have h2 : p₂.2 ∣ p₁.1 * p₁.2 := (dvd_mul_left p₂.2 p₂.1).trans hass.symm.dvd
      exact hcop12.symm.dvd_of_dvd_mul_left h2
    have hv_eq : p₁.2 = p₂.2 :=
      eq_of_associated_inQ1 (mem_Q1Set_iff.mp hv₁).2 (mem_Q1Set_iff.mp hv₂).2
        (associated_of_dvd_dvd hv_dvd1 hv_dvd2)
    exact Prod.ext hu_eq hv_eq
  · intro w hw
    have hwn := (mem_Q1Set_iff.mp hw).1
    have hwq := (mem_Q1Set_iff.mp hw).2
    have hw0 : w ≠ 0 := by
      intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hwn; nlinarith
    have hw_dvd_mn : w ∣ (m : GaussianInt) * (n : GaussianInt) := by
      refine ⟨star w, ?_⟩
      rw [gi_mul_star, hwn, Nat.cast_mul]
    let g₁ : GaussianInt := EuclideanDomain.gcd w (m : GaussianInt)
    let g₂ : GaussianInt := EuclideanDomain.gcd w (n : GaussianInt)
    have hg1_w : g₁ ∣ w := EuclideanDomain.gcd_dvd_left w (m : GaussianInt)
    have hg1_m : g₁ ∣ (m : GaussianInt) := EuclideanDomain.gcd_dvd_right w (m : GaussianInt)
    have hg2_w : g₂ ∣ w := EuclideanDomain.gcd_dvd_left w (n : GaussianInt)
    have hg2_n : g₂ ∣ (n : GaussianInt) := EuclideanDomain.gcd_dvd_right w (n : GaussianInt)
    have hcop_g : IsCoprime g₁ g₂ :=
      isCoprime_of_dvd (isCoprime_natCast hmn) hg1_m hg2_n
    have hg12_dvd_w : g₁ * g₂ ∣ w := hcop_g.mul_dvd hg1_w hg2_w
    have hw_dvd_g12 : w ∣ g₁ * g₂ := by
      have h1 := EuclideanDomain.gcd_eq_gcd_ab w (m : GaussianInt)
      have h2 := EuclideanDomain.gcd_eq_gcd_ab w (n : GaussianInt)
      have hexp : g₁ * g₂ =
          w * (w * EuclideanDomain.gcdA w m * EuclideanDomain.gcdA w n +
               (m : GaussianInt) * EuclideanDomain.gcdB w m * EuclideanDomain.gcdA w n +
               (n : GaussianInt) * EuclideanDomain.gcdB w n * EuclideanDomain.gcdA w m) +
          ((m : GaussianInt) * (n : GaussianInt)) *
            (EuclideanDomain.gcdB w m * EuclideanDomain.gcdB w n) := by
        change EuclideanDomain.gcd w m * EuclideanDomain.gcd w n = _
        rw [h1, h2]
        ring
      rw [hexp]
      exact dvd_add (dvd_mul_right w _) (dvd_mul_of_dvd_left hw_dvd_mn _)
    have hass_w : Associated (g₁ * g₂) w := associated_of_dvd_dvd hg12_dvd_w hw_dvd_g12
    have hprod_norm : giNorm g₁ * giNorm g₂ = m * n := by
      rw [← giNorm_mul, giNorm_eq_of_associated hass_w, hwn]
    have hg1_dvd_m2 : giNorm g₁ ∣ m ^ 2 := by
      simpa [giNorm_natCast] using giNorm_dvd_of_dvd hg1_m
    have hg2_dvd_n2 : giNorm g₂ ∣ n ^ 2 := by
      simpa [giNorm_natCast] using giNorm_dvd_of_dvd hg2_n
    have hcop_g1_n : Nat.Coprime (giNorm g₁) n :=
      ((hmn.pow_left 2).coprime_dvd_left hg1_dvd_m2)
    have hcop_g2_m : Nat.Coprime (giNorm g₂) m :=
      ((hmn.symm.pow_left 2).coprime_dvd_left hg2_dvd_n2)
    have hg1_eq : giNorm g₁ = m := by
      have hd1 : giNorm g₁ ∣ m := hcop_g1_n.dvd_of_dvd_mul_right ⟨giNorm g₂, hprod_norm.symm⟩
      have hd2 : m ∣ giNorm g₁ := hcop_g2_m.symm.dvd_of_dvd_mul_right ⟨n, by linarith⟩
      exact Nat.dvd_antisymm hd1 hd2
    have hg2_eq : giNorm g₂ = n := by
      rw [hg1_eq] at hprod_norm
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) hprod_norm
    have hg1_ne : g₁ ≠ 0 := by
      intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hg1_eq; omega
    have hg2_ne : g₂ ≠ 0 := by
      intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hg2_eq; omega
    refine ⟨(canon g₁, canon g₂), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, hg1_eq], canon_inQ1 hg1_ne⟩
    · exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, hg2_eq], canon_inQ1 hg2_ne⟩
    · have hc_ass : Associated (canon g₁ * canon g₂) w :=
        ((canon_associated g₁).symm.mul_mul (canon_associated g₂).symm).trans hass_w
      have hc_ne : canon g₁ * canon g₂ ≠ 0 := by
        intro h0
        have := giNorm_eq_of_associated hc_ass
        rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hwn] at this
        nlinarith
      rw [← canon_eq_self hwq]
      exact (canon_eq_iff_associated hc_ne hw0).mpr hc_ass

/- ### Prime power cases for `(Q1Set (p ^ k)).card` -/

private lemma gi_prime_of_norm_prime {π : GaussianInt} {p : ℕ} (hp : p.Prime)
    (hπ : giNorm π = p) : Prime π := by
  have hπ0 : π ≠ 0 := by
    intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hπ; exact hp.ne_zero hπ.symm
  have hnu : ¬ IsUnit π := by
    rw [← giNorm_eq_one_iff, hπ]; exact hp.ne_one
  refine ⟨hπ0, hnu, fun x y hxy => ?_⟩
  by_cases hx : π ∣ x
  · exact Or.inl hx
  · right
    let g := EuclideanDomain.gcd π x
    have hgπ : g ∣ π := EuclideanDomain.gcd_dvd_left π x
    have hgx : g ∣ x := EuclideanDomain.gcd_dvd_right π x
    have hgdvd : giNorm g ∣ p := by rw [← hπ]; exact giNorm_dvd_of_dvd hgπ
    rcases hp.eq_one_or_self_of_dvd _ hgdvd with hg1 | hgp
    · rcases (giNorm_eq_one_iff g).mp hg1 with ⟨u, hu⟩
      have hab := EuclideanDomain.gcd_eq_gcd_ab π x
      change g = π * EuclideanDomain.gcdA π x + x * EuclideanDomain.gcdB π x at hab
      have hy : y = π * (EuclideanDomain.gcdA π x * (u⁻¹ : GaussianIntˣ) * y) +
          (x * y) * (EuclideanDomain.gcdB π x * (u⁻¹ : GaussianIntˣ)) := by
        have h1 : (1 : GaussianInt) =
            π * (EuclideanDomain.gcdA π x * (u⁻¹ : GaussianIntˣ)) +
            x * (EuclideanDomain.gcdB π x * (u⁻¹ : GaussianIntˣ)) := by
          calc
            (1 : GaussianInt) = (u : GaussianInt) * (u⁻¹ : GaussianIntˣ) := by simp
            _ = g * (u⁻¹ : GaussianIntˣ) := by rw [hu]
            _ = (π * EuclideanDomain.gcdA π x + x * EuclideanDomain.gcdB π x) *
                  (u⁻¹ : GaussianIntˣ) := by rw [hab]
            _ = _ := by ring
        calc
          y = 1 * y := (one_mul y).symm
          _ = (π * (EuclideanDomain.gcdA π x * (u⁻¹ : GaussianIntˣ)) +
                x * (EuclideanDomain.gcdB π x * (u⁻¹ : GaussianIntˣ))) * y := by rw [← h1]
          _ = _ := by ring
      rw [hy]
      exact dvd_add (dvd_mul_right π _) (dvd_mul_of_dvd_left hxy _)
    · exfalso
      rcases hgπ with ⟨c, hc⟩
      have hc1 : giNorm c = 1 := by
        have hmul := giNorm_mul g c
        rw [← hc, hπ, hgp] at hmul
        exact Nat.eq_of_mul_eq_mul_left hp.pos (by linarith)
      rcases (giNorm_eq_one_iff c).mp hc1 with ⟨u, hu⟩
      have hπg : π ∣ g := ⟨(u⁻¹ : GaussianIntˣ), by rw [hc, ← hu]; simp⟩
      exact hx (hπg.trans hgx)

private lemma card_Q1Set_two_pow (k : ℕ) : (Q1Set (2 ^ k)).card = 1 := by
  let π : GaussianInt := ⟨1, 1⟩
  have hπ_norm : giNorm π = 2 := by decide
  have hall : ∀ m : ℕ, ∀ z : GaussianInt, giNorm z = 2 ^ m → Associated z (π ^ m) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      rw [pow_zero, giNorm_eq_one_iff] at hz
      rcases hz with ⟨u, hu⟩
      exact ⟨u⁻¹, by rw [pow_zero, ← hu]; simp⟩
    | succ m ih =>
      intro z hz
      have h2dvd : 2 ∣ z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
        rw [← giNorm_eq, hz, pow_succ]
        exact dvd_mul_left 2 _
      have hpar : (z.re + z.im) % 2 = 0 ∧ (z.im - z.re) % 2 = 0 := by
        have h2int : (2 : ℤ) ∣ z.re ^ 2 + z.im ^ 2 := by
          have : (z.re.natAbs ^ 2 + z.im.natAbs ^ 2 : ℤ) = z.re ^ 2 + z.im ^ 2 := by
            simp
          rw [← this]
          exact_mod_cast h2dvd
        have hsq_mod : ∀ a : ℤ, a ^ 2 % 2 = a % 2 := by
          intro a
          rcases Int.emod_two_eq_zero_or_one a with h0 | h1
          · rw [sq, Int.mul_emod, h0]; norm_num
          · rw [sq, Int.mul_emod, h1]; norm_num
        have h1 : (z.re ^ 2 + z.im ^ 2) % 2 = 0 := Int.emod_eq_zero_of_dvd h2int
        rw [Int.add_emod, hsq_mod, hsq_mod] at h1
        omega
      let w : GaussianInt := ⟨(z.re + z.im) / 2, (z.im - z.re) / 2⟩
      have hzw : z = π * w := by
        ext <;> simp [π, w] <;> omega
      have hwn : giNorm w = 2 ^ m := by
        have hmul := giNorm_mul π w
        rw [← hzw, hz, hπ_norm, pow_succ] at hmul
        omega
      have hass := ih w hwn
      rw [hzw, pow_succ']
      exact (Associated.refl π).mul_mul hass
  have hπk0 : π ^ k ≠ 0 := by
    intro h0
    have := giNorm_pow π k
    rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hπ_norm] at this
    exact (pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0)) this.symm
  have hset : Q1Set (2 ^ k) = {canon (π ^ k)} := by
    ext z
    simp only [mem_Q1Set_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hzn, hzq⟩
      have hass : Associated z (canon (π ^ k)) :=
        (hall k z hzn).trans (canon_associated (π ^ k))
      exact eq_of_associated_inQ1 hzq (canon_inQ1 hπk0) hass
    · rintro rfl
      exact ⟨by rw [giNorm_canon, giNorm_pow, hπ_norm], canon_inQ1 hπk0⟩
  rw [hset, Finset.card_singleton]

private lemma card_Q1Set_mod4_three {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (k : ℕ) :
    ((Q1Set (p ^ k)).card : ℤ) = if Even k then 1 else 0 := by
  have hdvd_both : ∀ z : GaussianInt, p ∣ giNorm z → (p : GaussianInt) ∣ z := by
    intro z hz
    have hmod : ((z.re : ZMod p) ^ 2 + (z.im : ZMod p) ^ 2) = 0 := by
      have h2 : (p : ℤ) ∣ z.re ^ 2 + z.im ^ 2 := by
        have : (z.re.natAbs ^ 2 + z.im.natAbs ^ 2 : ℤ) = z.re ^ 2 + z.im ^ 2 := by
          simp
        rw [← this]
        rw [giNorm_eq] at hz
        exact_mod_cast hz
      rcases h2 with ⟨c, hc⟩
      have hcast : (((z.re ^ 2 + z.im ^ 2 : ℤ) : ZMod p)) = ((p : ℤ) * c : ℤ) := by
        rw [hc]
      push_cast at hcast
      simpa using hcast
    have : Fact p.Prime := ⟨hp⟩
    have hre0 : (z.re : ZMod p) = 0 := by
      by_contra hne
      have hsq : IsSquare (-1 : ZMod p) := by
        refine ⟨(z.im : ZMod p) * (z.re : ZMod p)⁻¹, ?_⟩
        have h1 : (z.im : ZMod p) ^ 2 = -(z.re : ZMod p) ^ 2 := eq_neg_of_add_eq_zero_right hmod
        calc
          (-1 : ZMod p) = -((z.re : ZMod p) ^ 2 * ((z.re : ZMod p)⁻¹) ^ 2) := by
            rw [← mul_pow, mul_inv_cancel₀ hne, one_pow]
          _ = (-(z.re : ZMod p) ^ 2) * ((z.re : ZMod p)⁻¹) ^ 2 := by ring
          _ = (z.im : ZMod p) ^ 2 * ((z.re : ZMod p)⁻¹) ^ 2 := by rw [← h1]
          _ = ((z.im : ZMod p) * (z.re : ZMod p)⁻¹) * ((z.im : ZMod p) * (z.re : ZMod p)⁻¹) := by
            ring
      have hne3 : p % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
      exact hne3 hp3
    have him0 : (z.im : ZMod p) = 0 := by
      rw [hre0, zero_pow (by norm_num), zero_add] at hmod
      exact eq_zero_of_pow_eq_zero hmod
    have hdre : (p : ℤ) ∣ z.re := (ZMod.intCast_zmod_eq_zero_iff_dvd z.re p).mp hre0
    have hdim : (p : ℤ) ∣ z.im := (ZMod.intCast_zmod_eq_zero_iff_dvd z.im p).mp him0
    rcases hdre with ⟨a, ha⟩
    rcases hdim with ⟨b, hb⟩
    refine ⟨⟨a, b⟩, ?_⟩
    ext <;> simp [ha, hb]
  have hstep : ∀ m : ℕ, (Q1Set (p ^ (m + 2))).card = (Q1Set (p ^ m)).card := by
    intro m
    symm
    refine Finset.card_bij (fun w _ => (p : GaussianInt) * w) ?_ ?_ ?_
    · intro w hw
      rcases mem_Q1Set_iff.mp hw with ⟨hwn, hre, him⟩
      refine mem_Q1Set_iff.mpr ⟨?_, ?_, ?_⟩
      · rw [giNorm_mul, giNorm_natCast, hwn]; ring
      · simp
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
        nlinarith
      · simp
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
        nlinarith
    · intro w₁ _ w₂ _ heq
      have hp0 : (p : GaussianInt) ≠ 0 := by exact_mod_cast hp.ne_zero
      exact mul_left_cancel₀ hp0 heq
    · intro z hz
      rcases mem_Q1Set_iff.mp hz with ⟨hzn, hre, him⟩
      have hpdvd : p ∣ giNorm z := by
        rw [hzn, pow_add]; exact dvd_mul_of_dvd_right (dvd_pow_self p (by norm_num)) _
      rcases hdvd_both z hpdvd with ⟨w, hw⟩
      refine ⟨w, mem_Q1Set_iff.mpr ⟨?_, ?_, ?_⟩, hw.symm⟩
      · have hmul := giNorm_mul (p : GaussianInt) w
        rw [← hw, hzn, giNorm_natCast, pow_add] at hmul
        have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
        exact Nat.eq_of_mul_eq_mul_left hp2_pos (by linarith)
      · have hre' : z.re = (p : ℤ) * w.re := by rw [hw]; simp
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
        nlinarith
      · have him' : z.im = (p : ℤ) * w.im := by rw [hw]; simp
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
        nlinarith
  have hbase0 : (Q1Set 1).card = 1 := by
    have hset : Q1Set 1 = {1} := by
      ext z
      simp only [mem_Q1Set_iff, Finset.mem_singleton]
      constructor
      · rintro ⟨hz1, hzq⟩
        have hass : Associated z 1 := by
          rcases (giNorm_eq_one_iff z).mp hz1 with ⟨u, hu⟩
          exact ⟨u⁻¹, by rw [← hu]; simp⟩
        exact eq_of_associated_inQ1 hzq ⟨by decide, by decide⟩ hass
      · rintro rfl
        exact ⟨by decide, ⟨by decide, by decide⟩⟩
    rw [hset, Finset.card_singleton]
  have hbase1 : (Q1Set p).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro z hz
    have hzn : giNorm z = p := (mem_Q1Set_iff.mp hz).1
    rcases hdvd_both z (by rw [hzn]) with ⟨w, hw⟩
    have hmul := giNorm_mul (p : GaussianInt) w
    rw [← hw, hzn, giNorm_natCast] at hmul
    have hp2 : p ^ 2 ≤ p := by
      have hw1 : 1 ≤ giNorm w := by
        by_contra h0
        have hw0 : giNorm w = 0 := by omega
        rw [hw0, mul_zero] at hmul
        exact hp.ne_zero hmul
      nlinarith [hp.two_le]
    nlinarith [hp.two_le]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [hbase0]
    | 1 => simp [hbase1]
    | m + 2 =>
      rw [hstep m, ih m (by omega)]
      have hev : Even (m + 2) ↔ Even m := by
        constructor
        · rintro ⟨r, hr⟩; exact ⟨r - 1, by omega⟩
        · rintro ⟨r, hr⟩; exact ⟨r + 1, by omega⟩
      simp [hev]

private lemma card_Q1Set_mod4_one {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (k : ℕ) :
    (Q1Set (p ^ k)).card = k + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.Prime.sq_add_sq (p := p) (by omega : p % 4 ≠ 3) with ⟨a, b, hab⟩
  let π : GaussianInt := ⟨(a : ℤ), (b : ℤ)⟩
  let π' : GaussianInt := star π
  have hπ_norm : giNorm π = p := by
    simp only [giNorm_eq, π, Int.natAbs_natCast]
    exact hab
  have hπ'_norm : giNorm π' = p := by rw [giNorm_star, hπ_norm]
  have hπ_prime : Prime π := gi_prime_of_norm_prime hp hπ_norm
  have hπ'_prime : Prime π' := gi_prime_of_norm_prime hp hπ'_norm
  have hmul_p : π * π' = (p : GaussianInt) := by
    simpa [π', hπ_norm] using gi_mul_star π
  have hnot_ass : ¬ Associated π π' := by
    intro hass
    have ha_ne0 : a ≠ 0 := by
      intro h0; subst h0
      have hb2 : b ^ 2 = p := by simpa using hab
      have hb_pos : 0 < b := by nlinarith [hp.two_le]
      rcases (by omega : b = 1 ∨ 2 ≤ b) with rfl | hb2'
      · nlinarith [hp.two_le]
      · have hdvd : b ∣ p := ⟨b, by linarith⟩
        rcases hp.eq_one_or_self_of_dvd b hdvd with h1 | hbp
        · omega
        · nlinarith
    have hb_ne0 : b ≠ 0 := by
      intro h0; subst h0
      have ha2 : a ^ 2 = p := by simpa using hab
      have ha_pos : 0 < a := by nlinarith [hp.two_le]
      rcases (by omega : a = 1 ∨ 2 ≤ a) with rfl | ha2'
      · nlinarith [hp.two_le]
      · have hdvd : a ∣ p := ⟨a, by linarith⟩
        rcases hp.eq_one_or_self_of_dvd a hdvd with h1 | hap
        · omega
        · nlinarith
    have hab_ne : a ≠ b := by
      intro heq; subst heq
      have h2 : 2 ∣ p := ⟨a ^ 2, by linarith⟩
      rcases hp.eq_one_or_self_of_dvd 2 h2 with h1 | h2p
      · omega
      · omega
    rcases hass with ⟨u, hu⟩
    have hmem := (mem_giUnits_iff u).mpr u.isUnit
    simp only [giUnits, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1 | h1 | h1
    · rw [h1, mul_one] at hu
      have := congr_arg Zsqrtd.im hu
      simp [π, π'] at this; omega
    · rw [h1] at hu
      have := congr_arg Zsqrtd.re hu
      simp [π, π'] at this; omega
    · rw [h1] at hu
      have := congr_arg Zsqrtd.re hu
      simp [π, π', giI] at this; omega
    · rw [h1] at hu
      have := congr_arg Zsqrtd.re hu
      simp [π, π', giI] at this; omega
  have hall : ∀ m : ℕ, ∀ z : GaussianInt, giNorm z = p ^ m →
      ∃ j ≤ m, Associated z (π ^ j * π' ^ (m - j)) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      rw [pow_zero, giNorm_eq_one_iff] at hz
      rcases hz with ⟨u, hu⟩
      exact ⟨0, le_refl 0, ⟨u⁻¹, by simp [← hu]⟩⟩
    | succ m ih =>
      intro z hz
      have hprod : z * star z = (p ^ (m + 1) : GaussianInt) := by
        simpa [hz] using gi_mul_star z
      have hπ_dvd_prod : π ∣ z * star z := by
        refine ⟨π' * (p : GaussianInt) ^ m, ?_⟩
        calc
          z * star z = (p : GaussianInt) * (p : GaussianInt) ^ m := by
            rw [hprod, pow_succ']
          _ = (π * π') * (p : GaussianInt) ^ m := by rw [hmul_p]
          _ = π * (π' * (p : GaussianInt) ^ m) := by ring
      rcases hπ_prime.dvd_or_dvd hπ_dvd_prod with hπz | hπsz
      · rcases hπz with ⟨w, hw⟩
        have hwn : giNorm w = p ^ m := by
          have hmul := giNorm_mul π w
          rw [← hw, hz, hπ_norm, pow_succ'] at hmul
          exact Nat.eq_of_mul_eq_mul_left hp.pos hmul.symm
        rcases ih w hwn with ⟨j, hjm, hass⟩
        refine ⟨j + 1, by omega, ?_⟩
        have hsub : m + 1 - (j + 1) = m - j := by omega
        rw [hsub, hw, pow_succ', mul_assoc]
        exact (Associated.refl π).mul_mul hass
      · rcases hπsz with ⟨w, hw⟩
        have hπ'z : z = π' * star w := by
          have := congr_arg star hw
          simpa [π', star_mul, mul_comm] using this
        have hwn : giNorm (star w) = p ^ m := by
          have hmul := giNorm_mul π' (star w)
          rw [← hπ'z, hz, hπ'_norm, pow_succ'] at hmul
          exact Nat.eq_of_mul_eq_mul_left hp.pos hmul.symm
        rcases ih (star w) hwn with ⟨j, hjm, hass⟩
        refine ⟨j, by omega, ?_⟩
        have hsub : m + 1 - j = (m - j) + 1 := by omega
        rw [hsub, hπ'z, pow_succ', mul_left_comm]
        exact (Associated.refl π').mul_mul hass
  rw [← Finset.card_range (k + 1)]
  symm
  refine Finset.card_bij (fun j _ => canon (π ^ j * π' ^ (k - j))) ?_ ?_ ?_
  · intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hnorm : giNorm (π ^ j * π' ^ (k - j)) = p ^ k := by
      rw [giNorm_mul, giNorm_pow, giNorm_pow, hπ_norm, hπ'_norm, ← pow_add,
        Nat.add_sub_of_le hjk]
    have hne : π ^ j * π' ^ (k - j) ≠ 0 := by
      intro h0
      rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hnorm
      exact pow_ne_zero k hp.ne_zero hnorm.symm
    exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, hnorm], canon_inQ1 hne⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    have hjk₁ : j₁ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₁)
    have hjk₂ : j₂ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₂)
    have hne₁ : π ^ j₁ * π' ^ (k - j₁) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hπ_prime.ne_zero) (pow_ne_zero _ hπ'_prime.ne_zero)
    have hne₂ : π ^ j₂ * π' ^ (k - j₂) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hπ_prime.ne_zero) (pow_ne_zero _ hπ'_prime.ne_zero)
    have hass := (canon_eq_iff_associated hne₁ hne₂).mp heq
    by_contra hne
    have hcontra : ∀ a b : ℕ, a < b → b ≤ k →
        Associated (π ^ a * π' ^ (k - a)) (π ^ b * π' ^ (k - b)) → False := by
      intro a b hab hbk hba
      have hba_dvd : π ^ b * π' ^ (k - b) ∣ π ^ a * π' ^ (k - a) := hba.symm.dvd
      have hre1 : π ^ b * π' ^ (k - b) = (π ^ a * π' ^ (k - b)) * π ^ (b - a) := by
        rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le (le_of_lt hab)]
      have hre2 : π ^ a * π' ^ (k - a) = (π ^ a * π' ^ (k - b)) * π' ^ (b - a) := by
        rw [mul_assoc, ← pow_add, show (k - b) + (b - a) = k - a by omega]
      rw [hre1, hre2] at hba_dvd
      have hc0 : π ^ a * π' ^ (k - b) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hπ_prime.ne_zero) (pow_ne_zero _ hπ'_prime.ne_zero)
      have hpow_dvd : π ^ (b - a) ∣ π' ^ (b - a) := (mul_dvd_mul_iff_left hc0).mp hba_dvd
      have hπ_dvd_pow : π ∣ π' ^ (b - a) :=
        (dvd_pow_self π (by omega : b - a ≠ 0)).trans hpow_dvd
      have hπ_dvd_π' : π ∣ π' := hπ_prime.dvd_of_dvd_pow hπ_dvd_pow
      rcases hπ_dvd_π' with ⟨c, hc⟩
      have hc1 : giNorm c = 1 := by
        have hmul := giNorm_mul π c
        rw [← hc, hπ'_norm, hπ_norm] at hmul
        exact Nat.eq_of_mul_eq_mul_left hp.pos (by linarith)
      rcases (giNorm_eq_one_iff c).mp hc1 with ⟨u, hu⟩
      exact hnot_ass ⟨u, by rw [hu, ← hc]⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hcontra j₁ j₂ hlt hjk₂ hass
    · exact hcontra j₂ j₁ hgt hjk₁ hass.symm
  · intro z hz
    rcases mem_Q1Set_iff.mp hz with ⟨hzn, hzq⟩
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hzn
      exact pow_ne_zero k hp.ne_zero hzn.symm
    rcases hall k z hzn with ⟨j, hjk, hass⟩
    refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    have hne : π ^ j * π' ^ (k - j) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hπ_prime.ne_zero) (pow_ne_zero _ hπ'_prime.ne_zero)
    rw [← canon_eq_self hzq]
    exact (canon_eq_iff_associated hne hz0).mpr hass.symm

private lemma card_Q1Set_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((Q1Set (p ^ k)).card : ℤ) = divSumChi4 (p ^ k) := by
  rw [divSumChi4_prime_pow hp k]
  by_cases hp2 : p = 2
  · subst hp2
    rw [card_Q1Set_two_pow k]
    have hchi2 : chi4 2 = 0 := by decide
    simp only [hchi2]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj; simp [zero_pow hj]
    · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0
  · have hodd : p % 2 = 1 := by
      have hndvd : ¬ (2 ∣ p) := fun h => hp2 ((hp.eq_one_or_self_of_dvd 2 h).resolve_left (by decide)).symm
      omega
    have hmod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hmod4 with hp1 | hp3
    · rw [card_Q1Set_mod4_one hp hp1 k]
      have hchi : chi4 p = 1 := by simp [chi4, hp1]
      simp [hchi]
    · rw [card_Q1Set_mod4_three hp hp3 k]
      have hchi : chi4 p = -1 := by simp [chi4, hp3]
      simp only [hchi]
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ← ih]
        by_cases hev : Even k
        · have hodd' : ¬ Even (k + 1) := by
            rcases hev with ⟨r, hr⟩; rintro ⟨s, hs⟩; omega
          have hpow : (-1 : ℤ) ^ (k + 1) = -1 := by
            rcases hev with ⟨r, hr⟩
            rw [hr, ← two_mul, pow_succ, pow_mul]; norm_num
          simp [hev, hodd', hpow]
        · have hev' : Even (k + 1) := by
            have : k % 2 = 1 := by
              by_contra h
              exact hev ⟨k / 2, by omega⟩
            exact ⟨k / 2 + 1, by omega⟩
          have hpow : (-1 : ℤ) ^ (k + 1) = 1 := by
            rcases hev' with ⟨r, hr⟩
            rw [hr, ← two_mul, pow_mul]; norm_num
          simp [hev, hev', hpow]

private lemma card_Q1Set_eq_divSumChi4 {n : ℕ} (hn : 1 ≤ n) :
    ((Q1Set n).card : ℤ) = divSumChi4 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn1 : n = 1
    · subst hn1
      rw [divSumChi4_one]
      have hset : Q1Set 1 = {1} := by
        ext z
        simp only [mem_Q1Set_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨hz1, hzq⟩
          rcases (giNorm_eq_one_iff z).mp hz1 with ⟨u, hu⟩
          exact eq_of_associated_inQ1 hzq ⟨by decide, by decide⟩ ⟨u⁻¹, by rw [← hu]; simp⟩
        · rintro rfl
          exact ⟨by decide, ⟨by decide, by decide⟩⟩
      simp [hset]
    · let p := n.minFac
      have hp : p.Prime := Nat.minFac_prime hn1
      have hpn : p ∣ n := Nat.minFac_dvd n
      let a := p ^ n.factorization p
      let b := n / a
      have hadvd : a ∣ n := Nat.ordProj_dvd n p
      have hmul : a * b = n := Nat.mul_div_cancel' hadvd
      have hcop : Nat.Coprime a b := (Nat.coprime_ordCompl hp (by omega : n ≠ 0)).pow_left _
      have ha_ge : 1 ≤ a := pow_pos hp.pos _
      have hb_ge : 1 ≤ b := Nat.pos_of_ne_zero fun hb0 => by
        rw [hb0, mul_zero] at hmul; omega
      have ha_gt1 : 1 < a := by
        have hfac : 1 ≤ n.factorization p := by
          have hne : n.factorization p ≠ 0 :=
            (hp.dvd_iff_one_le_factorization (by omega : n ≠ 0)).mp hpn |> Nat.pos_iff_ne_zero.mp
          omega
        exact one_lt_pow₀ hp.one_lt (by omega)
      have hb_lt : b < n := by nlinarith
      rw [← hmul, card_Q1Set_mul ha_ge hb_ge hcop, Nat.cast_mul, divSumChi4_mul hcop,
        card_Q1Set_prime_pow hp (n.factorization p), ih b hb_lt hb_ge]

private lemma card_giOfNorm_eq {n : ℕ} (hn : 1 ≤ n) :
    ((giOfNorm n).card : ℤ) = 4 * divSumChi4 n := by
  rw [card_giOfNorm_eq_four_mul hn, Nat.cast_mul, Nat.cast_ofNat, card_Q1Set_eq_divSumChi4 hn]

/- ### Lattice-point sum and floor identity -/

private lemma card_ball_eq_sum_giOfNorm (M : ℕ) :
    ({ p : ℤ × ℤ | p.1.natAbs ^ 2 + p.2.natAbs ^ 2 ≤ M }).ncard =
      1 + ∑ n ∈ Finset.Icc 1 M, (giOfNorm n).card := by
  let B : Finset (ℤ × ℤ) :=
    (Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-(M : ℤ)) M).filter
      fun p => p.1.natAbs ^ 2 + p.2.natAbs ^ 2 ≤ M
  have hB_coe : (B : Set (ℤ × ℤ)) = { p : ℤ × ℤ | p.1.natAbs ^ 2 + p.2.natAbs ^ 2 ≤ M } := by
    ext p
    simp only [B, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_ofPred_eq]
    constructor
    · exact fun h => h.2
    · intro hle
      refine ⟨⟨?_, ?_⟩, hle⟩
      · have : p.1.natAbs ≤ p.1.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
        omega
      · have : p.2.natAbs ≤ p.2.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
        omega
  rw [← hB_coe, Set.ncard_coe_finset]
  have hfib := Finset.card_eq_sum_card_fiberwise
    (s := B) (t := Finset.range (M + 1))
    (f := fun p : ℤ × ℤ => p.1.natAbs ^ 2 + p.2.natAbs ^ 2)
    (fun p hp => Finset.mem_range.mpr (by
      have hle := (Finset.mem_filter.mp hp).2
      dsimp only
      omega))
  rw [hfib]
  have hfiber_card : ∀ n ≤ M,
      (B.filter fun p => p.1.natAbs ^ 2 + p.2.natAbs ^ 2 = n).card = (giOfNorm n).card := by
    intro n hn
    refine Finset.card_bij (fun p _ => (⟨p.1, p.2⟩ : GaussianInt)) ?_ ?_ ?_
    · intro p hp
      rw [mem_giOfNorm_iff, giNorm_eq]
      exact (Finset.mem_filter.mp hp).2
    · intro p₁ _ p₂ _ heq
      exact Prod.ext (congr_arg Zsqrtd.re heq) (congr_arg Zsqrtd.im heq)
    · intro z hz
      have hzn : z.re.natAbs ^ 2 + z.im.natAbs ^ 2 = n := by
        rw [← giNorm_eq]; exact mem_giOfNorm_iff.mp hz
      refine ⟨(z.re, z.im), Finset.mem_filter.mpr ⟨?_, hzn⟩, by ext <;> rfl⟩
      have hmem : (z.re, z.im) ∈ (B : Set (ℤ × ℤ)) := by
        rw [hB_coe]; exact le_of_eq_of_le hzn hn
      exact Finset.mem_coe.mp hmem
  have hsum_eq : ∑ n ∈ Finset.range (M + 1),
      (B.filter fun p => p.1.natAbs ^ 2 + p.2.natAbs ^ 2 = n).card =
      ∑ n ∈ Finset.range (M + 1), (giOfNorm n).card :=
    Finset.sum_congr rfl fun n hn => hfiber_card n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  rw [hsum_eq, Finset.sum_range_succ']
  have h0 : (giOfNorm 0).card = 1 := by
    have hset : giOfNorm 0 = {0} := by
      ext z
      simp only [mem_giOfNorm_iff, Finset.mem_singleton, giNorm_eq_zero_iff]
    rw [hset, Finset.card_singleton]
  rw [h0, add_comm]
  congr 1
  refine Finset.sum_bij (fun n _ => n + 1) ?_ ?_ ?_ ?_
  · intro n hn; simp only [Finset.mem_range] at hn; simp only [Finset.mem_Icc]; omega
  · intro _ _ _ _ h; omega
  · intro n hn; simp only [Finset.mem_Icc] at hn; exact ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro _ _; rfl

private lemma card_multiples_Icc (M d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Icc 1 M).filter (d ∣ ·)).card = M / d := by
  have hcard : (Finset.Icc 1 (M / d)).card = M / d := by simp
  rw [← hcard]
  symm
  refine Finset.card_bij (fun k _ => d * k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right d k⟩
    · nlinarith
    · exact (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hk.2 |> fun h => by linarith
  · intro k₁ _ k₂ _ heq
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < d) heq
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, k, rfl⟩
    simp only [Finset.mem_Icc] at hnIcc
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0, mul_zero] at hnIcc; omega
    have hk2 : k ≤ M / d := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by linarith)
    exact ⟨k, Finset.mem_Icc.mpr ⟨hk1, hk2⟩, rfl⟩

private lemma sum_divSumChi4_eq (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, divSumChi4 n =
      ∑ d ∈ Finset.Icc 1 M, ((M / d : ℕ) : ℤ) * chi4 d := by
  have h1 : ∀ n ∈ Finset.Icc 1 M,
      divSumChi4 n = ∑ d ∈ Finset.Icc 1 M, if d ∣ n then chi4 d else 0 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [divSumChi4, ← Finset.sum_filter]
    congr 1
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdn, hn0⟩
      have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdn (by omega)
      have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdn
      exact ⟨⟨hdpos, by omega⟩, hdn⟩
    · rintro ⟨⟨_, _⟩, hdn⟩
      exact ⟨hdn, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    card_multiples_Icc M d (Finset.mem_Icc.mp hd).1]

private lemma sum_range_four_mul (f : ℕ → ℤ) (K : ℕ) :
    ∑ d ∈ Finset.range (4 * K), f d =
      ∑ i ∈ Finset.range K, (f (4 * i) + f (4 * i + 1) + f (4 * i + 2) + f (4 * i + 3)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih, mul_add, mul_one]
    rw [show 4 * K + 4 = (((4 * K + 1) + 1) + 1) + 1 by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have h2 : 4 * K + 1 + 1 = 4 * K + 2 := by omega
    have h3 : 4 * K + 1 + 1 + 1 = 4 * K + 3 := by omega
    rw [h2, h3]
    ring

private lemma floor_div_eq_nat_div {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (hd : 1 ≤ d) :
    ⌊x / (d : ℝ)⌋ = ((⌊x⌋₊ / d : ℕ) : ℤ) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hdiv_nonneg : 0 ≤ x / (d : ℝ) := div_nonneg hx hd_pos.le
  rw [← Int.natCast_floor_eq_floor hdiv_nonneg]
  congr 1
  apply le_antisymm
  · rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
    rw [Nat.le_floor_iff hx]
    have h1 : (⌊x / (d : ℝ)⌋₊ : ℝ) ≤ x / (d : ℝ) := Nat.floor_le hdiv_nonneg
    have h2 : (⌊x / (d : ℝ)⌋₊ : ℝ) * (d : ℝ) ≤ x := (le_div_iff₀ hd_pos).mp h1
    exact_mod_cast h2
  · rw [Nat.le_floor_iff hdiv_nonneg, le_div_iff₀ hd_pos]
    have h1 : (⌊x⌋₊ / d) * d ≤ ⌊x⌋₊ := Nat.div_mul_le_self ⌊x⌋₊ d
    have h2 : ((⌊x⌋₊ / d : ℕ) : ℝ) * (d : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    exact le_trans h2 (Nat.floor_le hx)

private lemma mem_closedBall_iff_sq_le {r : ℝ} (hr : 0 ≤ r) (a b : ℤ) :
    !₂[(a : ℝ), (b : ℝ)] ∈ Metric.closedBall (0 : ℝ²) r ↔
      a.natAbs ^ 2 + b.natAbs ^ 2 ≤ ⌊r ^ 2⌋₊ := by
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_le_iff]
  have hsq : ∀ t : ℤ, ((t.natAbs : ℕ) : ℝ) ^ 2 = (t : ℝ) ^ 2 := fun t => by
    rw [← Int.cast_natCast, ← Int.cast_pow, Int.natAbs_sq, Int.cast_pow]
  have hcast : ((a.natAbs ^ 2 + b.natAbs ^ 2 : ℕ) : ℝ) = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
    push_cast
    rw [hsq a, hsq b]
  rw [← hcast, Nat.le_floor_iff (sq_nonneg r)]
  exact ⟨fun h => h.2, fun h => ⟨hr, h⟩⟩

end GaussCircleFloorProof

open GaussCircleProblem GaussCircleFloorProof
open scoped EuclideanGeometry

theorem OMA.solution : type_of% @GaussCircleProblem.exact_form_floor := by
  intro r hr
  let M : ℕ := ⌊r ^ 2⌋₊
  have hN_set :
      { p : ℤ × ℤ | !₂[(p.1 : ℝ), (p.2 : ℝ)] ∈ Metric.closedBall (0 : ℝ²) r } =
      { p : ℤ × ℤ | p.1.natAbs ^ 2 + p.2.natAbs ^ 2 ≤ M } := by
    ext ⟨a, b⟩
    exact mem_closedBall_iff_sq_le hr a b
  have hN_eq : (N r : ℤ) = 1 + 4 * ∑ d ∈ Finset.Icc 1 M, ((M / d : ℕ) : ℤ) * chi4 d := by
    rw [N, hN_set, card_ball_eq_sum_giOfNorm M, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
    have hsum : ∑ n ∈ Finset.Icc 1 M, ((giOfNorm n).card : ℤ) =
        ∑ n ∈ Finset.Icc 1 M, 4 * divSumChi4 n :=
      Finset.sum_congr rfl fun n hn => card_giOfNorm_eq (Finset.mem_Icc.mp hn).1
    rw [hsum, ← Finset.mul_sum, sum_divSumChi4_eq M]
  rw [hN_eq]
  congr 2
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hterm : ∀ i : ℕ,
      ⌊r ^ 2 / (4 * (i : ℝ) + 1)⌋ - ⌊r ^ 2 / (4 * (i : ℝ) + 3)⌋ =
        ((M / (4 * i + 1) : ℕ) : ℤ) - ((M / (4 * i + 3) : ℕ) : ℤ) := by
    intro i
    have h1 := floor_div_eq_nat_div hr2 (d := 4 * i + 1) (by omega)
    have h3 := floor_div_eq_nat_div hr2 (d := 4 * i + 3) (by omega)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h1 h3
    rw [h1, h3]
  have htsum :
      ∑' (i : ℕ), (⌊r ^ 2 / (4 * (i : ℝ) + 1)⌋ - ⌊r ^ 2 / (4 * (i : ℝ) + 3)⌋) =
        ∑ i ∈ Finset.range (M + 1),
          (((M / (4 * i + 1) : ℕ) : ℤ) - ((M / (4 * i + 3) : ℕ) : ℤ)) := by
    rw [tsum_eq_sum (s := Finset.range (M + 1))]
    · exact Finset.sum_congr rfl fun i _ => hterm i
    · intro i hi
      simp only [Finset.mem_range, not_lt] at hi
      rw [hterm i]
      rw [Nat.div_eq_of_lt (by omega : M < 4 * i + 1),
          Nat.div_eq_of_lt (by omega : M < 4 * i + 3)]
      norm_num
  rw [htsum]
  let f : ℕ → ℤ := fun d => ((M / d : ℕ) : ℤ) * chi4 d
  have hrange : ∑ d ∈ Finset.Icc 1 M, f d = ∑ d ∈ Finset.range (4 * (M + 1)), f d := by
    refine Finset.sum_subset ?_ ?_
    · intro d hd
      simp only [Finset.mem_Icc] at hd
      exact Finset.mem_range.mpr (by omega)
    · intro d hd hnot
      simp only [Finset.mem_Icc] at hnot
      by_cases hd0 : d = 0
      · subst hd0; simp [f, chi4]
      · have hgt : M < d := by omega
        dsimp only [f]
        rw [Nat.div_eq_of_lt hgt]
        simp
  change ∑ d ∈ Finset.Icc 1 M, f d = _
  rw [hrange, sum_range_four_mul f (M + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h0 : chi4 (4 * i) = 0 := by simp [chi4]
  have h1 : chi4 (4 * i + 1) = 1 := by simp [chi4]
  have h2 : chi4 (4 * i + 2) = 0 := by simp [chi4]
  have h3 : chi4 (4 * i + 3) = -1 := by simp [chi4]
  simp only [f, h0, h1, h2, h3]
  ring
