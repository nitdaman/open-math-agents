import FormalConjectures.OEIS.«215926»

namespace OMA.R_OeisA215926_conjecture_2_R1

open OeisA215926

-- Exclude almost perfect numbers only in the interval that can interfere.
def H1 : Prop :=
  ∀ m k : ℕ, 1 ≤ m → k < 2 ^ m → nextPrimeTwoPow m + 1 ≤ 2 * k →
    (∑ d ∈ k.divisors, d) + 1 ≠ 2 * k

-- A power of two supplies a multiplier for odd primes in this range.
def H2 : Prop :=
  ∀ j q : ℕ, q.Prime → 2 < q → q < 2 * 2 ^ j →
    (2 ^ j * q).Perfect ∨ (2 ^ j * q).Abundant

private theorem nond {n : ℕ} (hn : 0 < n) :
    n.Perfect ∨ n.Abundant ↔ 2 * n ≤ ∑ d ∈ n.divisors, d := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hn, Nat.abundant_iff_sum_divisors]
  omega

private theorem liftNondef {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (hd : u ∣ v)
    (h : u.Perfect ∨ u.Abundant) : v.Perfect ∨ v.Abundant := by
  have hi : ∀ t : ℕ, 0 < t → (2 ≤ t.abundancyIndex ↔ t.Perfect ∨ t.Abundant) := by
    intro t ht
    rw [nond ht, Nat.abundancyIndex, le_div_iff₀ (by positivity)]
    norm_cast
  exact (hi v hv).mp (((hi u hu).mpr h).trans (Nat.abundancyIndex_le_of_dvd hv.ne' hd))

private theorem obstruction {k p : ℕ} (hp : p.Prime) (hlt : k < p)
    (hd : k.Deficient) (hprod : (k*p).Perfect ∨ (k*p).Abundant) :
    (∑ d ∈ k.divisors, d) + 1 = 2*k ∧ p+1 ≤ 2*k := by
  have hk := hd.pos
  have h := (nond (Nat.mul_pos hk hp.pos)).mp hprod
  rw [(Nat.coprime_of_lt_prime hk.ne' hlt hp).symm.sum_divisors_mul, hp.divisors] at h
  simp [Ne.symm hp.ne_one] at h
  have hlt' : (∑ d ∈ k.divisors, d) < 2*k := by
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
    unfold Nat.Deficient at hd
    omega
  have he : (∑ d ∈ k.divisors, d) + 1 = 2*k := by
    by_contra hn
    have hh : (∑ d ∈ k.divisors, d) + 2 ≤ 2*k := by omega
    nlinarith [Nat.mul_le_mul_right (1+p) hh]
  exact ⟨he, by nlinarith [congrArg (· * p) he]⟩

theorem main : H1 → H2 → type_of% @OeisA215926.conjecture_2 := by
  intro hgap hprime m hm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let x := 2 ^ (j+1)
  let p := nextPrimeTwoPow (j+1)
  have hx : 2 ≤ x := by dsimp [x]; rw [pow_succ]; have := Nat.two_pow_pos j; omega
  obtain ⟨r, hr, hrx, hru⟩ := Nat.exists_prime_lt_and_le_two_mul x (by omega)
  let S := {r : ℕ | x < r ∧ r.Prime}
  have hs : S.Nonempty := ⟨r, hrx, hr⟩
  have hp : x < p ∧ p.Prime := Nat.sInf_mem hs
  have hmin : ∀ q ∈ S, p ≤ q := fun q hq => Nat.sInf_le hq
  have hpr := hmin r ⟨hrx, hr⟩
  have hpo := hp.2.odd_of_ne_two (by omega)
  obtain ⟨t, ht⟩ := hpo
  have hpu : p < 2*x := by omega
  change IsLeast {n : ℕ | 2 ≤ n ∧ a n = x} p
  constructor
  · refine ⟨hp.2.two_le, IsLeast.csInf_eq ?_⟩
    refine ⟨⟨Nat.prime_two.deficient_pow, hprime _ p hp.2 (by omega) hpu⟩, ?_⟩
    intro k ⟨hk, hkp⟩
    by_contra! hsmall
    have H := obstruction hp.2 (by omega : k < p) hk hkp
    exact hgap _ _ hm hsmall H.2 H.1
  · intro n ⟨hn, ha⟩
    change a n = x at ha
    change p ≤ n
    by_contra! hnlt
    let q := n.minFac
    have hq : q.Prime := Nat.minFac_prime (by omega)
    have hd : q ∣ n := Nat.minFac_dvd n
    have hql : q ≤ n := Nat.le_of_dvd (by omega) hd
    have hqx : q ≤ x := by
      by_contra! h
      exact (by omega : ¬p ≤ q) (hmin q ⟨h, hq⟩)
    have bound (k : ℕ) (hk : k.Deficient) (hw : (k*n).Perfect ∨ (k*n).Abundant) : x ≤ k :=
      ha ▸ (Nat.sInf_le (s := {b : ℕ | b.Deficient ∧ ((b*n).Perfect ∨ (b*n).Abundant)}) (m := k) ⟨hk,hw⟩ : a n ≤ k)
    by_cases htwo : q = 2
    · have hw := liftNondef (u := 6) (v := 3*n) (by decide) (by omega)
          (show 3*2 ∣ 3*n from Nat.mul_dvd_mul_left 3 (htwo ▸ hd)) (Or.inl (by decide))
      have hb := bound 3 Nat.deficient_three hw
      have hx2 : x = 2 := by
        have hh := Nat.two_pow_pos j
        dsimp [x] at hb ⊢
        rw [pow_succ] at hb ⊢
        omega
      have hp3 := hmin 3 ⟨by omega, by decide⟩
      have hn2 : n = 2 := by omega
      subst n
      rw [a_2] at ha
      omega
    · have hodd := hq.odd_of_ne_two htwo
      obtain ⟨s, hs⟩ := hodd
      have hxj : x = 2^j * 2 := pow_succ ..
      have hw := hprime j q hq (by have := hq.two_le; omega) (by omega)
      have hnpos : 0 < n := by omega
      have hqpos := hq.pos
      have hb := bound (2^j) Nat.prime_two.deficient_pow
        (liftNondef (by positivity) (by positivity) (Nat.mul_dvd_mul_left _ hd) hw)
      have := Nat.two_pow_pos j
      omega

end OMA.R_OeisA215926_conjecture_2_R1
