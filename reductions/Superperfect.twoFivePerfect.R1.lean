import FormalConjectures.Wikipedia.Superperfectnumbers

/-! A prime power in the factorization of the intermediate divisor sum must supply a
factor of five. Its residue determines a divisibility constraint on its exponent. -/

namespace OMA.R_Superperfect_twoFivePerfect_R1

open ArithmeticFunction ArithmeticFunction.sigma

-- Strip the exact prime power p^e from the intermediate divisor sum.

def H1 : Prop := ∀ p e u : ℕ, p.Prime → p.Coprime u → 0 < u →
  (p : ZMod 5) = 1 → 5 ∣ e + 1 → σ 1 ((σ 1 (p ^ e) / 5) * σ 1 u) ≠ p ^ e * u

def H2 : Prop := ∀ p e u : ℕ, p.Prime → p.Coprime u → 0 < u →
  (p : ZMod 5) = 4 → 2 ∣ e + 1 → σ 1 ((σ 1 (p ^ e) / 5) * σ 1 u) ≠ p ^ e * u

def H3 : Prop := ∀ p e u : ℕ, p.Prime → p.Coprime u → 0 < u →
  ((p : ZMod 5) = 2 ∨ (p : ZMod 5) = 3) → 4 ∣ e + 1 → σ 1 ((σ 1 (p ^ e) / 5) * σ 1 u) ≠ p ^ e * u

theorem main : H1 → H2 → H3 → type_of% @Superperfect.twoFivePerfect := by
  intro h1 h2 h3 ⟨n, hn, heq⟩
  let m := σ 1 n
  change σ 1 m = 5 * n at heq
  have hm : m ≠ 0 := (sigma_pos 1 n hn.ne').ne'
  have hd : 5 ∣ σ 1 m := ⟨n, heq⟩
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm] at hd
  simp only [mul_one] at hd
  have prime5 : Prime (5 : ℕ) := by decide
  obtain ⟨p, hp, hd⟩ := (prime5.dvd_finsetProd_iff _).mp hd
  let e := m.factorization p
  let u := m / p^e
  have pp := Nat.prime_of_mem_primeFactors hp
  have hu : p.Coprime u := Nat.coprime_ordCompl pp hm
  have hup : 0 < u := Nat.ordCompl_pos p hm
  have hfac : p^e * u = m := Nat.ordProj_mul_ordCompl_eq_self m p
  have hσ : 5 ∣ σ 1 (p^e) := by rwa [sigma_one_apply_prime_pow pp]
  have he : (σ 1 (p^e) / 5) * σ 1 u = n := by
    rw [← hfac, isMultiplicative_sigma.map_mul_of_coprime (hu.pow_left e)] at heq
    have hh := Nat.div_mul_cancel hσ
    nlinarith only [heq, congrArg (· * σ 1 u) hh]
  have bad : ¬ (σ 1 ((σ 1 (p ^ e) / 5) * σ 1 u) ≠ p ^ e * u) := by
    rw [he, hfac]
    exact fun h => h rfl
  have hz : (∑ i ∈ Finset.range (e+1), (p : ZMod 5)^i) = 0 := by
    have hh := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at hh
    exact hh
  by_cases hone : (p : ZMod 5) = 1
  · apply bad (h1 p e u pp hu hup hone ?_)
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa [hone] using hz
  have hpw := geom_sum_mul (p : ZMod 5) (e+1)
  rw [hz, zero_mul] at hpw
  have ho := orderOf_dvd_of_pow_eq_one (sub_eq_zero.mp hpw.symm)
  have hnz : (p : ZMod 5) ≠ 0 := by
    intro h
    have hpow : (p : ZMod 5)^(e+1) = 1 := sub_eq_zero.mp hpw.symm
    rw [h, zero_pow (Nat.succ_ne_zero e)] at hpow
    exact (by decide : (0 : ZMod 5) ≠ 1) hpow
  have classes : ∀ x : ZMod 5, x ≠ 0 → x ≠ 1 → x = 4 ∨ x = 2 ∨ x = 3 := by decide
  rcases classes _ hnz hone with h | h
  · have hh : orderOf (p : ZMod 5) = 2 := by
      rw [h]
      exact orderOf_eq_prime (by decide) (by decide)
    exact bad (h2 p e u pp hu hup h (hh ▸ ho))
  · have hh : orderOf (p : ZMod 5) = 2^(1+1) := by
      apply orderOf_eq_prime_pow (p := 2) (n := 1)
      · rcases h with h | h <;> rw [h] <;> decide
      · rcases h with h | h <;> rw [h] <;> decide
    rw [hh] at ho
    exact bad (h3 p e u pp hu hup h ho)

end OMA.R_Superperfect_twoFivePerfect_R1
