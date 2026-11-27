import FormalConjectures.Wikipedia.Agrawal

/-! Reduction by separability and descent to prime-power divisors of the modulus. -/

open Polynomial

namespace OMA.R_AgrawalConjecture_agrawal_conjecture_R1

/-- At a prime modulus, test divisibility with multiplicity two. -/
def H1 : Prop :=
  ∀ n p : ℕ, 1 < n → ¬ n.Prime → p.Prime → n.Coprime p →
    let x := (X : Polynomial (ZMod n))
    (x ^ p - 1)^2 ∣ (x - 1)^n - (x^n - 1) → p ∣ n^2 - 1

/-- Lift the arithmetic congruence by one prime-power level. -/
def H2 : Prop :=
  ∀ n p k : ℕ, 1 < n → ¬ n.Prime → p.Prime → n.Coprime p → 0 < k →
    p^k ∣ n^2 - 1 →
    let x := (X : Polynomial (ZMod n))
    (x ^ (p^(k+1)) - 1)^2 ∣ (x - 1)^n - (x^n - 1) → p^(k+1) ∣ n^2 - 1

private theorem double_factor {R : Type*} [CommRing R] {g f : R[X]}
    (hs : g.Separable) (hd : derivative f = 0) (h : g ∣ f) : g^2 ∣ f := by
  obtain ⟨q, rfl⟩ := h
  rw [derivative_mul] at hd
  have hq : g ∣ q := hs.dvd_of_dvd_mul_left (by
    use -derivative q
    linear_combination hd)
  obtain ⟨a, rfl⟩ := hq
  exact ⟨a, by ring⟩

theorem main : H1 → H2 → type_of% @AgrawalConjecture.agrawal_conjecture := by
  intro hPrime hLift n r hn _ hg
  dsimp only
  intro h
  by_cases hp : n.Prime
  · exact Or.inl hp
  right
  let x := (X : Polynomial (ZMod n))
  let f := (x - 1)^n - (x^n - 1)
  have hf : x^r - 1 ∣ f := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have hzero : (n : Polynomial (ZMod n)) = 0 := by
    rw [← C_eq_natCast]; simp
  have hd : derivative f = 0 := by simp [f, derivative_pow, hzero]
  have hs : (x^r - 1).Separable := by
    simpa [x] using separable_X_pow_sub_C_unit (n := r) (1 : (ZMod n)ˣ)
      ((ZMod.isUnit_iff_coprime r n).2 (Nat.Coprime.symm hg))
  have descend (d : ℕ) (hdv : d ∣ r) : (x^d - 1)^2 ∣ f := by
    obtain ⟨a, rfl⟩ := hdv
    have hdiv : x^d - 1 ∣ x^(d*a) - 1 := by
      rw [pow_mul]; exact sub_one_dvd_pow_sub_one _ _
    exact (pow_dvd_pow_of_dvd hdiv 2).trans (double_factor hs hd hf)
  have hdiv : r ∣ n^2 - 1 := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
    intro p k hpr
    induction k with
    | zero => simp
    | succ k ih =>
      intro hpk
      have hpd : p ∣ p^(k+1) := dvd_pow_self _ (by omega)
      have hc := Nat.Coprime.of_dvd_right (hpd.trans hpk) hg
      cases k with
      | zero => simpa using hPrime n p hn hp hpr hc (descend p (hpd.trans hpk))
      | succ j =>
        exact hLift n p (j+1) hn hp hpr hc (by omega)
          (ih ((pow_dvd_pow p (by omega)).trans hpk)) (descend _ hpk)
  have hm := (Nat.modEq_iff_dvd' (show 1 ≤ n^2 by nlinarith)).2 hdiv
  simpa using (ZMod.natCast_eq_natCast_iff _ _ _).2 hm.symm

end OMA.R_AgrawalConjecture_agrawal_conjecture_R1
