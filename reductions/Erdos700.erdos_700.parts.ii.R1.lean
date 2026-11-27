import FormalConjectures.ErdosProblems.«700»

-- Reduction Erdos700.erdos_700.parts.ii.R1 of Erdős Problem 700 — ii
-- Credit: @implicitall
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Strategy (A. Tresmontant's elementary argument, verified at erdosproblemaday.com/day/700):
-- H1 is the Lucas-digit lemma for close prime triples with increasing gaps,
-- H2 is the existence of infinitely many such triples (Chebyshev plus pigeonhole).

namespace OMA.R_Erdos700_erdos_700_parts_ii_R1

/-- For primes `p < q < r` with increasing gaps `q - p < r - q` and `2 (r - p)^2 < p`,
the product `n = p q r` satisfies `f n > sqrt n`. -/
def H1 : Prop :=
  ∀ p q r : ℕ, p.Prime → q.Prime → r.Prime → p < q → q < r → q - p < r - q →
    2 * (r - p) ^ 2 < p → Erdos700.f (p * q * r) ^ 2 > p * q * r

/-- There are arbitrarily large prime triples `p < q < r` with increasing gaps and
`2 (r - p)^2 < p`. -/
def H2 : Prop :=
  ∀ N : ℕ, ∃ p q r : ℕ, N < p ∧ p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧
    q - p < r - q ∧ 2 * (r - p) ^ 2 < p

theorem main : H1 → H2 → type_of% @Erdos700.erdos_700.parts.ii := by
  intro h1 h2
  refine Set.infinite_of_forall_exists_gt ?_
  intro N
  obtain ⟨p, q, r, hN, hp, hq, hr, hpq, hqr, hgap, hsmall⟩ := h2 N
  refine ⟨p * q * r, ⟨?_, ?_, h1 p q r hp hq hr hpq hqr hgap hsmall⟩, ?_⟩
  · rw [mul_assoc]
    exact Nat.not_prime_mul hp.one_lt.ne' (Nat.one_lt_mul_iff.mpr
      ⟨hq.pos, hr.pos, Or.inl hq.one_lt⟩).ne'
  · have := hp.one_lt
    have := hq.pos
    have := hr.pos
    calc 1 < p := hp.one_lt
      _ ≤ p * q := Nat.le_mul_of_pos_right p hq.pos
      _ ≤ p * q * r := Nat.le_mul_of_pos_right _ hr.pos
  · calc N < p := hN
      _ ≤ p * q := Nat.le_mul_of_pos_right p hq.pos
      _ ≤ p * q * r := Nat.le_mul_of_pos_right _ hr.pos

end OMA.R_Erdos700_erdos_700_parts_ii_R1
