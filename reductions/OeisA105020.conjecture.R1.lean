import FormalConjectures.OEIS.«105020»

/-
Michael Hiebl posed the sequence question in OEIS A105020 (2007).
Wesley Ivan Hurt recorded its row connection with Goldbach pairs in A228553 (2021).
The equivalence below includes every pair of endpoints allowed by the Lean statement.
-/
namespace OMA.R_OeisA105020_conjecture_R1

open OeisA105020
open scoped ArithmeticFunction.Omega

lemma triangular_step (c : ℕ) :
    triangularNumber (c + 1) = triangularNumber c + c + 1 := by
  change (c + 1 + 1).choose (1 + 1) = (c + 1).choose 2 + c + 1
  rw [Nat.choose_succ_succ, Nat.choose_one_right]
  change (c + 1) + (c + 1).choose 2 = (c + 1).choose 2 + c + 1
  omega

lemma twice_triangular (c : ℕ) : 2 * triangularNumber c = c * (c + 1) := by
  induction c with
  | zero => decide
  | succ c ih =>
    rw [triangular_step]
    nlinarith

lemma row_index (c t : ℕ) (ht : t ≤ c) :
    antidiagonalIndex (triangularNumber c + t) = c := by
  have h := twice_triangular c
  have lo : 2*c + 1 ≤ Nat.sqrt (8 * (triangularNumber c + t) + 1) := by
    apply Nat.le_sqrt.mpr
    nlinarith
  have hi : Nat.sqrt (8 * (triangularNumber c + t) + 1) < 2*c + 3 := by
    apply Nat.sqrt_lt.mpr
    nlinarith
  unfold antidiagonalIndex
  omega

lemma entry_factors (c t : ℕ) (ht : t ≤ c) :
    a (triangularNumber c + t) = (t + 1) * (2*c + 1 - t) := by
  unfold a
  rw [row_index c t ht]
  simp only [Nat.add_sub_cancel_left]
  have he : 2*c + 1 - t = c + (c - t) + 1 := by omega
  rw [he]
  generalize hz : c - t = z
  have hc : c = t + z := by omega
  subst c
  apply Nat.sub_eq_of_eq_add
  ring

lemma row_start (c : ℕ) : a (triangularNumber c) = 2*c + 1 := by
  simpa using entry_factors c 0 (Nat.zero_le _)

lemma locate_entry (i : ℕ) :
    ∃ c t, t ≤ c ∧ i = triangularNumber c + t := by
  induction i with
  | zero => exact ⟨0, 0, le_rfl, rfl⟩
  | succ i ih =>
    obtain ⟨c, t, ht, rfl⟩ := ih
    by_cases h : t = c
    · exact ⟨c + 1, 0, Nat.zero_le _, by rw [triangular_step]; omega⟩
    · exact ⟨c, t + 1, by omega, by omega⟩

lemma prime_factors_of_semiprime {p q : ℕ} (hp : 1 < p) (hq : 1 < q)
    (h : (p*q).IsSemiprime) : p.Prime ∧ q.Prime := by
  have htot := h.2
  rw [ArithmeticFunction.cardFactors_mul (by omega) (by omega)] at htot
  have hp' := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hp
  have hq' := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hq
  exact ⟨ArithmeticFunction.cardFactors_eq_one_iff_prime.mp (by omega),
    ArithmeticFunction.cardFactors_eq_one_iff_prime.mp (by omega)⟩

lemma row_witness_of_ordered_primes {c p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≤ q) (hs : 2*c + 2 = p + q) :
    ∃ t, 1 ≤ t ∧ t ≤ c ∧ (a (triangularNumber c + t)).IsSemiprime := by
  have hp2 := hp.two_le
  have ht : p - 1 ≤ c := by omega
  refine ⟨p - 1, by omega, ht, ?_⟩
  rw [entry_factors c (p-1) ht, show p - 1 + 1 = p by omega,
    show 2*c + 1 - (p-1) = q by omega]
  exact hp.mul_isAlmostPrime_two hq

lemma space_for_next_row {c t n : ℕ} (ht : t ≤ c) (ht0 : 0 < t)
    (h : (t + 1) * (2*c + 1 - t) = 2*n + 1) : 2 ≤ t ∧ 2*c ≤ n := by
  have ht2 : 2 ≤ t := by
    by_contra! hbad
    have : t = 1 := by omega
    subst t
    simp at h
    omega
  refine ⟨ht2, ?_⟩
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht2
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le ht
  have he : 2 * (2 + u + v) + 1 - (2 + u) = u + 2*v + 3 := by omega
  rw [he] at h
  nlinarith [Nat.zero_le (u*u), Nat.zero_le (u*v)]

lemma intervals_of_rows
    (rows : ∀ c : ℕ, 1 ≤ c → ∃ t, 1 ≤ t ∧ t ≤ c ∧
      (a (triangularNumber c + t)).IsSemiprime) :
    ∀ n i j : ℕ, 1 ≤ n → a i = 2*n + 1 → j = i+n+1 →
      ∃ k, i < k ∧ k < j ∧ (a k).IsSemiprime := by
  intro n i j hn hi hj
  obtain ⟨c, t, ht, rfl⟩ := locate_entry i
  rw [entry_factors c t ht] at hi
  by_cases hzero : t = 0
  · subst t
    simp at hi
    obtain ⟨u, hu, huc, hsemi⟩ := rows c (by omega)
    exact ⟨triangularNumber c + u, by omega, by omega, hsemi⟩
  · obtain ⟨ht2, hsize⟩ := space_for_next_row ht (by omega) hi
    obtain ⟨u, hu, huc, hsemi⟩ := rows (c + 1) (by omega)
    refine ⟨triangularNumber (c + 1) + u, ?_, ?_, hsemi⟩ <;>
      rw [triangular_step] <;> omega

lemma rows_of_goldbach
    (goldbach : ∀ e : ℕ, 2 < e → Even e → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ e = p + q) :
    ∀ c : ℕ, 1 ≤ c → ∃ t, 1 ≤ t ∧ t ≤ c ∧
      (a (triangularNumber c + t)).IsSemiprime := by
  intro c hc
  obtain ⟨p, q, hp, hq, hs⟩ := goldbach (2*c + 2) (by omega) ⟨c+1, by omega⟩
  rcases le_total p q with h | h
  · exact row_witness_of_ordered_primes hp hq h hs
  · exact row_witness_of_ordered_primes hq hp h (by omega)

lemma sequence_iff_goldbach :
    (type_of% @OeisA105020.conjecture) ↔
      ∀ e : ℕ, 2 < e → Even e → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ e = p + q := by
  constructor
  · intro sequence e he heven
    obtain ⟨m, hm⟩ := heven
    let c := m - 1
    have hc : 1 ≤ c := by dsimp [c]; omega
    have heq : e = 2*c + 2 := by dsimp [c]; omega
    obtain ⟨k, hlo, hhi, hsemi⟩ := sequence c (triangularNumber c)
      (triangularNumber (c + 1)) hc (row_start c) (by rw [row_start]; omega)
      (triangular_step c)
    rw [triangular_step] at hhi
    let t := k - triangularNumber c
    have ht : t ≤ c := by dsimp [t]; omega
    have htpos : 0 < t := by dsimp [t]; omega
    have hk : k = triangularNumber c + t := by dsimp [t]; omega
    rw [hk, entry_factors c t ht] at hsemi
    obtain ⟨hp, hq⟩ := prime_factors_of_semiprime (by omega) (by omega) hsemi
    exact ⟨t + 1, 2*c + 1 - t, hp, hq, by omega⟩
  · intro goldbach n i j hn hi _ hj
    exact intervals_of_rows (rows_of_goldbach goldbach) n i j hn hi hj

/-- The sequence conjecture already implies a semiprime among the next `n` terms
whenever the current entry is `2*n+1`. The value at the far endpoint is unnecessary. -/
lemma sequence_iff_first_endpoint :
    (type_of% @OeisA105020.conjecture) ↔
      ∀ n i : ℕ, 1 ≤ n → a i = 2*n + 1 →
        ∃ k, i < k ∧ k < i+n+1 ∧ (a k).IsSemiprime := by
  constructor
  · intro sequence n i hn hi
    exact intervals_of_rows (rows_of_goldbach (sequence_iff_goldbach.mp sequence)) n i _ hn hi rfl
  · intro intervals n i j hn hi _ hj
    subst j
    exact intervals n i hn hi

-- Each remaining case is a statement about primes alone.
def H1 : Prop := ∀ m : ℕ, 0 < m → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 4*m = p + q

def H2 : Prop := ∀ m : ℕ, 0 < m → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 4*m + 2 = p + q

theorem main : H1 → H2 → type_of% @OeisA105020.conjecture := by
  intro h0 h2
  apply sequence_iff_goldbach.mpr
  intro e he heven
  obtain ⟨r, hr⟩ := heven
  by_cases h : e % 4 = 0
  · obtain ⟨p, q, hp, hq, heq⟩ := h0 (e/4) (by omega)
    exact ⟨p, q, hp, hq, by omega⟩
  · obtain ⟨p, q, hp, hq, heq⟩ := h2 (e/4) (by omega)
    exact ⟨p, q, hp, hq, by omega⟩

end OMA.R_OeisA105020_conjecture_R1
