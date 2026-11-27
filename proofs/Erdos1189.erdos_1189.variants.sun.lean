import FormalConjectures.ErdosProblems.«1189»

/-! Sun’s irreducible covering set for an odd prime. -/

-- Problem: Erdős Problem 1189 — sun
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1189.lean:161 (declaration Erdos1189.erdos_1189.variants.sun)
-- Credit: @vkascheev (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace SunCover

open Erdos1189

private def moduli (p n : ℕ) : Finset ℕ :=
  ((2 ^ n * p).divisors.filter (1 < ·))

private lemma mem_moduli {p n m : ℕ} (hp : p.Prime) :
    m ∈ moduli p n ↔
      (∃ i : ℕ, 0 < i ∧ i ≤ n ∧ m = 2 ^ i) ∨
      (∃ i : ℕ, i ≤ n ∧ m = 2 ^ i * p) := by
  simp only [moduli, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨c, hc⟩, -⟩, hm⟩
    have hprod : p ∣ m * c := by rw [← hc]; exact dvd_mul_left _ _
    rcases hp.dvd_mul.mp hprod with ⟨d, hd⟩ | ⟨d, hd⟩
    · have heq : 2 ^ n = d * c := by
        apply Nat.eq_of_mul_eq_mul_left hp.pos
        simpa [hd, mul_assoc, mul_comm, mul_left_comm] using hc
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ⟨c, heq⟩
      exact Or.inr ⟨i, hi, by rw [hd, hi', mul_comm]⟩
    · have heq : 2 ^ n = m * d := by
        apply Nat.eq_of_mul_eq_mul_left hp.pos
        simpa [hd, mul_assoc, mul_comm, mul_left_comm] using hc
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ⟨d, heq⟩
      refine Or.inl ⟨i, ?_, hi, hi'⟩
      by_contra! h
      have : i = 0 := by omega
      simp [hi', this] at hm
  · have hne : 2 ^ n * p ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ (by decide)) hp.ne_zero
    rintro (⟨i, hi, hin, rfl⟩ | ⟨i, hin, rfl⟩)
    · refine ⟨⟨(pow_dvd_pow 2 hin).trans (dvd_mul_right _ _), hne⟩, ?_⟩
      exact one_lt_pow₀ (by decide) (Nat.ne_of_gt hi)
    · refine ⟨⟨mul_dvd_mul_right (pow_dvd_pow 2 hin) p, hne⟩, ?_⟩
      exact hp.one_lt.trans_le (Nat.le_mul_of_pos_left p (by positivity))

private lemma dyadic_not_zero (n : ℕ) :
    ¬ (2 : ℤ) ^ n ≡ 0 [ZMOD (2 : ℤ) ^ (n + 1)] := by
  intro h
  have h' : (2 : ℤ) ^ n * 1 ≡ (2 : ℤ) ^ n * 0 [ZMOD (2 : ℤ) ^ n * 2] := by
    simpa [pow_succ] using h
  have h'' := Int.ModEq.mul_left_cancel' (show (2 : ℤ) ^ n ≠ 0 by positivity) h'
  exact (by decide : ¬ (1 : ℤ) ≡ 0 [ZMOD 2]) h''

private lemma avoid_powers (a : ℕ → ℤ) (n : ℕ) :
    ∃ r : ℤ, ∀ k < n, ¬ r ≡ a (2 ^ (k + 1)) [ZMOD (2 : ℤ) ^ (k + 1)] := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    by_cases h : r ≡ a (2 ^ (n + 1)) [ZMOD (2 : ℤ) ^ (n + 1)]
    · have hs : r + (2 : ℤ) ^ n ≡ r [ZMOD (2 : ℤ) ^ n] :=
        Int.add_modEq_right
      refine ⟨r + (2 : ℤ) ^ n, fun k hk hz => ?_⟩
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkn | rfl
      · exact hr k hkn ((hs.of_dvd (pow_dvd_pow 2 (Nat.succ_le_of_lt hkn))).symm.trans hz)
      · have hshift : r + (2 : ℤ) ^ k ≡ r + 0 [ZMOD (2 : ℤ) ^ (k + 1)] := by
          simpa only [add_zero] using hz.trans h.symm
        exact dyadic_not_zero k (hshift.add_left_cancel' r)
    · refine ⟨r, fun k hk => ?_⟩
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkn | rfl
      · exact hr k hkn
      · exact h

private lemma cover_powers (z : ℤ) (n : ℕ) :
    (∃ k < n, z ≡ (2 : ℤ) ^ k [ZMOD (2 : ℤ) ^ (k + 1)]) ∨
    z ≡ 0 [ZMOD (2 : ℤ) ^ n] := by
  induction n with
  | zero => exact Or.inr (by simpa using Int.modEq_one)
  | succ n ih =>
    rcases ih with ⟨k, hk, hz⟩ | hz
    · exact Or.inl ⟨k, by omega, hz⟩
    · obtain ⟨q, hq⟩ := Int.modEq_zero_iff_dvd.mp hz
      by_cases h : q ≡ 0 [ZMOD 2]
      · exact Or.inr (by simpa [hq, pow_succ] using h.mul_left' (c := (2 : ℤ) ^ n))
      · have h' : q ≡ 1 [ZMOD 2] := by
          change ¬ q % 2 = 0 % 2 at h
          change q % 2 = 1 % 2
          omega
        exact Or.inl ⟨n, Nat.lt_succ_self _, by
          simpa [hq, pow_succ] using h'.mul_left' (c := (2 : ℤ) ^ n)⟩

private lemma missing_residue {p j : ℕ} (hp : 0 < p) (hj : j < p) (a : ℕ → ℤ) :
    ∃ t : ℤ, ∀ i < p, i ≠ j → ¬ t ≡ a i [ZMOD (p : ℤ)] := by
  let s := (Finset.range p).erase j
  let f : ℕ → ℕ := fun i => (a i % (p : ℤ)).toNat
  have hcard : (s.image f).card < (Finset.range p).card := by
    have hle := Finset.card_image_le (s := s) (f := f)
    have hs : s.card = p - 1 := by
      simp [s, Finset.card_erase_of_mem (Finset.mem_range.mpr hj)]
    rw [hs] at hle
    simp only [Finset.card_range]
    omega
  obtain ⟨t, ht, ht'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have htp : (t : ℤ) < (p : ℤ) := by exact_mod_cast Finset.mem_range.mp ht
  have hp' : (p : ℤ) ≠ 0 := by positivity
  refine ⟨t, fun i hi hij he => ht' (Finset.mem_image.mpr ⟨i, ?_, ?_⟩)⟩
  · exact Finset.mem_erase.mpr ⟨hij, Finset.mem_range.mpr hi⟩
  · change (a i % (p : ℤ)).toNat = t
    rw [← he.eq, Int.emod_eq_of_lt (by positivity) htp]
    simp

private lemma is_covering {p n : ℕ} (hp : p.Prime) (hn : p = n + 1)
    (hc : (2 ^ n : ℕ).Coprime p)
    (hpow : ∀ k : ℕ, ¬ p ∣ (2 : ℕ) ^ k) :
    IsCoveringSet (moduli p n) := by
  obtain ⟨y, hy⟩ := Int.mod_coprime hc
  have hy' : (2 : ℤ) ^ n * y ≡ 1 [ZMOD (p : ℤ)] := by exact_mod_cast hy
  let a : ℕ → ℤ := fun m =>
    if p ∣ m then (2 : ℤ) ^ n * y * (Nat.log 2 (m / p) : ℤ)
    else ((m / 2 : ℕ) : ℤ)
  refine ⟨fun m hm => (Finset.mem_filter.mp hm).2, a, fun z => ?_⟩
  rcases cover_powers z n with ⟨k, hk, hz⟩ | hz
  · refine ⟨2 ^ (k + 1), (mem_moduli hp).mpr (Or.inl ⟨k + 1, by omega, by omega, rfl⟩), ?_⟩
    rw [show a (2 ^ (k + 1)) = (2 : ℤ) ^ k by
      simp only [a, if_neg (hpow (k + 1))]
      rw [pow_succ, Nat.mul_div_cancel _ (by decide : 0 < (2 : ℕ))] <;> simp]
    exact_mod_cast hz
  · obtain ⟨t, ht, htz⟩ := Int.existsUnique_equiv_nat z (b := (p : ℤ)) (by exact_mod_cast hp.pos)
    have htn : t ≤ n := by omega
    have ht' : a (2 ^ t * p) = (2 : ℤ) ^ n * y * (t : ℤ) := by
      simp [a, Nat.mul_div_cancel _ hp.pos, Nat.log_pow (by decide : 1 < (2 : ℕ))]
    have hz₁ : z ≡ a (2 ^ t * p) [ZMOD (2 : ℤ) ^ t] := by
      apply (hz.of_dvd (pow_dvd_pow 2 htn)).trans
      rw [ht', Int.modEq_comm, Int.modEq_zero_iff_dvd]
      exact ((pow_dvd_pow 2 htn).trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _)
    have hz₂ : z ≡ a (2 ^ t * p) [ZMOD (p : ℤ)] := by
      rw [ht']
      exact htz.symm.trans (by simpa using (hy'.mul_right (t : ℤ)).symm)
    have hcop : ((2 : ℤ) ^ t).natAbs.Coprime (p : ℤ).natAbs := by
      simpa using (hp.coprime_iff_not_dvd.mpr (hpow t)).symm
    refine ⟨2 ^ t * p, (mem_moduli hp).mpr (Or.inr ⟨t, htn, rfl⟩), ?_⟩
    exact_mod_cast (Int.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hz₁, hz₂⟩

private lemma not_covering_subset {p n : ℕ} (hp : p.Prime) (hn : p = n + 1)
    (hc : (2 ^ n : ℕ).Coprime p) (N : Finset ℕ) (hN : N ⊂ moduli p n) :
    ¬ IsCoveringSet N := by
  rintro ⟨-, a, ha⟩
  obtain ⟨m, hm, hmN⟩ := (Finset.ssubset_iff_of_subset hN.subset).mp hN
  have havoids : ∃ (r : ℤ) (j : ℕ), j < p ∧
      (∀ k < n, 2 ^ (k + 1) ∈ N → ¬ r ≡ a (2 ^ (k + 1)) [ZMOD (2 : ℤ) ^ (k + 1)]) ∧
      (2 ^ j * p ∈ N → ¬ r ≡ a (2 ^ j * p) [ZMOD (2 : ℤ) ^ j]) := by
    rcases (mem_moduli hp).mp hm with ⟨i, hi, hin, rfl⟩ | ⟨i, hin, rfl⟩
    · -- Use the missing power of two to exclude the largest modulus divisible by p.
      let b : ℕ → ℤ := fun d => if d = 2 ^ i then a (2 ^ n * p) else a d
      obtain ⟨r, hr⟩ := avoid_powers b n
      refine ⟨r, n, by omega, ?_, fun _ hz => ?_⟩
      · intro k hk hkN
        have hne : 2 ^ (k + 1) ≠ (2 : ℕ) ^ i := fun he => hmN (he ▸ hkN)
        simpa [b, hne] using hr k hk
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
        exact hr k (by omega) (by
          simpa [b] using hz.of_dvd (pow_dvd_pow 2 hin))
    · obtain ⟨r, hr⟩ := avoid_powers a n
      exact ⟨r, i, by omega, fun k hk _ => hr k hk, fun hi => (hmN hi).elim⟩
  obtain ⟨r, j, hj, hr, hside⟩ := havoids
  obtain ⟨t, ht⟩ := missing_residue hp.pos hj (fun i => a (2 ^ i * p))
  obtain ⟨y, hy⟩ := Int.mod_coprime hc
  have hy' : (2 : ℤ) ^ n * y ≡ 1 [ZMOD (p : ℤ)] := by exact_mod_cast hy
  let z := r + (2 : ℤ) ^ n * (y * (t - r))
  have hzr : z ≡ r [ZMOD (2 : ℤ) ^ n] := Int.modEq_add_fac_self
  have hzt : z ≡ t [ZMOD (p : ℤ)] := by
    have h := (hy'.mul_right (t - r)).add_left r
    have hleft : r + (2 : ℤ) ^ n * y * (t - r) = z := by simp [z, mul_assoc]
    have hright : r + 1 * (t - r) = t := by ring
    rwa [hleft, hright] at h
  obtain ⟨d, hd, hz⟩ := ha z
  rcases (mem_moduli hp).mp (hN.subset hd) with ⟨i, hi, hin, rfl⟩ | ⟨i, hin, rfl⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    have hz' : z ≡ a (2 ^ (k + 1)) [ZMOD (2 : ℤ) ^ (k + 1)] := by exact_mod_cast hz
    exact hr k (by omega) hd ((hzr.of_dvd (pow_dvd_pow 2 hin)).symm.trans hz')
  · have hz' : z ≡ a (2 ^ i * p) [ZMOD (2 : ℤ) ^ i * (p : ℤ)] := by exact_mod_cast hz
    by_cases hij : i = j
    · subst i
      exact hside hd ((hzr.of_dvd (pow_dvd_pow 2 hin)).symm.trans (hz'.of_mul_right _))
    · exact ht i (by omega) hij (hzt.symm.trans (hz'.of_mul_left _))

private theorem irreducible (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    IsIrreducibleCoveringSet ((2 ^ (p - 1) * p).divisors.filter (1 < ·)) := by
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    exact (by decide : ¬ Odd (2 : ℕ)) hodd
  have hpow : ∀ k : ℕ, ¬ p ∣ (2 : ℕ) ^ k :=
    fun _ h => hp2 (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h)
  have hn : p = (p - 1) + 1 := by have := hp.pos; omega
  have hc : (2 ^ (p - 1) : ℕ).Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (hpow _)).symm
  exact ⟨is_covering hp hn hc hpow, fun N => not_covering_subset hp hn hc N⟩

end SunCover

theorem OMA.solution : type_of% @Erdos1189.erdos_1189.variants.sun := by
  exact SunCover.irreducible
