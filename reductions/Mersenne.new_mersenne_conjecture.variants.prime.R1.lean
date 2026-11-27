import FormalConjectures.Wikipedia.Mersenne
/-! For prime exponents above five, a prime of the form 2p+1 excludes
both special form and simultaneous Mersenne and Wagstaff primality. -/

-- Credit: @desenyon
open Mersenne

namespace OMA.R_Mersenne_new_mersenne_conjecture_variants_prime_R1

private theorem no_prime_pair (p : ℕ) (h : Odd p) (h₇ : 7 ≤ p) (hq : (2*p+1).Prime)
    (hm : (mersenne p).Prime) (hw : Nat.GivesWagstaffPrime p) : False := by
  have size (n : ℕ) (hn : 7 ≤ n) : 6*n+6 < 2^n := by
    induction n, hn using Nat.le_induction with
    | base => decide
    | succ n hn ih => rw [pow_succ]; omega
  have hs := size p h₇
  have hd : 3 ∣ 2^p+1 := by
    simpa using h.nat_add_dvd_pow_add_pow (x := 2) (y := 1)
  have he := Nat.div_mul_cancel hd
  let q := 2*p+1
  have : Fact q.Prime := ⟨hq⟩
  have hn : (2 : ZMod q) ≠ 0 := by
    change ((2 : ℕ) : ZMod q) ≠ 0
    intro hzero
    apply (show ¬q ∣ 2 by exact Nat.not_dvd_of_pos_of_lt (by decide) (by dsimp [q]; omega))
    exact (CharP.cast_eq_zero_iff (ZMod q) q 2).mp hzero
  have hf := ZMod.pow_card_sub_one_eq_one hn
  have hh : q-1 = p+p := by dsimp [q]; omega
  rw [hh, pow_add] at hf
  have hz : ((2 : ZMod q)^p-1)*(2^p+1) = 0 := by linear_combination hf
  have smallM : q < mersenne p := by dsimp [q, mersenne]; omega
  have smallW : q < (2^p+1)/3 := by dsimp [q]; omega
  have contra (n : ℕ) (hp : n.Prime) (hlt : q < n) (dvd : q ∣ n) : False := by
    rcases hp.eq_one_or_self_of_dvd q dvd with ha | ha <;> dsimp [q] at * <;> omega
  rcases mul_eq_zero.mp hz with hz | hz
  · apply contra _ hm smallM
    apply (CharP.cast_eq_zero_iff (ZMod q) q _).mp
    simpa [mersenne, Nat.cast_sub (show 1 ≤ (2:ℕ)^p by omega)] using hz
  · have dv : q ∣ 2^p+1 := by
      apply (CharP.cast_eq_zero_iff (ZMod q) q _).mp
      simpa using hz
    rw [← he] at dv
    rcases hq.dvd_mul.mp dv with hd | hd
    · exact contra _ hw.2 smallW hd
    · exact Nat.not_dvd_of_pos_of_lt (by decide) (by dsimp [q]; omega : 3 < q) hd

private theorem not_special {p : ℕ} (h : 7 ≤ p) (hp : p.Prime) (hq : (2*p+1).Prime) :
    ¬ Nat.IsSpecialForm p := by
  have excl (n : ℕ) (hn : n.Prime) (hl : 5 < n) : ¬3 ∣ n ∧ ¬5 ∣ n := by
    constructor <;> intro hd <;> have := hn.eq_one_or_self_of_dvd _ hd <;> omega
  obtain ⟨a,b⟩ := excl p hp (by omega)
  obtain ⟨c,d⟩ := excl _ hq (by omega)
  have cycle (k : ℕ) : 2^k % 15 = 1 ∨ 2^k % 15 = 2 ∨ 2^k % 15 = 4 ∨ 2^k % 15 = 8 := by
    induction k with
    | zero => decide
    | succ k ih => rw [pow_succ, Nat.mul_mod]; rcases ih with e|e|e|e <;> rw [e] <;> decide
  have four (k : ℕ) : 4^k % 3 = 1 := by simp [Nat.pow_mod]
  rintro ⟨k, h1|h2|h3|h4⟩
  · rcases cycle k with e|e|e|e <;> omega
  · rcases cycle k with e|e|e|e <;> omega
  · have := four k; omega
  · have := four k; omega

/-- For nonspecial exponents with composite double-plus-one, the two candidates
have no simultaneous prime values. -/
def H1 : Prop := ∀ p : ℕ, 7 ≤ p → p.Prime → Odd p → ¬ (2*p+1).Prime →
  ¬ Nat.IsSpecialForm p → (mersenne p).Prime → ¬ Nat.GivesWagstaffPrime p

/-- On the special exponents still under consideration the two tests agree. -/
def H2 : Prop := ∀ p : ℕ, 7 ≤ p → p.Prime → Odd p → ¬ (2*p+1).Prime →
  Nat.IsSpecialForm p → ((mersenne p).Prime ↔ Nat.GivesWagstaffPrime p)

theorem main : H1 → H2 → type_of% @Mersenne.new_mersenne_conjecture.variants.prime := by
  intro hn hs p hp ho
  by_cases hl : 7 ≤ p
  · by_cases hq : (2*p+1).Prime
    · have nf := not_special hl hp hq
      exact ⟨fun ⟨hm,hw⟩ => (no_prime_pair p ho hl hq hm hw).elim,
        fun ⟨_,hf⟩ => (nf hf).elim, fun ⟨_,hf⟩ => (nf hf).elim⟩
    by_cases hf : Nat.IsSpecialForm p
    · have e := hs p hl hp ho hq hf
      exact ⟨fun _ => hf, fun h => e.mp h.1, fun h => e.mpr h.1⟩
    exact ⟨fun h => (hn p hl hp ho hq hf h.1 h.2).elim,
      fun h => (hf h.2).elim, fun h => (hf h.2).elim⟩
  have cases : p = 3 ∨ p = 5 := by
    have := hp.two_le
    obtain ⟨k,hk⟩ := ho
    omega
  rcases cases with rfl | rfl
  · exact ⟨fun _ => ⟨1, Or.inl rfl⟩, fun _ => ⟨by decide, by decide⟩, fun _ => by decide⟩
  · exact ⟨fun _ => ⟨2, Or.inl rfl⟩, fun _ => ⟨by decide, by decide⟩, fun _ => by decide⟩

end OMA.R_Mersenne_new_mersenne_conjecture_variants_prime_R1
