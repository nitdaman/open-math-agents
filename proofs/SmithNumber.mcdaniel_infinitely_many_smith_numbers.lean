import FormalConjectures.Wikipedia.SmithNumber

-- Problem: McDaniel's Theorem (1987)
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/SmithNumber.lean:100 (declaration SmithNumber.mcdaniel_infinitely_many_smith_numbers)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# McDaniel's theorem: infinitely many base-10 Smith numbers

The statement is due to W. L. McDaniel (1987). This file gives a self-contained proof along the
lines of his construction.

Write `S(x)` for the digit sum of `x` and `Sp(x)` for the sum of the digit sums of the prime
factors of `x`, counted with multiplicity.

* Every prime `p` satisfies `2 * 10 ^ S(p) ≤ p ^ 9` (`good_prime`). This is proved for all `x ≥ 2`
  other than `8` and the numbers `10 ^ b - 1`, by induction on the number of digits.
* Multiplying over the prime factors gives `2 ^ Ω(m) * 10 ^ Sp(m) ≤ m ^ 9` (`omega_bound`).
* The number `m = 10 ^ (2 ^ j) - 1` has at least `j + 2` prime factors (`omega_rep`), so for
  `j ≥ 25` we get `Sp(m) + 9 ≤ 9 * 2 ^ j` (`sp_rep_bound`).
* For `t ∈ {2, 3, 4, 5, 7, 8, 15}` the digit sum of `t * m` is `9 * 2 ^ j` (`ds_mul_rep`), and the
  values `Sp(t) = 2, 3, 4, 5, 7, 6, 8` cover every residue modulo `7`. Since `Sp(10) = 7`, a
  suitable `t` and a suitable number `b` of trailing zeros make `t * m * 10 ^ b` a Smith number.
-/

namespace OMA.Smith

open SmithNumber

-- Digit sums

lemma ds_add (q d : ℕ) (hd : d < 10) : digitSum 10 (10 * q + d) = digitSum 10 q + d := by
  unfold digitSum
  rcases Nat.eq_zero_or_pos (10 * q + d) with h | h
  · have hq : q = 0 := by omega
    have hd0 : d = 0 := by omega
    subst hq
    subst hd0
    simp
  · rw [Nat.digits_def' (by norm_num) h]
    have h1 : (10 * q + d) % 10 = d := by omega
    have h2 : (10 * q + d) / 10 = q := by omega
    rw [h1, h2, List.sum_cons]
    omega

lemma ds_mul_pow (x b : ℕ) : digitSum 10 (x * 10 ^ b) = digitSum 10 x := by
  induction b with
  | zero => simp
  | succ k ih =>
    have h : x * 10 ^ (k + 1) = 10 * (x * 10 ^ k) + 0 := by ring
    rw [h, ds_add _ _ (by norm_num), ih, Nat.add_zero]

lemma ds_pow_sub_one (k : ℕ) : digitSum 10 (10 ^ k - 1) = 9 * k := by
  induction k with
  | zero => simp [digitSum]
  | succ k ih =>
    have hpos : 1 ≤ 10 ^ k := Nat.one_le_pow k 10 (by norm_num)
    have h : 10 ^ (k + 1) - 1 = 10 * (10 ^ k - 1) + 9 := by
      rw [pow_succ]
      omega
    rw [h, ds_add _ _ (by norm_num), ih]
    ring

lemma ds_append (k : ℕ) : ∀ c a : ℕ, a < 10 ^ k →
    digitSum 10 (c * 10 ^ k + a) = digitSum 10 c + digitSum 10 a := by
  induction k with
  | zero =>
    intro c a ha
    have h0 : a = 0 := by simpa using ha
    subst h0
    simp [digitSum]
  | succ k ih =>
    intro c a ha
    have ha' : a / 10 < 10 ^ k := by
      rw [pow_succ] at ha
      omega
    have hmod : a % 10 < 10 := Nat.mod_lt _ (by norm_num)
    have hdm : 10 * (a / 10) + a % 10 = a := Nat.div_add_mod a 10
    have hsplit : c * 10 ^ (k + 1) + a = 10 * (c * 10 ^ k + a / 10) + a % 10 := by
      calc c * 10 ^ (k + 1) + a = c * 10 ^ (k + 1) + (10 * (a / 10) + a % 10) := by rw [hdm]
        _ = 10 * (c * 10 ^ k + a / 10) + a % 10 := by ring
    have hda : digitSum 10 a = digitSum 10 (a / 10) + a % 10 := by
      have h := ds_add (a / 10) (a % 10) hmod
      rwa [hdm] at h
    rw [hsplit, ds_add _ _ hmod, ih c (a / 10) ha', hda]
    ring

/-- The digit sum of `(s + 1) * (10 ^ (k + 2) - 1)` when `s ≤ 99`. -/
lemma ds_mul_rep (s u k : ℕ) (hsu : s + u = 99) :
    digitSum 10 ((s + 1) * (10 ^ (k + 2) - 1)) = digitSum 10 s + 9 * k + digitSum 10 u := by
  have hP : 1 ≤ 10 ^ k := Nat.one_le_pow k 10 (by norm_num)
  obtain ⟨Q, hQ⟩ : ∃ Q, 10 ^ k = Q + 1 := ⟨10 ^ k - 1, by omega⟩
  have e0 : 10 ^ (k + 2) = 100 * Q + 100 := by
    rw [pow_add, hQ]
    ring
  have e1 : 10 ^ (k + 2) - 1 = 100 * Q + 99 := by omega
  have e2 : (10 ^ k - 1) * 10 ^ 2 = 100 * Q := by
    rw [hQ, Nat.add_sub_cancel]
    ring
  have hsplit : (s + 1) * (10 ^ (k + 2) - 1)
      = s * 10 ^ (k + 2) + ((10 ^ k - 1) * 10 ^ 2 + u) := by
    rw [e1, e0, e2]
    nlinarith [hsu]
  have hu : u < 10 ^ 2 := by omega
  have hlt : (10 ^ k - 1) * 10 ^ 2 + u < 10 ^ (k + 2) := by
    rw [e2, e0]
    omega
  rw [hsplit, ds_append (k + 2) s _ hlt, ds_append 2 (10 ^ k - 1) u hu, ds_pow_sub_one]
  ring

-- The key inequality for primes

/-- `2 * 10 ^ S(x) ≤ x ^ 9` for every `x ≥ 2` other than `8` and the numbers `10 ^ b - 1`. -/
lemma good (x : ℕ) : 2 ≤ x → x ≠ 8 → (∀ b : ℕ, x + 1 ≠ 10 ^ b) →
    2 * 10 ^ digitSum 10 x ≤ x ^ 9 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro h2 h8 hpow
    rcases Nat.lt_or_ge x 10 with hx | hx
    · -- a single digit
      have h9 : x ≠ 9 := by
        intro h
        exact hpow 1 (by rw [h]; norm_num)
      have hds : digitSum 10 x = x := by
        unfold digitSum
        rw [Nat.digits_of_lt 10 x (by omega) hx]
        simp
      rw [hds]
      interval_cases x <;> first | exact absurd rfl h8 | exact absurd rfl h9 | norm_num
    · -- several digits: peel off the last one
      obtain ⟨q, d, hd, rfl⟩ : ∃ q d, d < 10 ∧ x = 10 * q + d :=
        ⟨x / 10, x % 10, Nat.mod_lt _ (by norm_num), by omega⟩
      rw [ds_add q d hd]
      by_cases hq1 : q = 1
      · subst hq1
        have h1 : digitSum 10 1 = 1 := by norm_num [digitSum]
        rw [h1]
        interval_cases d <;> norm_num
      by_cases hq8 : q = 8
      · subst hq8
        have h1 : digitSum 10 8 = 8 := by norm_num [digitSum]
        rw [h1]
        interval_cases d <;> norm_num
      by_cases hqp : ∃ b : ℕ, q + 1 = 10 ^ b
      · obtain ⟨b, hb⟩ := hqp
        have hb1 : 1 ≤ b := by
          rcases Nat.eq_zero_or_pos b with h0 | h0
          · subst h0
            rw [pow_zero] at hb
            omega
          · exact h0
        have hten : 10 ≤ 10 ^ b := by
          calc 10 = 10 ^ 1 := by norm_num
            _ ≤ 10 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
        have hq : q = 10 ^ b - 1 := by omega
        have hds : digitSum 10 q = 9 * b := by
          rw [hq]
          exact ds_pow_sub_one b
        have hd9 : d ≠ 9 := by
          intro h
          apply hpow (b + 1)
          rw [pow_succ, ← hb, h]
          ring
        have key : 9 * 10 ^ b ≤ 10 * q := by omega
        rw [hds]
        calc 2 * 10 ^ (9 * b + d) ≤ 2 * 10 ^ (9 * b + 8) :=
              Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) (by omega))
          _ = (2 * 10 ^ 8) * (10 ^ b) ^ 9 := by ring
          _ ≤ 9 ^ 9 * (10 ^ b) ^ 9 := Nat.mul_le_mul_right _ (by norm_num)
          _ = (9 * 10 ^ b) ^ 9 := by ring
          _ ≤ (10 * q) ^ 9 := Nat.pow_le_pow_left key 9
          _ ≤ (10 * q + d) ^ 9 := Nat.pow_le_pow_left (by omega) 9
      · have hq := ih q (by omega) (by omega) hq8 (fun b hb => hqp ⟨b, hb⟩)
        calc 2 * 10 ^ (digitSum 10 q + d) = (2 * 10 ^ digitSum 10 q) * 10 ^ d := by ring
          _ ≤ q ^ 9 * 10 ^ 9 :=
              Nat.mul_le_mul hq (Nat.pow_le_pow_right (by norm_num) (by omega))
          _ = (10 * q) ^ 9 := by ring
          _ ≤ (10 * q + d) ^ 9 := Nat.pow_le_pow_left (by omega) 9

lemma good_prime (p : ℕ) (hp : p.Prime) : 2 * 10 ^ digitSum 10 p ≤ p ^ 9 := by
  refine good p hp.two_le ?_ ?_
  · rintro rfl
    norm_num at hp
  · intro b hb
    have hp2 := hp.two_le
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0
      rw [pow_zero] at hb
      omega
    · have hmod : 10 ^ b % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have h3 : 3 ∣ p := by omega
      have hp3 : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
      have hten : 10 ≤ 10 ^ b := by
        calc 10 = 10 ^ 1 := by norm_num
          _ ≤ 10 ^ b := Nat.pow_le_pow_right (by norm_num) h0
      omega

-- Prime factorisations

lemma list_bound : ∀ L : List ℕ, (∀ p ∈ L, p.Prime) →
    2 ^ L.length * 10 ^ (L.map (digitSum 10)).sum ≤ L.prod ^ 9 := by
  intro L
  induction L with
  | nil =>
    intro _
    simp
  | cons p L ih =>
    intro h
    have hp := good_prime p (h p List.mem_cons_self)
    have hL := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.length_cons, List.map_cons, List.sum_cons, List.prod_cons]
    calc 2 ^ (L.length + 1) * 10 ^ (digitSum 10 p + (L.map (digitSum 10)).sum)
        = (2 * 10 ^ digitSum 10 p) * (2 ^ L.length * 10 ^ (L.map (digitSum 10)).sum) := by ring
      _ ≤ p ^ 9 * L.prod ^ 9 := Nat.mul_le_mul hp hL
      _ = (p * L.prod) ^ 9 := by ring

lemma omega_bound (m : ℕ) (hm : m ≠ 0) :
    2 ^ m.primeFactorsList.length * 10 ^ primeFactorsDigitSum 10 m ≤ m ^ 9 := by
  have h := list_bound m.primeFactorsList (fun p hp => Nat.prime_of_mem_primeFactorsList hp)
  rw [Nat.prod_primeFactorsList hm] at h
  exact h

lemma pfl_len_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).primeFactorsList.length = a.primeFactorsList.length + b.primeFactorsList.length := by
  rw [(Nat.perm_primeFactorsList_mul ha hb).length_eq, List.length_append]

lemma sp_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    primeFactorsDigitSum 10 (a * b) = primeFactorsDigitSum 10 a + primeFactorsDigitSum 10 b := by
  unfold primeFactorsDigitSum
  rw [((Nat.perm_primeFactorsList_mul ha hb).map _).sum_eq, List.map_append, List.sum_append]

lemma sp_small {p : ℕ} (hp : p.Prime) (hlt : p < 10) : primeFactorsDigitSum 10 p = p := by
  rw [primeFactorsDigitSum_of_prime 10 hp]
  unfold digitSum
  rw [Nat.digits_of_lt 10 p hp.ne_zero hlt]
  simp

lemma sp_two : primeFactorsDigitSum 10 2 = 2 := sp_small Nat.prime_two (by norm_num)

lemma sp_three : primeFactorsDigitSum 10 3 = 3 := sp_small Nat.prime_three (by norm_num)

lemma sp_five : primeFactorsDigitSum 10 5 = 5 := sp_small Nat.prime_five (by norm_num)

lemma sp_seven : primeFactorsDigitSum 10 7 = 7 := sp_small (by norm_num) (by norm_num)

lemma sp_four : primeFactorsDigitSum 10 4 = 4 := by
  have h := sp_mul (a := 2) (b := 2) (by norm_num) (by norm_num)
  rw [sp_two] at h
  exact h

lemma sp_eight : primeFactorsDigitSum 10 8 = 6 := by
  have h := sp_mul (a := 2) (b := 4) (by norm_num) (by norm_num)
  rw [sp_two, sp_four] at h
  exact h

lemma sp_fifteen : primeFactorsDigitSum 10 15 = 8 := by
  have h := sp_mul (a := 3) (b := 5) (by norm_num) (by norm_num)
  rw [sp_three, sp_five] at h
  exact h

lemma sp_ten : primeFactorsDigitSum 10 10 = 7 := by
  have h := sp_mul (a := 2) (b := 5) (by norm_num) (by norm_num)
  rw [sp_two, sp_five] at h
  exact h

lemma sp_pow_ten (b : ℕ) : primeFactorsDigitSum 10 (10 ^ b) = 7 * b := by
  induction b with
  | zero => simp [primeFactorsDigitSum]
  | succ k ih =>
    rw [pow_succ, sp_mul (by positivity) (by norm_num), ih, sp_ten]
    ring

lemma omega_pos {x : ℕ} (hx : 2 ≤ x) : 1 ≤ x.primeFactorsList.length := by
  have hmem : x.minFac ∈ x.primeFactorsList :=
    (Nat.mem_primeFactorsList (by omega)).mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd x⟩
  exact List.length_pos_of_mem hmem

/-- `10 ^ (2 ^ j) - 1` has at least `j + 2` prime factors. -/
lemma omega_rep (j : ℕ) : j + 2 ≤ (10 ^ 2 ^ j - 1).primeFactorsList.length := by
  induction j with
  | zero =>
    have h9 : (10 ^ 2 ^ 0 - 1 : ℕ) = 3 * 3 := by norm_num
    rw [h9, pfl_len_mul (by norm_num) (by norm_num), Nat.primeFactorsList_prime Nat.prime_three]
    simp
  | succ j ih =>
    have hX10 : 10 ≤ 10 ^ 2 ^ j := by
      calc 10 = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow j 2 (by norm_num))
    obtain ⟨Y, hY⟩ : ∃ Y, 10 ^ 2 ^ j = Y + 2 := ⟨10 ^ 2 ^ j - 2, by omega⟩
    have hsq : 10 ^ 2 ^ (j + 1) = (10 ^ 2 ^ j) * (10 ^ 2 ^ j) := by
      rw [pow_succ, pow_mul, sq]
    have hfac : 10 ^ 2 ^ (j + 1) - 1 = (10 ^ 2 ^ j - 1) * (10 ^ 2 ^ j + 1) := by
      rw [hsq, hY]
      have e : (Y + 2) * (Y + 2) = (Y + 1) * (Y + 2 + 1) + 1 := by ring
      rw [e]
      simp
    rw [hfac, pfl_len_mul (by omega) (by omega)]
    have h1 := omega_pos (x := 10 ^ 2 ^ j + 1) (by omega)
    omega

/-- For `j ≥ 25` the prime factors of `10 ^ (2 ^ j) - 1` have small total digit sum. -/
lemma sp_rep_bound (j : ℕ) (hj : 25 ≤ j) :
    primeFactorsDigitSum 10 (10 ^ 2 ^ j - 1) + 9 ≤ 9 * 2 ^ j := by
  have hpos : 10 ≤ 10 ^ 2 ^ j := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow j 2 (by norm_num))
  have hm0 : 10 ^ 2 ^ j - 1 ≠ 0 := by omega
  have h1 := omega_bound (10 ^ 2 ^ j - 1) hm0
  have h2 := omega_rep j
  have h3 : (10 ^ 2 ^ j - 1) ^ 9 < (10 ^ 2 ^ j) ^ 9 :=
    Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h27 : (10 : ℕ) ^ 8 ≤ 2 ^ 27 := by norm_num
  have hlen : 2 ^ 27 ≤ 2 ^ (10 ^ 2 ^ j - 1).primeFactorsList.length :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 10 ^ 8 ≤ 2 ^ (10 ^ 2 ^ j - 1).primeFactorsList.length := le_trans h27 hlen
  have h5 : 10 ^ (primeFactorsDigitSum 10 (10 ^ 2 ^ j - 1) + 8) < 10 ^ (9 * 2 ^ j) := by
    calc 10 ^ (primeFactorsDigitSum 10 (10 ^ 2 ^ j - 1) + 8)
        = 10 ^ 8 * 10 ^ primeFactorsDigitSum 10 (10 ^ 2 ^ j - 1) := by ring
      _ ≤ 2 ^ (10 ^ 2 ^ j - 1).primeFactorsList.length
            * 10 ^ primeFactorsDigitSum 10 (10 ^ 2 ^ j - 1) := Nat.mul_le_mul_right _ h4
      _ ≤ (10 ^ 2 ^ j - 1) ^ 9 := h1
      _ < (10 ^ 2 ^ j) ^ 9 := h3
      _ = 10 ^ (9 * 2 ^ j) := by ring
  have h6 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp h5
  omega

-- The construction

lemma smith_of (k s u b : ℕ) (hsu : s + u = 99) (hs : 1 ≤ s)
    (hdig : digitSum 10 s + digitSum 10 u = 18)
    (hsp : primeFactorsDigitSum 10 (s + 1) + primeFactorsDigitSum 10 (10 ^ (k + 2) - 1) + 7 * b
      = 9 * (k + 2)) :
    IsSmithNumber 10 ((s + 1) * (10 ^ (k + 2) - 1) * 10 ^ b) := by
  have hpow : 100 ≤ 10 ^ (k + 2) := by
    calc 100 = 10 ^ 2 := by norm_num
      _ ≤ 10 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm : 2 ≤ 10 ^ (k + 2) - 1 := by omega
  have hb : 1 ≤ 10 ^ b := Nat.one_le_pow b 10 (by norm_num)
  have hs2 : 2 ≤ s + 1 := by omega
  have hne1 : s + 1 ≠ 0 := by omega
  have hne2 : 10 ^ (k + 2) - 1 ≠ 0 := by omega
  have hne3 : (s + 1) * (10 ^ (k + 2) - 1) ≠ 0 := Nat.mul_ne_zero hne1 hne2
  have hne4 : 10 ^ b ≠ 0 := by positivity
  refine ⟨by norm_num, ⟨?_, ?_⟩, ?_⟩
  · have h : 2 * 2 * 1 ≤ (s + 1) * (10 ^ (k + 2) - 1) * 10 ^ b :=
      Nat.mul_le_mul (Nat.mul_le_mul hs2 hm) hb
    omega
  · rw [Nat.mul_assoc]
    apply Nat.not_prime_mul
    · omega
    · have h : 2 * 1 ≤ (10 ^ (k + 2) - 1) * 10 ^ b := Nat.mul_le_mul hm hb
      omega
  · rw [ds_mul_pow, ds_mul_rep s u k hsu, sp_mul hne3 hne4, sp_mul hne1 hne2, sp_pow_ten]
    omega

lemma exists_smith_aux (k : ℕ)
    (hbound : primeFactorsDigitSum 10 (10 ^ (k + 2) - 1) + 9 ≤ 9 * (k + 2))
    (t s u spt : ℕ) (ht : t = s + 1) (hsu : s + u = 99) (hs : 1 ≤ s)
    (hdig : digitSum 10 s + digitSum 10 u = 18)
    (hspt : primeFactorsDigitSum 10 t = spt) (hle : spt ≤ 8)
    (hmod : (9 * (k + 2) - primeFactorsDigitSum 10 (10 ^ (k + 2) - 1)) % 7 = spt % 7) :
    ∃ b : ℕ, IsSmithNumber 10 (t * (10 ^ (k + 2) - 1) * 10 ^ b) := by
  refine ⟨(9 * (k + 2) - primeFactorsDigitSum 10 (10 ^ (k + 2) - 1) - spt) / 7, ?_⟩
  subst ht
  apply smith_of k s u _ hsu hs hdig
  rw [hspt]
  omega

lemma exists_smith (j : ℕ) (hj : 25 ≤ j) : ∃ M : ℕ, j < M ∧ IsSmithNumber 10 M := by
  have hn : 4 ≤ 2 ^ j := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ j = k + 2 := ⟨2 ^ j - 2, by omega⟩
  have hbound := sp_rep_bound j hj
  rw [hk] at hbound
  have hjk : j < k + 2 := by
    have h : j < 2 ^ j := Nat.lt_two_pow_self
    omega
  have hkpow : k + 2 < 10 ^ (k + 2) := Nat.lt_pow_self (by norm_num)
  have hex : ∃ t b : ℕ, 1 ≤ t ∧ IsSmithNumber 10 (t * (10 ^ (k + 2) - 1) * 10 ^ b) := by
    have hcases : (9 * (k + 2) - primeFactorsDigitSum 10 (10 ^ (k + 2) - 1)) % 7 = 0 ∨
        (9 * (k + 2) - primeFactorsDigitSum 10 (10 ^ (k + 2) - 1)) % 7 = 1 ∨
        (9 * (k + 2) - primeFactorsDigitSum 10 (10 ^ (k + 2) - 1)) % 7 = 2 ∨
        (9 * (k + 2) - primeFactorsDigitSum 10 (10 ^ (k + 2) - 1)) % 7 = 3 ∨
        (9 * (k + 2) - primeFactorsDigitSum 10 (10 ^ (k + 2) - 1)) % 7 = 4 ∨
        (9 * (k + 2) - primeFactorsDigitSum 10 (10 ^ (k + 2) - 1)) % 7 = 5 ∨
        (9 * (k + 2) - primeFactorsDigitSum 10 (10 ^ (k + 2) - 1)) % 7 = 6 := by omega
    rcases hcases with h | h | h | h | h | h | h
    · obtain ⟨b, hb⟩ := exists_smith_aux k hbound 7 6 93 7 rfl (by norm_num) (by norm_num)
        (by norm_num [digitSum]) sp_seven (by norm_num) (by omega)
      exact ⟨7, b, by norm_num, hb⟩
    · obtain ⟨b, hb⟩ := exists_smith_aux k hbound 15 14 85 8 rfl (by norm_num) (by norm_num)
        (by norm_num [digitSum]) sp_fifteen (by norm_num) (by omega)
      exact ⟨15, b, by norm_num, hb⟩
    · obtain ⟨b, hb⟩ := exists_smith_aux k hbound 2 1 98 2 rfl (by norm_num) (by norm_num)
        (by norm_num [digitSum]) sp_two (by norm_num) (by omega)
      exact ⟨2, b, by norm_num, hb⟩
    · obtain ⟨b, hb⟩ := exists_smith_aux k hbound 3 2 97 3 rfl (by norm_num) (by norm_num)
        (by norm_num [digitSum]) sp_three (by norm_num) (by omega)
      exact ⟨3, b, by norm_num, hb⟩
    · obtain ⟨b, hb⟩ := exists_smith_aux k hbound 4 3 96 4 rfl (by norm_num) (by norm_num)
        (by norm_num [digitSum]) sp_four (by norm_num) (by omega)
      exact ⟨4, b, by norm_num, hb⟩
    · obtain ⟨b, hb⟩ := exists_smith_aux k hbound 5 4 95 5 rfl (by norm_num) (by norm_num)
        (by norm_num [digitSum]) sp_five (by norm_num) (by omega)
      exact ⟨5, b, by norm_num, hb⟩
    · obtain ⟨b, hb⟩ := exists_smith_aux k hbound 8 7 92 6 rfl (by norm_num) (by norm_num)
        (by norm_num [digitSum]) sp_eight (by norm_num) (by omega)
      exact ⟨8, b, by norm_num, hb⟩
  obtain ⟨t, b, ht, hS⟩ := hex
  refine ⟨t * (10 ^ (k + 2) - 1) * 10 ^ b, ?_, hS⟩
  have hb : 1 ≤ 10 ^ b := Nat.one_le_pow b 10 (by norm_num)
  have h : 1 * (10 ^ (k + 2) - 1) * 1 ≤ t * (10 ^ (k + 2) - 1) * 10 ^ b :=
    Nat.mul_le_mul (Nat.mul_le_mul ht le_rfl) hb
  omega

theorem main : {n : ℕ | IsSmithNumber 10 n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨M, hM, hS⟩ := exists_smith (max a 25) (le_max_right _ _)
  exact ⟨M, hS, lt_of_le_of_lt (le_max_left _ _) hM⟩

end OMA.Smith

theorem OMA.solution : type_of% @SmithNumber.mcdaniel_infinitely_many_smith_numbers :=
  OMA.Smith.main
