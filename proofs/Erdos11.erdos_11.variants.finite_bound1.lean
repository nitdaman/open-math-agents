import FormalConjectures.ErdosProblems.«11»

-- Problem: Erdős Problem 11 — finite bound1
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/11.lean:77 (declaration Erdos11.erdos_11.variants.finite_bound1)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA
def N : Nat := 10^7
def M (d m : Nat) : Nat := (2^(d*m) - 1) / (2^d - 1)
def good (q : Nat) : Bool :=
  decide (q ≤ 23) || (q % 2 != 0 && q % 3 != 0 && q % 5 != 0 && q % 7 != 0 && q % 11 != 0 &&
    q % 13 != 0 && q % 17 != 0 && q % 19 != 0 && q % 23 != 0)
def ns : Nat → Nat
  | 0 => 0
  | m+1 => (if good (m+2) = true then M ((m+2)*(m+2)) ((N-1) / ((m+2)*(m+2)) + 1) else 0) ||| ns m
def ns2 : Nat → Nat
  | 0 => 0
  | m+1 => (if good (m+2237) = true then 2^((m+2237)*(m+2237)) else 0) ||| ns2 m
def term (S l : Nat) : Nat := (S <<< (2^l)) ||| (2^(2^l) - 1)
def bad (S : Nat) : Nat → Nat
  | 0 => term S 0
  | l+1 => term S (l+1) &&& bad S l
def check (S : Nat) : Bool := (bad S 23 &&& (M 2 (N/2) <<< 1)) == 2
set_option maxRecDepth 100000 in
theorem bench : check (ns 2235 ||| ns2 926) = true := by decide +kernel

def T (d m : Nat) : Nat := ∑ j ∈ Finset.range m, 2^(d*j)

lemma T_identity (d m : Nat) : T d m * (2^d - 1) + 1 = 2^(d*m) := by
  have hx : 2^d - 1 + 1 = 2^d := Nat.sub_add_cancel Nat.one_le_two_pow
  have h := geom_sum_mul_add (2^d - 1) m
  rw [hx] at h
  have hT : T d m = ∑ i ∈ Finset.range m, (2^d)^i := by
    unfold T
    exact Finset.sum_congr rfl (fun j _ => by rw [← pow_mul])
  rw [hT, pow_mul]
  exact h

lemma two_pow_sub_pos (d : Nat) (hd : 0 < d) : 0 < 2^d - 1 := by
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hd
  simp only [pow_one] at this
  omega

lemma T_lt (d m : Nat) (hd : 0 < d) : T d m < 2^(d*m) := by
  have h := T_identity d m
  have h1 := two_pow_sub_pos d hd
  have h2 : T d m ≤ T d m * (2^d - 1) := Nat.le_mul_of_pos_right _ h1
  omega

lemma M_eq_T (d m : Nat) (hd : 0 < d) : M d m = T d m := by
  unfold M
  apply Nat.div_eq_of_eq_mul_left (two_pow_sub_pos d hd)
  have := T_identity d m
  rw [← this, Nat.add_sub_cancel]

lemma T_testBit (d : Nat) (hd : 0 < d) (m : Nat) : ∀ k, d ∣ k → k < d*m → (T d m).testBit k = true := by
  induction m with
  | zero => intro k _ hk; simp at hk
  | succ m ih =>
    intro k hdk hk
    have hsucc : T d (m+1) = 2^(d*m) + T d m := by
      unfold T
      rw [Finset.sum_range_succ, add_comm]
    rw [hsucc]
    by_cases hlt : k < d*m
    · rw [Nat.testBit_two_pow_add_gt hlt]
      exact ih k hdk hlt
    · obtain ⟨c, rfl⟩ := hdk
      have hc1 : m ≤ c := Nat.le_of_mul_le_mul_left (Nat.not_lt.mp hlt) hd
      have hc2 : c < m + 1 := Nat.lt_of_mul_lt_mul_left hk
      have hcm : c = m := by omega
      subst hcm
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt (T_lt d c hd)]
      rfl

lemma M_testBit (d m k : Nat) (hd : 0 < d) (hdk : d ∣ k) (hk : k < d*m) : (M d m).testBit k = true := by
  rw [M_eq_T d m hd]
  exact T_testBit d hd m k hdk hk

lemma good_of_prime (p : Nat) (hp : p.Prime) : good p = true := by
  by_cases h : p ≤ 23
  · simp [good, h]
  · have h2 : p % 2 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h0); omega
    have h3 : p % 3 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h0); omega
    have h5 : p % 5 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero h0); omega
    have h7 : p % 7 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 7 (Nat.dvd_of_mod_eq_zero h0); omega
    have h11 : p % 11 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 11 (Nat.dvd_of_mod_eq_zero h0); omega
    have h13 : p % 13 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 13 (Nat.dvd_of_mod_eq_zero h0); omega
    have h17 : p % 17 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 17 (Nat.dvd_of_mod_eq_zero h0); omega
    have h19 : p % 19 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 19 (Nat.dvd_of_mod_eq_zero h0); omega
    have h23 : p % 23 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 23 (Nat.dvd_of_mod_eq_zero h0); omega
    unfold good
    simp [h] <;> omega

lemma ns_testBit (m : Nat) : ∀ k q, 2 ≤ q → q ≤ m+1 → good q = true → q*q ∣ k → k < N →
    (ns m).testBit k = true := by
  induction m with
  | zero => intro k q h2 hq _ _ _; omega
  | succ m ih =>
    intro k q h2 hq hg hdk hk
    simp only [ns, Nat.testBit_or, Bool.or_eq_true]
    by_cases hq' : q = m+2
    · subst hq'
      left
      rw [if_pos hg]
      have hdpos : 0 < (m+2)*(m+2) := by positivity
      apply M_testBit _ _ _ hdpos hdk
      have h1 := Nat.lt_mul_div_succ (N-1) hdpos
      exact lt_of_le_of_lt (by omega) h1
    · right
      exact ih k q h2 (by omega) hg hdk hk

lemma ns2_testBit (m : Nat) : ∀ q, 2237 ≤ q → q ≤ 2236 + m → good q = true →
    (ns2 m).testBit (q*q) = true := by
  induction m with
  | zero => intro q h1 h2; omega
  | succ m ih =>
    intro q h1 h2 hg
    simp only [ns2, Nat.testBit_or, Bool.or_eq_true]
    by_cases hq' : q = m+2237
    · subst hq'
      left
      rw [if_pos hg]
      exact Nat.testBit_two_pow_self
    · right
      exact ih q h1 (by omega) hg

lemma S_testBit (k : Nat) (hk : k < N) (hs : ¬ Squarefree k) :
    (ns 2235 ||| ns2 926).testBit k = true := by
  have hk' : k < 10^7 := hk
  rw [Nat.testBit_or, Bool.or_eq_true]
  by_cases h0 : k = 0
  · subst h0
    left
    exact ns_testBit 2235 0 2 (by norm_num) (by norm_num) (by decide) (dvd_zero _) hk
  · rw [Nat.squarefree_iff_prime_squarefree] at hs
    push_neg at hs
    obtain ⟨p, hp, hpd⟩ := hs
    have hle : p*p ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hpd
    have hp3 : p ≤ 3162 := by nlinarith
    have hg : good p = true := good_of_prime p hp
    have hp2 : 2 ≤ p := hp.two_le
    by_cases hq4 : p ≤ 2236
    · left
      exact ns_testBit 2235 k p hp2 (by omega) hg hpd hk
    · have hq5 : 2237 ≤ p := by omega
      right
      obtain ⟨c, rfl⟩ := hpd
      have hc1 : c = 1 := by
        rcases c with _ | _ | c
        · simp at h0
        · rfl
        · nlinarith [Nat.mul_le_mul hq5 hq5]
      subst hc1
      rw [mul_one]
      exact ns2_testBit 926 p hq5 (by omega) hg

lemma term_false (S l n : Nat) (h : (term S l).testBit n = false) :
    2^l ≤ n ∧ S.testBit (n - 2^l) = false := by
  unfold term at h
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one] at h
  by_cases hl : 2^l ≤ n
  · refine ⟨hl, ?_⟩
    have hl' : ¬ n < 2^l := Nat.not_lt.mpr hl
    simpa [hl, hl'] using h
  · have hl' : n < 2^l := Nat.lt_of_not_le hl
    simp [hl, hl'] at h

lemma bad_false (S : Nat) : ∀ L n, (bad S L).testBit n = false →
    ∃ l, l ≤ L ∧ 2^l ≤ n ∧ S.testBit (n - 2^l) = false := by
  intro L
  induction L with
  | zero =>
    intro n h
    simp only [bad] at h
    obtain ⟨hl, hS⟩ := term_false S 0 n h
    exact ⟨0, le_refl 0, hl, hS⟩
  | succ L ih =>
    intro n h
    rw [bad, Nat.testBit_and] at h
    rcases Bool.and_eq_false_iff.mp h with h1 | h2
    · obtain ⟨hl, hS⟩ := term_false S (L+1) n h1
      exact ⟨L+1, le_refl _, hl, hS⟩
    · obtain ⟨l, hl, h3, h4⟩ := ih n h2
      exact ⟨l, by omega, h3, h4⟩

theorem main_odd (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n) :
    ∃ k l : ℕ, Squarefree k ∧ n = k + 2^l := by
  have hN : n < N := h
  have hN2 : 2 * (N/2) = N := by norm_num [N]
  have hb := bench
  unfold check at hb
  rw [beq_iff_eq] at hb
  have hbit := congrArg (fun x => Nat.testBit x n) hb
  obtain ⟨t, ht⟩ := hn
  have hM : (M 2 (N/2)).testBit (n-1) = true :=
    M_testBit 2 (N/2) (n-1) (by norm_num) ⟨t, by omega⟩ (by omega)
  have htwo : (2 : ℕ).testBit n = false := by
    apply Nat.testBit_eq_false_of_lt
    have : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at this
    omega
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, hM, htwo] at hbit
  have hbad : (bad (ns 2235 ||| ns2 926) 23).testBit n = false := by
    have hn1 : decide (n ≥ 1) = true := by simp; omega
    rw [hn1] at hbit
    simpa using hbit
  obtain ⟨l, _, hl, hS⟩ := bad_false _ 23 n hbad
  have hsq : Squarefree (n - 2^l) := by
    by_contra hsf
    have := S_testBit (n - 2^l) (lt_of_le_of_lt (Nat.sub_le n _) hN) hsf
    rw [hS] at this
    exact Bool.false_ne_true this
  exact ⟨n - 2^l, l, hsq, (Nat.sub_add_cancel hl).symm⟩

end OMA

theorem OMA.solution : type_of% @Erdos11.erdos_11.variants.finite_bound1 := by
  intro n hn h hn'
  exact OMA.main_odd n hn h hn'
