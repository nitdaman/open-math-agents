import FormalConjectures.Wikipedia.RefactorableNumber

-- Problem: Kennedy–Cooper Theorem (1990)
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/RefactorableNumber.lean:55 (declaration RefactorableNumber.refactorable_hasDensity_zero)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMAw2Refac

open Finset Filter

/-- `q` divides `n` exactly once. -/
def Ex (q n : ℕ) : Prop := q ∣ n ∧ ¬ q ^ 2 ∣ n

instance (q n : ℕ) : Decidable (Ex q n) := inferInstanceAs (Decidable (_ ∧ _))

noncomputable def f (q n : ℕ) : ℝ := if Ex q n then 1 / 2 else 1

noncomputable def w (S : Finset ℕ) (n : ℕ) : ℝ := ∏ q ∈ S, f q n

def X (S : Finset ℕ) (n : ℕ) : ℕ := #(S.filter fun q => Ex q n)

lemma pow_dvd_card (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) {n : ℕ} (hn : n ≠ 0) :
    2 ^ X S n ∣ #n.divisors := by
  rw [Nat.card_divisors hn]
  have hsub : S.filter (fun q => Ex q n) ⊆ n.primeFactors := by
    intro q hq
    rw [mem_filter] at hq
    exact Nat.mem_primeFactors.2 ⟨hS q hq.1, hq.2.1, hn⟩
  have h2 : ∏ q ∈ S.filter (fun q => Ex q n), (n.factorization q + 1) = 2 ^ X S n := by
    rw [X, ← prod_const]
    refine prod_congr rfl fun q hq => ?_
    rw [mem_filter] at hq
    have hp := hS q hq.1
    have h1 : 1 ≤ n.factorization q := (hp.pow_dvd_iff_le_factorization hn).1 (by simpa using hq.2.1)
    have h2 : ¬ 2 ≤ n.factorization q := fun h => hq.2.2 ((hp.pow_dvd_iff_le_factorization hn).2 h)
    omega
  rw [← h2]
  exact prod_dvd_prod_of_subset _ _ _ hsub

lemma w_eq (S : Finset ℕ) (n : ℕ) : w S n = (1 / 2 : ℝ) ^ X S n := by
  rw [w, X]
  simp only [f]
  rw [prod_ite, prod_const, prod_const_one, mul_one]

lemma f_mod (q n : ℕ) : f q n = f q (n % q ^ 2) := by
  have h1 : q ∣ q ^ 2 := dvd_pow_self q two_ne_zero
  unfold f
  exact if_congr (by simp only [Ex, Nat.dvd_mod_iff h1, Nat.dvd_mod_iff (dvd_refl (q ^ 2))]) rfl rfl

lemma w_mod (S : Finset ℕ) (Q : ℕ) (hQ : ∀ q ∈ S, q ^ 2 ∣ Q) (n : ℕ) : w S n = w S (n % Q) := by
  refine prod_congr rfl fun q hq => ?_
  rw [f_mod q n, f_mod q (n % Q), Nat.mod_mod_of_dvd n (hQ q hq)]

lemma crt_sum {a b : ℕ} (co : a.Coprime b) (ha : a ≠ 0) (hb : b ≠ 0) (F G : ℕ → ℝ)
    (hF : ∀ n, F n = F (n % a)) (hG : ∀ n, G n = G (n % b)) :
    ∑ n ∈ range (a * b), F n * G n = (∑ n ∈ range a, F n) * (∑ n ∈ range b, G n) := by
  rw [sum_mul_sum, ← sum_product']
  refine sum_nbij' (fun n => (n % a, n % b)) (fun p => (Nat.chineseRemainder co p.1 p.2 : ℕ))
    ?_ ?_ ?_ ?_ ?_
  · intro n _
    simp only [mem_product, mem_range]
    exact ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero ha), Nat.mod_lt _ (Nat.pos_of_ne_zero hb)⟩
  · intro p _
    simp only [mem_range]
    exact Nat.chineseRemainder_lt_mul co _ _ ha hb
  · intro n hn
    simp only [mem_range] at hn
    have h := Nat.chineseRemainder_modEq_unique co (Nat.mod_modEq n a).symm (Nat.mod_modEq n b).symm
    have hlt := Nat.chineseRemainder_lt_mul co (n % a) (n % b) ha hb
    unfold Nat.ModEq at h
    rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hlt] at h
    exact h.symm
  · intro p hp
    simp only [mem_product, mem_range] at hp
    have h1 : (Nat.chineseRemainder co p.1 p.2 : ℕ) % a = p.1 :=
      (show _ = _ from (Nat.chineseRemainder co p.1 p.2).prop.1).trans (Nat.mod_eq_of_lt hp.1)
    have h2 : (Nat.chineseRemainder co p.1 p.2 : ℕ) % b = p.2 :=
      (show _ = _ from (Nat.chineseRemainder co p.1 p.2).prop.2).trans (Nat.mod_eq_of_lt hp.2)
    exact Prod.ext h1 h2
  · intro n _
    simp only
    rw [← hF, ← hG]

/-- The period. -/
def Q (S : Finset ℕ) : ℕ := ∏ q ∈ S, q ^ 2

lemma dvd_Q {S : Finset ℕ} {q : ℕ} (hq : q ∈ S) : q ^ 2 ∣ Q S := dvd_prod_of_mem _ hq

lemma Q_pos (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) : 0 < Q S :=
  prod_pos fun q hq => pow_pos (hS q hq).pos 2

lemma period_sum (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∑ n ∈ range (Q S), w S n = ∏ q ∈ S, ∑ r ∈ range (q ^ 2), f q r := by
  induction S using Finset.induction_on with
  | empty => simp [Q, w]
  | insert q s hqs ih =>
    have hq : q.Prime := hS q (mem_insert_self q s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => hS p (mem_insert_of_mem hp)
    have co : (q ^ 2).Coprime (Q s) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      refine Nat.Coprime.pow _ _ ?_
      exact (Nat.coprime_primes hq (hs p hp)).2 (fun h => hqs (h ▸ hp))
    rw [prod_insert hqs, ← ih hs]
    have hQ : Q (insert q s) = q ^ 2 * Q s := by rw [Q, prod_insert hqs]; rfl
    rw [hQ]
    have hw : ∀ n, w (insert q s) n = f q n * w s n := fun n => by rw [w, prod_insert hqs]; rfl
    simp only [hw]
    exact crt_sum co (pow_ne_zero 2 hq.ne_zero) (Q_pos s hs).ne' _ _ (f_mod q)
      (w_mod s (Q s) (fun p hp => dvd_Q hp))

lemma multiple_sum (g : ℕ → ℝ) (P : ℕ) (hg : ∀ n, g n = g (n % P)) (M : ℕ) :
    ∑ n ∈ range (M * P), g n = M * ∑ n ∈ range P, g n := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    have : ∀ x ∈ range P, g (M * P + x) = g x := fun x _ => by
      rw [hg (M * P + x), hg x, show M * P + x = x + P * M by ring, Nat.add_mul_mod_self_left]
    rw [sum_congr rfl this]
    push_cast; ring

lemma f_nonneg (q n : ℕ) : 0 ≤ f q n := by unfold f; split_ifs <;> norm_num

lemma w_nonneg (S : Finset ℕ) (n : ℕ) : 0 ≤ w S n := prod_nonneg fun q _ => f_nonneg q n

lemma local_sum (q : ℕ) (hq : q.Prime) :
    ∑ r ∈ range (q ^ 2), f q r ≤ (q : ℝ) ^ 2 * (1 - 1 / (4 * q)) := by
  have hcard : q - 1 ≤ #((range (q ^ 2)).filter fun r => Ex q r) := by
    have : (Ico 1 q).image (fun j => q * j) ⊆ (range (q ^ 2)).filter fun r => Ex q r := by
      intro r hr
      simp only [mem_image, mem_Ico] at hr
      obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hr
      rw [mem_filter, mem_range]
      unfold Ex
      refine ⟨by rw [pow_two]; exact Nat.mul_lt_mul_of_pos_left hj2 hq.pos, dvd_mul_right q j, ?_⟩
      rintro h
      rw [pow_two] at h
      have := Nat.le_of_dvd (by omega) (Nat.dvd_of_mul_dvd_mul_left hq.pos h)
      omega
    have h2 := card_le_card this
    rw [card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hq.pos h)] at h2
    simpa using h2
  have hsplit := card_filter_add_card_filter_not (s := range (q ^ 2)) (fun r => Ex q r)
  rw [card_range] at hsplit
  simp only [f]
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hc : ((q : ℝ) - 1) ≤ (#((range (q ^ 2)).filter fun r => Ex q r) : ℝ) := by
    have : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub hq.one_le]; simp
    rw [← this]; exact_mod_cast hcard
  have hs : (#((range (q ^ 2)).filter fun r => Ex q r) : ℝ) +
      (#((range (q ^ 2)).filter fun r => ¬ Ex q r) : ℝ) = (q : ℝ) ^ 2 := by
    exact_mod_cast hsplit
  have hqpos : (0 : ℝ) < q := by linarith
  have : (q : ℝ) ^ 2 * (1 - 1 / (4 * q)) = (q : ℝ) ^ 2 - q / 4 := by
    field_simp
  rw [this]
  nlinarith

lemma card_dvd_le (p N : ℕ) (hp : 0 < p) :
    (#((range N).filter fun n => p ∣ n) : ℝ) ≤ N / p + 1 := by
  have hsub : (range N).filter (fun n => p ∣ n) ⊆
      insert 0 (((range N).filter fun e => p ∣ e + 1).image (· + 1)) := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · refine mem_insert_of_mem (mem_image.2 ⟨n - 1, ?_, by omega⟩)
      simp only [mem_filter, mem_range]
      refine ⟨by omega, ?_⟩
      rw [Nat.sub_add_cancel h]; exact hn.2
  have h1 := card_le_card hsub
  have h2 := card_insert_le 0 (((range N).filter fun e => p ∣ e + 1).image (· + 1))
  have h3 := card_image_le (s := (range N).filter fun e => p ∣ e + 1) (f := (· + 1))
  rw [Nat.card_multiples] at h3
  have h4 : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
  have : (#((range N).filter fun n => p ∣ n) : ℝ) ≤ ((N / p : ℕ) : ℝ) + 1 := by
    exact_mod_cast (h1.trans h2).trans (Nat.add_le_add_right h3 1)
  linarith

/-- Main counting bound. -/
lemma count_bound (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (k N : ℕ) :
    (#((range N).filter Nat.IsRefactorable) : ℝ) ≤
      N / 2 ^ k + 1 + 2 ^ k * ((N + Q S) * ∏ q ∈ S, (1 - 1 / (4 * (q : ℝ)))) := by
  classical
  have hsub : (range N).filter Nat.IsRefactorable ⊆
      (range N).filter (fun n => 2 ^ k ∣ n) ∪ (range N).filter (fun n => X S n < k) := by
    intro n hn
    simp only [mem_filter, mem_range, mem_union] at hn ⊢
    by_cases hX : X S n < k
    · exact Or.inr ⟨hn.1, hX⟩
    · left
      refine ⟨hn.1, ?_⟩
      have h1 := pow_dvd_card S hS (n := n) (by have := hn.2.1; omega)
      exact (pow_dvd_pow 2 (by omega)).trans (h1.trans hn.2.2)
  have hA := card_dvd_le (2 ^ k) N (by positivity)
  push_cast at hA
  -- second part
  have hB : (#((range N).filter (fun n => X S n < k)) : ℝ) ≤ 2 ^ k * ∑ n ∈ range N, w S n := by
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, mul_sum]
    refine sum_le_sum fun n _ => ?_
    split_ifs with h
    · rw [w_eq, Nat.cast_one]
      calc (1 : ℝ) = 2 ^ k * (1 / 2) ^ k := by rw [← mul_pow]; norm_num
        _ ≤ 2 ^ k * (1 / 2) ^ X S n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) h.le)
            (by positivity)
    · exact mul_nonneg (by positivity) (w_nonneg S n)
  have hQpos := Q_pos S hS
  have hMQ : (N : ℝ) ≤ ((N / Q S + 1) * Q S : ℕ) := by
    have := Nat.lt_div_mul_add (a := N) hQpos
    have h : N ≤ (N / Q S + 1) * Q S := by rw [Nat.add_mul, one_mul]; omega
    exact_mod_cast h
  have hMQ' : (((N / Q S + 1) * Q S : ℕ) : ℝ) ≤ N + Q S := by
    have h : (N / Q S + 1) * Q S ≤ N + Q S := by
      rw [Nat.add_mul, one_mul]; have := Nat.div_mul_le_self N (Q S); omega
    exact_mod_cast h
  have hC : ∑ n ∈ range N, w S n ≤ (N + Q S) * ∏ q ∈ S, (1 - 1 / (4 * (q : ℝ))) := by
    have h1 : ∑ n ∈ range N, w S n ≤ ∑ n ∈ range ((N / Q S + 1) * Q S), w S n :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by exact_mod_cast hMQ))
        (fun n _ _ => w_nonneg S n)
    rw [multiple_sum (w S) (Q S) (w_mod S (Q S) (fun q hq => dvd_Q hq)) (N / Q S + 1), period_sum S hS] at h1
    have h2 : ∏ q ∈ S, ∑ r ∈ range (q ^ 2), f q r ≤
        ∏ q ∈ S, ((q : ℝ) ^ 2 * (1 - 1 / (4 * q))) :=
      prod_le_prod (fun q _ => sum_nonneg fun r _ => f_nonneg q r)
        (fun q hq => local_sum q (hS q hq))
    rw [prod_mul_distrib] at h2
    have hQc : ∏ q ∈ S, ((q : ℝ) ^ 2) = (Q S : ℝ) := by simp [Q]
    rw [hQc] at h2
    have hPnn : 0 ≤ ∏ q ∈ S, (1 - 1 / (4 * (q : ℝ))) := by
      refine prod_nonneg fun q hq => ?_
      have : (2 : ℝ) ≤ q := by exact_mod_cast (hS q hq).two_le
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    calc ∑ n ∈ range N, w S n ≤ ((N / Q S + 1 : ℕ) : ℝ) * ∏ q ∈ S, ∑ r ∈ range (q ^ 2), f q r := h1
      _ ≤ ((N / Q S + 1 : ℕ) : ℝ) * (Q S * ∏ q ∈ S, (1 - 1 / (4 * (q : ℝ)))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (((N / Q S + 1) * Q S : ℕ) : ℝ) * ∏ q ∈ S, (1 - 1 / (4 * (q : ℝ))) := by push_cast; ring
      _ ≤ (N + Q S) * ∏ q ∈ S, (1 - 1 / (4 * (q : ℝ))) := mul_le_mul_of_nonneg_right hMQ' hPnn
  have h1 := card_le_card hsub
  have h2 := card_union_le ((range N).filter (fun n => 2 ^ k ∣ n))
    ((range N).filter (fun n => X S n < k))
  have h3 : (#((range N).filter Nat.IsRefactorable) : ℝ) ≤
      #((range N).filter (fun n => 2 ^ k ∣ n)) + #((range N).filter (fun n => X S n < k)) := by
    exact_mod_cast h1.trans h2
  have h4 := mul_le_mul_of_nonneg_left hC (by positivity : (0 : ℝ) ≤ 2 ^ k)
  linarith

end OMAw2Refac

theorem OMA.solution : type_of% @RefactorableNumber.refactorable_hasDensity_zero := by
  open OMAw2Refac Finset Filter in
  show Tendsto _ atTop _
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 4 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  set L : ℝ := 4 * 2 ^ k / ε with hL
  have hLpos : 0 < L := by positivity
  have hex : ∃ u : Finset ℕ,
      4 * L < ∑ x ∈ u, Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) x := by
    by_contra h
    push Not at h
    exact not_summable_one_div_on_primes
      (summable_of_sum_le (fun n => Set.indicator_nonneg (fun n _ => by positivity) n) h)
  obtain ⟨u, hu⟩ := hex
  set S := u.filter Nat.Prime with hSdef
  have hS : ∀ q ∈ S, q.Prime := fun q hq => (mem_filter.1 hq).2
  have hsum : ∑ x ∈ u, Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) x =
      ∑ q ∈ S, (1 : ℝ) / q := by
    rw [hSdef, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    simp [Set.indicator_apply]
  rw [hsum] at hu
  set P := ∏ q ∈ S, (1 - 1 / (4 * (q : ℝ))) with hPdef
  have hPnn : 0 ≤ P := by
    refine prod_nonneg fun q hq => ?_
    have : (2 : ℝ) ≤ q := by exact_mod_cast (hS q hq).two_le
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hP : P ≤ Real.exp (-(∑ q ∈ S, 1 / (4 * (q : ℝ)))) := by
    rw [← sum_neg_distrib, Real.exp_sum]
    refine prod_le_prod (fun q hq => ?_) (fun q _ => ?_)
    · have : (2 : ℝ) ≤ q := by exact_mod_cast (hS q hq).two_le
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    · have := Real.add_one_le_exp (-(1 / (4 * (q : ℝ)))); linarith
  have hs4 : ∑ q ∈ S, 1 / (4 * (q : ℝ)) = (1 / 4) * ∑ q ∈ S, (1 : ℝ) / q := by
    rw [mul_sum]; exact sum_congr rfl fun q _ => by ring
  have hexpL : Real.exp (-(∑ q ∈ S, 1 / (4 * (q : ℝ)))) ≤ Real.exp (-L) :=
    Real.exp_le_exp.2 (by rw [hs4]; linarith)
  have hexp2 : Real.exp (-L) < 1 / L := by
    rw [Real.exp_neg, inv_eq_one_div]
    have := Real.add_one_le_exp L
    exact one_div_lt_one_div_of_lt hLpos (by linarith)
  have h1L : 2 ^ k * (1 / L) = ε / 4 := by rw [hL]; field_simp
  have hkP : 2 ^ k * P < ε / 4 := by
    have : P < 1 / L := lt_of_le_of_lt (hP.trans hexpL) hexp2
    calc 2 ^ k * P < 2 ^ k * (1 / L) := mul_lt_mul_of_pos_left this h2k
      _ = ε / 4 := h1L
  set C : ℝ := 1 + 2 ^ k * (Q S * P) with hC
  have hCnn : 0 ≤ C := by positivity
  obtain ⟨N0, hN0⟩ := exists_nat_gt (4 * C / ε)
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNC : C < ε / 4 * N := by
    have h1 : (4 * C / ε : ℝ) < N := by
      have : ((N0 : ℕ) : ℝ) < N := by exact_mod_cast (show N0 < N by omega)
      linarith
    rw [div_lt_iff₀ hε] at h1
    linarith
  have e1 : ({n : ℕ | n.IsRefactorable} ∩ Set.univ ∩ Set.Iio N) =
      ↑((range N).filter Nat.IsRefactorable) := by
    ext n; simp [and_comm]
  have e2 : (Set.univ ∩ Set.Iio N : Set ℕ) = ↑(range N) := by ext; simp
  simp only [Set.partialDensity]
  rw [Real.dist_eq, sub_zero, e1, e2, Set.ncard_coe_finset, Set.ncard_coe_finset, card_range,
    abs_of_nonneg (by positivity), div_lt_iff₀ hNpos]
  have hb := count_bound S hS k N
  have e3 : (N : ℝ) / 2 ^ k = N * (1 / 2) ^ k := by rw [one_div_pow, mul_one_div]
  have e4 : (2 : ℝ) ^ k * ((N + Q S) * P) = (2 ^ k * P) * N + 2 ^ k * (Q S * P) := by ring
  have h5 : (N : ℝ) * (1 / 2) ^ k < N * (ε / 4) := mul_lt_mul_of_pos_left hk hNpos
  have h6 : (2 ^ k * P) * (N : ℝ) < (ε / 4) * N := mul_lt_mul_of_pos_right hkP hNpos
  rw [e3, e4] at hb
  linarith
