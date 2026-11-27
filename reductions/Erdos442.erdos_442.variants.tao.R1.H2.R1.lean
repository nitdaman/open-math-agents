import OMAReductions.R_Erdos442_erdos_442_variants_tao_R1
import Mathlib

-- Reduction Erdos442.erdos_442.variants.tao.R1.H2.R1 of step Erdos442.erdos_442.variants.tao.R1.H2
-- Credit: @dk8827

/-! Separate the analytic mass estimates from the finite divisor calculation.
The construction follows https://arxiv.org/abs/2407.04226v1. -/

namespace OMA.R_Erdos442_erdos_442_variants_tao_R1_H2_R1

open Filter
open scoped BigOperators

/-- A cutoff block whose small primes have reciprocal mass bounded below by
a fixed positive multiple of the square of the block index. -/
def H1 : Prop :=
  ∀ t : ℕ → ℝ, (∀ k, t k = Real.exp (Real.exp ((k : ℝ) ^ 2))) →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      ∃ k : ℕ, 1 ≤ k ∧ t k < x ∧ x ≤ t (k + 1) ∧
        let a := ∑ p ∈ Nat.primesLE ⌊t k⌋₊, (1 : ℝ) / p
        2 * (k : ℝ) ≤ a ∧ c * (k : ℝ) ^ 2 ≤ a

/-- The lower reciprocal-mass estimate for Tao's explicit set, in terms of the
small-prime reciprocal mass and the additional contribution of one large prime. -/
def H2 : Prop :=
  ∀ (t : ℕ → ℝ) (A : Set ℕ),
    (∀ k, t k = Real.exp (Real.exp ((k : ℝ) ^ 2))) →
    (∀ n, n ∈ A ↔ Squarefree n ∧ ∃ k : ℕ, 1 ≤ k ∧
      t k < (n : ℝ) ∧ (n : ℝ) ≤ t (k + 1) ∧
      (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ t k)).card ≤ k ∧
      (n.primeFactors.filter (fun p : ℕ => t k < (p : ℝ))).card ≤ 1) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x : ℝ in atTop,
      ∀ k : ℕ, 1 ≤ k → t k < x → x ≤ t (k + 1) →
        let S := (A ∩ Set.Icc 1 ⌊x⌋₊ : Set ℕ).toFinset
        let a := ∑ p ∈ Nat.primesLE ⌊t k⌋₊, (1 : ℝ) / p
        let Q := (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => t k < (p : ℝ))
        let q := ∑ p ∈ Q, (1 : ℝ) / p
        δ * (1 + q) * (a ^ k / (k.factorial : ℝ)) ≤ ∑ n ∈ S, (1 : ℝ) / n

theorem weighted_subsets_factorial_le {α : Type} (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (S : Finset α) (k : ℕ) :
    (k.factorial : ℝ) * (∑ T ∈ S.powersetCard k, ∏ a ∈ T, w a) ≤ (∑ a ∈ S, w a) ^ k := by
  classical
  induction S using Finset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => simp
    | succ k =>
      have h : (∅ : Finset α).powersetCard (k + 1) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      simp [h]
  | @insert a S ha ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hnot (T : Finset α) (hT : T ∈ S.powersetCard k) : a ∉ T :=
        fun ha' => ha ((Finset.mem_powersetCard.mp hT).1 ha')
      have hi : Set.InjOn (insert a) (↑(S.powersetCard k) : Set (Finset α)) := by
        intro T hT U hU he
        have he' := congrArg (fun t : Finset α => t.erase a) he
        rw [Finset.erase_insert (hnot T hT), Finset.erase_insert (hnot U hU)] at he'
        exact he'
      have hd : Disjoint (S.powersetCard (k + 1)) ((S.powersetCard k).image (insert a)) := by
        apply Finset.disjoint_left.mpr
        intro T hT hTa
        obtain ⟨U, hu, hEq⟩ := Finset.mem_image.mp hTa
        subst T
        exact ha ((Finset.mem_powersetCard.mp hT).1 (Finset.mem_insert_self _ _))
      have hsplit :
          (∑ T ∈ (insert a S).powersetCard (k + 1), ∏ b ∈ T, w b) =
            (∑ T ∈ S.powersetCard (k + 1), ∏ b ∈ T, w b) +
              w a * (∑ T ∈ S.powersetCard k, ∏ b ∈ T, w b) := by
        rw [Finset.powersetCard_succ_insert ha, Finset.sum_union hd, Finset.sum_image hi,
          Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun T hT => Finset.prod_insert (hnot T hT))
      let z := ∑ b ∈ S, w b
      have hz : 0 ≤ z := Finset.sum_nonneg (fun b _ => hw b)
      rw [hsplit, Finset.sum_insert ha, add_comm (w a)]
      calc
        _ = ((k + 1).factorial : ℝ) * (∑ T ∈ S.powersetCard (k + 1), ∏ b ∈ T, w b) +
              (((k + 1 : ℕ) : ℝ) * w a) *
                ((k.factorial : ℝ) * (∑ T ∈ S.powersetCard k, ∏ b ∈ T, w b)) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          ring
        _ ≤ z ^ (k + 1) + (((k + 1 : ℕ) : ℝ) * w a) * z ^ k :=
          add_le_add (ih (k + 1)) (mul_le_mul_of_nonneg_left (ih k) (mul_nonneg (by positivity) (hw a)))
        _ = z ^ (k + 1) + ((k + 1 : ℕ) : ℝ) * z ^ ((k + 1) - 1) * w a := by
          rw [Nat.add_sub_cancel]
          ring
        _ ≤ _ := pow_add_mul_le_add_pow hz (by linarith [hw a]) (k + 1)

lemma reciprocal_sum_le_factor_families (S P Q : Finset ℕ) (hPQ : Disjoint P Q)
    (F G : Finset (Finset ℕ)) (hS : ∀ n ∈ S, Squarefree n ∧ n.primeFactors ⊆ P ∪ Q ∧
        n.primeFactors ∩ P ∈ F ∧ n.primeFactors ∩ Q ∈ G) :
    ∑ n ∈ S, (1 : ℝ) / n ≤
      (∑ T ∈ F, ∏ p ∈ T, (1 : ℝ) / p) * (∑ U ∈ G, ∏ p ∈ U, (1 : ℝ) / p) := by
  classical
  let f (n : ℕ) := (n.primeFactors ∩ P, n.primeFactors ∩ Q)
  let w (r : Finset ℕ × Finset ℕ) : ℝ := (∏ p ∈ r.1, (1 : ℝ) / p) * (∏ p ∈ r.2, (1 : ℝ) / p)
  have parts_union (n : ℕ) (hn : n ∈ S) : (f n).1 ∪ (f n).2 = n.primeFactors := by
    change (n.primeFactors ∩ P) ∪ (n.primeFactors ∩ Q) = n.primeFactors
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr (hS n hn).2.1]
  have hf : Set.InjOn f ↑S := by
    intro n hn m hm hnm
    have h := congrArg (fun r : Finset ℕ × Finset ℕ => r.1 ∪ r.2) hnm
    change (f n).1 ∪ (f n).2 = (f m).1 ∪ (f m).2 at h
    rw [parts_union n hn, parts_union m hm] at h
    exact (Nat.prod_primeFactors_of_squarefree (hS n hn).1).symm.trans
      (h ▸ Nat.prod_primeFactors_of_squarefree (hS m hm).1)
  have hsub : S.image f ⊆ F ×ˢ G := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_product.mpr (hS n hn).2.2
  have hweight (n : ℕ) (hn : n ∈ S) : w (f n) = (1 : ℝ) / n := by
    have hdis : Disjoint (f n).1 (f n).2 :=
      hPQ.mono Finset.inter_subset_right Finset.inter_subset_right
    dsimp [w]
    rw [← Finset.prod_union hdis, parts_union n hn]
    have hp : (∏ p ∈ n.primeFactors, (p : ℝ)) = (n : ℝ) := by
      rw [← Nat.cast_prod (fun p : ℕ => p) n.primeFactors, Nat.prod_primeFactors_of_squarefree (hS n hn).1]
    simp only [one_div, Finset.prod_inv_distrib, hp]
  calc
    _ = ∑ n ∈ S, w (f n) := Finset.sum_congr rfl (fun n hn => (hweight n hn).symm)
    _ = ∑ a ∈ S.image f, w a := (Finset.sum_image hf).symm
    _ ≤ ∑ a ∈ F ×ˢ G, w a := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by
      dsimp [w]
      positivity)
    _ = _ := by
      rw [Finset.sum_product]
      simp only [w, ← Finset.mul_sum, ← Finset.sum_mul]

lemma powerset_le_eq_biUnion (P : Finset ℕ) (k : ℕ) :
    (P.powerset.filter (fun T => T.card ≤ k)) =
      (Finset.range (k + 1)).biUnion (fun j => P.powersetCard j) := by
  ext T
  rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion]
  constructor
  · rintro ⟨hsub, hcard⟩
    exact ⟨T.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hcard),
      Finset.mem_powersetCard.mpr ⟨hsub, rfl⟩⟩
  · rintro ⟨j, hj, hT⟩
    obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.mp hT
    exact ⟨hsub, hc ▸ Nat.le_of_lt_succ (Finset.mem_range.mp hj)⟩

lemma prime_weights_sum_le {P : Finset ℕ} (j : ℕ) :
    ∑ T ∈ P.powersetCard j, ∏ p ∈ T, (1 : ℝ) / p ≤
      (∑ p ∈ P, (1 : ℝ) / p) ^ j / (j.factorial : ℝ) := by
  have hf : 0 < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  apply (le_div_iff₀ hf).mpr
  rw [mul_comm]
  exact weighted_subsets_factorial_le (fun p : ℕ => (1 : ℝ) / p) (fun _ => by positivity) P j

lemma prime_weights_sum_at_most {P : Finset ℕ} (k : ℕ) :
    ∑ T ∈ P.powerset.filter (fun T => T.card ≤ k), ∏ p ∈ T, (1 : ℝ) / p ≤
      ∑ j ∈ Finset.range (k + 1), (∑ p ∈ P, (1 : ℝ) / p) ^ j / (j.factorial : ℝ) := by
  classical
  rw [powerset_le_eq_biUnion]
  have hd : (↑(Finset.range (k + 1)) : Set ℕ).PairwiseDisjoint (fun j => P.powersetCard j) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro T hTi hTj
    exact hij ((Finset.mem_powersetCard.mp hTi).2.symm.trans (Finset.mem_powersetCard.mp hTj).2)
  rw [Finset.sum_biUnion hd]
  exact Finset.sum_le_sum (fun j _ => prime_weights_sum_le j)

lemma reciprocal_exact_profile_bound (S P Q : Finset ℕ) (hPQ : Disjoint P Q)
    (j b : ℕ)
    (hS : ∀ n ∈ S, Squarefree n ∧ n.primeFactors ⊆ P ∪ Q ∧
      (n.primeFactors ∩ P).card = j ∧ (n.primeFactors ∩ Q).card = b) :
    ∑ n ∈ S, (1 : ℝ) / n ≤
      ((∑ p ∈ P, (1 : ℝ) / p) ^ j / (j.factorial : ℝ)) *
        ((∑ p ∈ Q, (1 : ℝ) / p) ^ b / (b.factorial : ℝ)) := by
  classical
  calc
    _ ≤ (∑ T ∈ P.powersetCard j, ∏ p ∈ T, (1 : ℝ) / p) *
        (∑ U ∈ Q.powersetCard b, ∏ p ∈ U, (1 : ℝ) / p) := by
      apply reciprocal_sum_le_factor_families S P Q hPQ
      intro n hn
      obtain ⟨hsf, hsub, hP, hQ⟩ := hS n hn
      exact ⟨hsf, hsub, Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hP⟩,
        Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hQ⟩⟩
    _ ≤ _ := mul_le_mul (prime_weights_sum_le j) (prime_weights_sum_le b)
      (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)

lemma reciprocal_bounded_profile (S P Q : Finset ℕ) (hPQ : Disjoint P Q)
    (j b : ℕ)
    (hS : ∀ n ∈ S, Squarefree n ∧ n.primeFactors ⊆ P ∪ Q ∧
      (n.primeFactors ∩ P).card ≤ j ∧ (n.primeFactors ∩ Q).card ≤ b) :
    ∑ n ∈ S, (1 : ℝ) / n ≤
      (∑ l ∈ Finset.range (j + 1), (∑ p ∈ P, (1 : ℝ) / p) ^ l / (l.factorial : ℝ)) *
        (∑ l ∈ Finset.range (b + 1), (∑ p ∈ Q, (1 : ℝ) / p) ^ l / (l.factorial : ℝ)) := by
  classical
  calc
    _ ≤ (∑ T ∈ P.powerset.filter (fun T => T.card ≤ j), ∏ p ∈ T, (1 : ℝ) / p) *
        (∑ U ∈ Q.powerset.filter (fun U => U.card ≤ b), ∏ p ∈ U, (1 : ℝ) / p) := by
      apply reciprocal_sum_le_factor_families S P Q hPQ
      intro n hn
      obtain ⟨hsf, hsub, hP, hQ⟩ := hS n hn
      exact ⟨hsf, hsub,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, hP⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, hQ⟩⟩
    _ ≤ _ := mul_le_mul (prime_weights_sum_at_most j) (prime_weights_sum_at_most b)
      (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)

lemma divisor_profile_of_support (P Q : Finset ℕ) {n d k : ℕ}
    (hn : Squarefree n) (hd : d ∣ n) (hsub : n.primeFactors ⊆ P ∪ Q)
    (hP : (n.primeFactors ∩ P).card ≤ k) (hQ : (n.primeFactors ∩ Q).card ≤ 1) :
    Squarefree d ∧ d.primeFactors ⊆ P ∪ Q ∧
      (d.primeFactors ∩ P).card ≤ k ∧ (d.primeFactors ∩ Q).card ≤ 1 := by
  have hm := Nat.primeFactors_mono hd hn.ne_zero
  exact ⟨hn.squarefree_of_dvd hd, hm.trans hsub,
    (Finset.card_le_card (Finset.inter_subset_inter_right hm)).trans hP,
    (Finset.card_le_card (Finset.inter_subset_inter_right hm)).trans hQ⟩

lemma quotient_profile_of_support (P Q : Finset ℕ) {n d k : ℕ}
    (hn : Squarefree n) (hd : d ∣ n) (hsub : n.primeFactors ⊆ P ∪ Q)
    (hP : (n.primeFactors ∩ P).card ≤ k) (hQ : (n.primeFactors ∩ Q).card ≤ 1) :
    Squarefree (n / d) ∧ (n / d).primeFactors ⊆ P ∪ Q ∧
      ((n / d).primeFactors ∩ P).card ≤ k - (d.primeFactors ∩ P).card ∧
      ((n / d).primeFactors ∩ Q).card ≤ 1 - (d.primeFactors ∩ Q).card := by
  have hd0 : d ≠ 0 := by
    intro he
    subst d
    exact hn.ne_zero (zero_dvd_iff.mp hd)
  have hdiff : (n / d).primeFactors = n.primeFactors \ d.primeFactors := by
    simpa only [Nat.gcd_eq_right_iff_dvd.mpr hd] using Nat.primeFactors_div_gcd hn hd0
  have hcount (T : Finset ℕ) : ((n / d).primeFactors ∩ T).card =
      (n.primeFactors ∩ T).card - (d.primeFactors ∩ T).card := by
    have hm : d.primeFactors ∩ T ⊆ n.primeFactors ∩ T :=
      Finset.inter_subset_inter_right (Nat.primeFactors_mono hd hn.ne_zero)
    have he : (n / d).primeFactors ∩ T = (n.primeFactors ∩ T) \ (d.primeFactors ∩ T) := by
      ext x
      rw [hdiff]
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      tauto
    rw [he, Finset.card_sdiff_of_subset hm]
  refine ⟨hn.squarefree_of_dvd (Nat.div_dvd_of_dvd hd), ?_, ?_, ?_⟩
  · rw [hdiff]
    exact Finset.sdiff_subset.trans hsub
  · rw [hcount]
    exact Nat.sub_le_sub_right hP _
  · rw [hcount]
    exact Nat.sub_le_sub_right hQ _

lemma truncated_exponential_le {a : ℝ} (ha : 0 < a) (k : ℕ) (hk : 2 * (k : ℝ) ≤ a) :
    ∑ j ∈ Finset.range (k + 1), a ^ j / (j.factorial : ℝ) ≤ 2 * (a ^ k / (k.factorial : ℝ)) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hk' : 2 * (k : ℝ) ≤ a := by
      rw [Nat.cast_succ] at hk
      linarith
    have hstep : 2 * (a ^ k / (k.factorial : ℝ)) ≤ a ^ (k + 1) / ((k + 1).factorial : ℝ) := by
      have hfactorial : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
      have hfactorial' : 0 < ((k + 1).factorial : ℝ) := by exact_mod_cast (k + 1).factorial_pos
      apply (le_div_iff₀ hfactorial').mpr
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      have heq : 2 * (a ^ k / (k.factorial : ℝ)) * (((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ)) =
          a ^ k * (2 * ((k + 1 : ℕ) : ℝ)) := by field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_left hk (by positivity)
    rw [Finset.sum_range_succ]
    linarith [ih hk']

lemma factorial_convolution_bound {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1),
      (a ^ j / (j.factorial : ℝ)) * (a ^ (k - j) / ((k - j).factorial : ℝ)) ^ 2 ≤
    (a ^ k / (k.factorial : ℝ)) ^ 2 * Real.exp ((k : ℝ) ^ 2 / a) := by
  let y := a ^ k / (k.factorial : ℝ)
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hterm (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
      a ^ j / (j.factorial : ℝ) * (a ^ (k - j) / ((k - j).factorial : ℝ)) ^ 2 ≤
        y ^ 2 * (((k : ℝ) ^ 2 / a) ^ j / (j.factorial : ℝ)) := by
    have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hkw : (k.descFactorial j : ℝ) ≤ (k : ℝ) ^ j := by exact_mod_cast k.descFactorial_le_pow j
    have hf : ((k - j).factorial : ℝ) * (k.descFactorial j : ℝ) = (k.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hjk
    have hp : a ^ j * a ^ (k - j) = a ^ k := by rw [← pow_add, Nat.add_sub_of_le hjk]
    have hf0 : ((k - j).factorial : ℝ) ≠ 0 := by exact_mod_cast (k - j).factorial_pos.ne'
    have hk0 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_pos.ne'
    have hr : a ^ (k - j) / ((k - j).factorial : ℝ) =
        y * ((k.descFactorial j : ℝ) / a ^ j) := by
      dsimp [y]
      field_simp
      rw [← hp, ← hf]
      ring
    have hpos : 0 ≤ a ^ (k - j) / ((k - j).factorial : ℝ) := by positivity
    calc
      _ ≤ a ^ j / (j.factorial : ℝ) * (y * ((k : ℝ) ^ j / a ^ j)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ hpos
        rw [hr]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hkw (by positivity)) hy
      _ = _ := by
        have hpow : ((k : ℝ) ^ 2 / a) ^ j = ((k : ℝ) ^ j) ^ 2 / a ^ j := by
          rw [div_pow, ← pow_mul, Nat.mul_comm 2 j, pow_mul]
        have hj0 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_pos.ne'
        rw [hpow, mul_pow, div_pow]
        field_simp
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1), y ^ 2 * (((k : ℝ) ^ 2 / a) ^ j / (j.factorial : ℝ)) :=
      Finset.sum_le_sum hterm
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by positivity) _) (by positivity)

lemma finite_divisor_energy (S D P Q : Finset ℕ) (k : ℕ)
    (hPQ : Disjoint P Q)
    (hS : ∀ n ∈ S, Squarefree n ∧ n.primeFactors ⊆ P ∪ Q ∧
      (n.primeFactors ∩ P).card ≤ k ∧ (n.primeFactors ∩ Q).card ≤ 1)
    (ha : 0 < ∑ p ∈ P, (1 : ℝ) / p)
    (hk : 2 * (k : ℝ) ≤ ∑ p ∈ P, (1 : ℝ) / p) :
    let a := ∑ p ∈ P, (1 : ℝ) / p
    let q := ∑ p ∈ Q, (1 : ℝ) / p
    ∑ d ∈ D, (d : ℝ) * (∑ n ∈ S.filter (fun n => d ∣ n), (1 : ℝ) / n) ^ 2 ≤
      8 * (1 + q) ^ 2 * (a ^ k / (k.factorial : ℝ)) ^ 2 * Real.exp ((k : ℝ) ^ 2 / a) := by
  classical
  dsimp
  let a := ∑ p ∈ P, (1 : ℝ) / p
  let q := ∑ p ∈ Q, (1 : ℝ) / p
  let w (d : ℕ) := ∑ n ∈ S.filter (fun n => d ∣ n), (1 : ℝ) / n
  let live := D.filter (fun d => ∃ n ∈ S, d ∣ n)
  let cls (d : ℕ) := ((d.primeFactors ∩ P).card, (d.primeFactors ∩ Q).card)
  let B := Finset.range (k + 1) ×ˢ Finset.range 2
  let K (j b : ℕ) : ℝ := 2 * (a ^ (k - j) / ((k - j).factorial : ℝ)) *
    (1 + ((1 - b : ℕ) : ℝ) * q)
  have hq : 0 ≤ q := Finset.sum_nonneg (fun _ _ => by positivity)
  have live_profile (d : ℕ) (hd : d ∈ live) : Squarefree d ∧ d.primeFactors ⊆ P ∪ Q ∧
      (cls d).1 ≤ k ∧ (cls d).2 ≤ 1 := by
    obtain ⟨n, hn, hdiv⟩ := (Finset.mem_filter.mp hd).2
    obtain ⟨hnf, hsub, hP, hQ⟩ := hS n hn
    exact divisor_profile_of_support P Q hnf hdiv hsub hP hQ
  have hcls (d : ℕ) (hd : d ∈ live) : cls d ∈ B := by
    obtain ⟨_, _, hj, hb⟩ := live_profile d hd
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hj), Finset.mem_range.mpr (Nat.lt_succ_of_le hb)⟩
  have hpoint (d : ℕ) (hd : d ∈ live) :
      (d : ℝ) * w d ^ 2 ≤ (1 : ℝ) / d * K (cls d).1 (cls d).2 ^ 2 := by
    obtain ⟨hsf, _, hj, hb⟩ := live_profile d hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hsf.ne_zero
    let A := S.filter (fun n => d ∣ n)
    let T := A.image (fun n => n / d)
    have hT (m : ℕ) (hm : m ∈ T) :
        Squarefree m ∧ m.primeFactors ⊆ P ∪ Q ∧
        (m.primeFactors ∩ P).card ≤ k - (cls d).1 ∧
        (m.primeFactors ∩ Q).card ≤ 1 - (cls d).2 := by
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨hn, hdiv⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnf, hsub, hP, hQ⟩ := hS n hn
      exact quotient_profile_of_support P Q hnf hdiv hsub hP hQ
    have hmass : w d = (1 : ℝ) / d * (∑ m ∈ T, (1 : ℝ) / m) := by
      have hinj : Set.InjOn (fun n : ℕ => n / d) (↑A : Set ℕ) := by
        intro n hn m hm h
        calc
          n = n / d * d := (Nat.div_mul_cancel (Finset.mem_filter.mp hn).2).symm
          _ = m / d * d := congrArg (fun a : ℕ => a * d) h
          _ = m := Nat.div_mul_cancel (Finset.mem_filter.mp hm).2
      dsimp [w, T]
      rw [Finset.sum_image hinj, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have he : ((n / d : ℕ) : ℝ) * (d : ℝ) = (n : ℝ) := by
        exact_mod_cast Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
      have hq0 : ((n / d : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (hT (n / d) (Finset.mem_image_of_mem _ hn)).1.ne_zero
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (hS n (Finset.mem_filter.mp hn).1).1.ne_zero
      field_simp
      nlinarith only [he]
    have hTmass := reciprocal_bounded_profile T P Q hPQ (k - (cls d).1) (1 - (cls d).2) hT
    have hsmall : 2 * ((k - (cls d).1 : ℕ) : ℝ) ≤ a := by
      have hle : ((k - (cls d).1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k (cls d).1
      linarith
    have hsumQ :
        (∑ l ∈ Finset.range (1 - (cls d).2 + 1), q ^ l / (l.factorial : ℝ)) =
          1 + ((1 - (cls d).2 : ℕ) : ℝ) * q := by
      obtain h | h : (cls d).2 = 0 ∨ (cls d).2 = 1 := by omega
      · rw [h]
        norm_num [Finset.sum_range_succ, add_comm]
      · rw [h]
        norm_num [Finset.sum_range_succ]
    have hbound : (∑ m ∈ T, (1 : ℝ) / m) ≤ K (cls d).1 (cls d).2 := by
      change _ ≤ (∑ l ∈ Finset.range (k - (cls d).1 + 1), a ^ l / (l.factorial : ℝ)) *
        (∑ l ∈ Finset.range (1 - (cls d).2 + 1), q ^ l / (l.factorial : ℝ)) at hTmass
      rw [hsumQ] at hTmass
      exact hTmass.trans (mul_le_mul_of_nonneg_right
        (truncated_exponential_le ha _ hsmall) (by positivity))
    rw [hmass, mul_pow]
    calc
      _ = (1 : ℝ) / d * (∑ m ∈ T, (1 : ℝ) / m) ^ 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) hbound _) (by positivity)
  have hcut : ∑ d ∈ D, (d : ℝ) * w d ^ 2 = ∑ d ∈ live, (d : ℝ) * w d ^ 2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    split
    · rfl
    · rename_i h
      have hz : w d = 0 := Finset.sum_eq_zero (fun n hn => by
        obtain ⟨hn, hdiv⟩ := Finset.mem_filter.mp hn
        exact (h ⟨n, hn, hdiv⟩).elim)
      simp [hz]
  have hprofile (z : ℕ × ℕ) (hz : z ∈ B) :
      ∑ d ∈ live.filter (fun d => cls d = z), (1 : ℝ) / d ≤
        (a ^ z.1 / (z.1.factorial : ℝ)) * (q ^ z.2 / (z.2.factorial : ℝ)) := by
    apply reciprocal_exact_profile_bound _ P Q hPQ z.1 z.2
    intro d hd
    obtain ⟨hl, hc⟩ := Finset.mem_filter.mp hd
    obtain ⟨hsf, hsub, h1, h2⟩ := live_profile d hl
    exact ⟨hsf, hsub, congrArg Prod.fst hc, congrArg Prod.snd hc⟩
  change (∑ d ∈ D, (d : ℝ) * w d ^ 2) ≤
    8 * (1 + q) ^ 2 * (a ^ k / (k.factorial : ℝ)) ^ 2 * Real.exp ((k : ℝ) ^ 2 / a)
  rw [hcut]
  have hsum :
      ∑ d ∈ live, (d : ℝ) * w d ^ 2 ≤
        ∑ z ∈ B, (a ^ z.1 / (z.1.factorial : ℝ)) * (q ^ z.2 / (z.2.factorial : ℝ)) * K z.1 z.2 ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hcls]
    apply Finset.sum_le_sum
    intro z hz
    calc
      _ ≤ ∑ d ∈ live.filter (fun d => cls d = z), (1 : ℝ) / d * K z.1 z.2 ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hd, he⟩ := Finset.mem_filter.mp hd
        simpa only [he] using hpoint d hd
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hprofile z hz) (sq_nonneg _)
  apply hsum.trans
  rw [Finset.sum_product]
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1),
        (8 * (1 + q) ^ 2) * ((a ^ j / (j.factorial : ℝ)) *
          (a ^ (k - j) / ((k - j).factorial : ℝ)) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      have hq' : q ≤ (1 + q) ^ 2 := by nlinarith only [hq, sq_nonneg q]
      have hscale : 0 ≤ 4 * (a ^ j / (j.factorial : ℝ)) *
          (a ^ (k - j) / ((k - j).factorial : ℝ)) ^ 2 := by positivity
      have hp : 4 * (a ^ j / (j.factorial : ℝ)) * (a ^ (k - j) / ((k - j).factorial : ℝ)) ^ 2 *
          ((1 + q) ^ 2 + q) ≤ 4 * (a ^ j / (j.factorial : ℝ)) *
          (a ^ (k - j) / ((k - j).factorial : ℝ)) ^ 2 * (2 * (1 + q) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith only [hq']) hscale
      calc
        _ = 4 * (a ^ j / (j.factorial : ℝ)) *
            (a ^ (k - j) / ((k - j).factorial : ℝ)) ^ 2 * ((1 + q) ^ 2 + q) := by
          norm_num [Finset.sum_range_succ, K]
          ring
        _ ≤ 4 * (a ^ j / (j.factorial : ℝ)) *
            (a ^ (k - j) / ((k - j).factorial : ℝ)) ^ 2 * (2 * (1 + q) ^ 2) := hp
        _ = _ := by ring
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      calc
        _ ≤ (8 * (1 + q) ^ 2) * ((a ^ k / (k.factorial : ℝ)) ^ 2 * Real.exp ((k : ℝ) ^ 2 / a)) :=
          mul_le_mul_of_nonneg_left (factorial_convolution_bound ha k) (by positivity)
        _ = _ := by ring

lemma tao_support_at_cutoff (t : ℕ → ℝ) (ht : StrictMono t) (A : Set ℕ)
    (hA : ∀ n, n ∈ A ↔ Squarefree n ∧ ∃ k : ℕ, 1 ≤ k ∧
      t k < (n : ℝ) ∧ (n : ℝ) ≤ t (k + 1) ∧
      (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ t k)).card ≤ k ∧
      (n.primeFactors.filter (fun p : ℕ => t k < (p : ℝ))).card ≤ 1)
    (x : ℝ) (k : ℕ) (hx : x ≤ t (k + 1)) (hx0 : 0 ≤ x)
    (n : ℕ) (hn : n ∈ (A ∩ Set.Icc 1 ⌊x⌋₊ : Set ℕ)) :
    let P := Nat.primesLE ⌊t k⌋₊
    let Q := (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => t k < (p : ℝ))
    Squarefree n ∧ n.primeFactors ⊆ P ∪ Q ∧
      (n.primeFactors ∩ P).card ≤ k ∧ (n.primeFactors ∩ Q).card ≤ 1 := by
  classical
  dsimp
  let P := Nat.primesLE ⌊t k⌋₊
  let Q := (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => t k < (p : ℝ))
  obtain ⟨hsf, i, hi, hil, hiu, hiP, hiQ⟩ := (hA n).mp hn.1
  have hntop : (n : ℝ) ≤ x := (Nat.cast_le.mpr hn.2.2).trans (Nat.floor_le hx0)
  have hi_le : i ≤ k := by
    by_contra! h
    exact (not_lt_of_ge (hntop.trans (hx.trans (ht.monotone (by omega))))) hil
  have Pmem (p : ℕ) (hp : p ∈ n.primeFactors) : p ∈ P ↔ (p : ℝ) ≤ t k := by
    have hp' := (Nat.mem_primeFactors.mp hp).1
    rw [Nat.mem_primesLE, and_iff_left hp', Nat.le_floor_iff' hp'.ne_zero]
  have Qmem (p : ℕ) (hp : p ∈ n.primeFactors) : p ∈ Q ↔ t k < (p : ℝ) := by
    obtain ⟨hp', hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    have hle := (Nat.le_of_dvd (Nat.pos_of_ne_zero hsf.ne_zero) hdvd).trans hn.2.2
    rw [Finset.mem_filter, Nat.mem_primesLE, and_iff_right ⟨hle, hp'⟩]
  have hsub : n.primeFactors ⊆ P ∪ Q := by
    intro p hp
    rcases le_or_gt (p : ℝ) (t k) with h | h
    · exact Finset.mem_union_left _ ((Pmem p hp).mpr h)
    · exact Finset.mem_union_right _ ((Qmem p hp).mpr h)
  have hPf : n.primeFactors ∩ P = n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ t k) := by
    ext p
    rw [Finset.mem_inter, Finset.mem_filter]
    exact and_congr_right (Pmem p)
  have hQf : n.primeFactors ∩ Q = n.primeFactors.filter (fun p : ℕ => t k < (p : ℝ)) := by
    ext p
    simpa only [Finset.mem_inter, Finset.mem_filter] using (and_congr_right (Qmem p))
  refine ⟨hsf, hsub, ?_⟩
  by_cases he : i = k
  · subst i
    exact ⟨by rw [hPf]; exact hiP, by rw [hQf]; exact hiQ⟩
  have hin : i + 1 ≤ k := by omega
  have hncut : (n : ℝ) ≤ t k := hiu.trans (ht.monotone hin)
  have hncard : n.primeFactors.card ≤ k := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := n.primeFactors) (p := fun p : ℕ => (p : ℝ) ≤ t i)
    simp only [not_le] at hsum
    omega
  refine ⟨(Finset.card_le_card Finset.inter_subset_left).trans hncard, ?_⟩
  rw [hQf]
  have hempty : n.primeFactors.filter (fun p : ℕ => t k < (p : ℝ)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp, hpgt⟩ := Finset.mem_filter.mp hp
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hsf.ne_zero) (Nat.mem_primeFactors.mp hp).2.1
    exact (not_lt_of_ge ((Nat.cast_le.mpr hle).trans hncut)) hpgt
  rw [hempty]
  decide

theorem main : H1 → H2 → OMA.R_Erdos442_erdos_442_variants_tao_R1.H2 := by
  intro hprime hmass t A hT hA
  classical
  have ht : StrictMono t := by
    intro i j hij
    rw [hT i, hT j]
    apply Real.exp_lt_exp.mpr
    apply Real.exp_lt_exp.mpr
    exact pow_lt_pow_left₀ (by exact_mod_cast hij) (by positivity) (by decide)
  have htpos (k : ℕ) : 0 < t k := by
    rw [hT]
    positivity
  obtain ⟨c, hc, hblocks⟩ := hprime t hT
  obtain ⟨δ, hδ, hlower⟩ := hmass t A hT hA
  let C := 8 * Real.exp (1 / c) / δ ^ 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hblocks, hlower] with x hx hxmass
  obtain ⟨k, hk, hkx, hxk, hka, hca⟩ := hx
  let S := (A ∩ Set.Icc 1 ⌊x⌋₊ : Set ℕ).toFinset
  let P := Nat.primesLE ⌊t k⌋₊
  let Q := (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => t k < (p : ℝ))
  let a := ∑ p ∈ P, (1 : ℝ) / p
  let q := ∑ p ∈ Q, (1 : ℝ) / p
  let y := (1 + q) * (a ^ k / (k.factorial : ℝ))
  have ha : 0 < a := by
    have h : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    change 2 * (k : ℝ) ≤ a at hka
    linarith
  have hq : 0 ≤ q := Finset.sum_nonneg (fun _ _ => by positivity)
  have hδy : δ * y ≤ ∑ n ∈ S, (1 : ℝ) / n := by
    simpa only [y, mul_assoc] using hxmass k hk hkx hxk
  have hPQ : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq'
    have hp' : p ≤ ⌊t k⌋₊ := (Nat.mem_primesLE.mp hp).1
    have hle : (p : ℝ) ≤ t k := (Nat.cast_le.mpr hp').trans (Nat.floor_le (htpos k).le)
    exact (not_lt_of_ge hle) (Finset.mem_filter.mp hq').2
  have hS (n : ℕ) (hn : n ∈ S) : Squarefree n ∧ n.primeFactors ⊆ P ∪ Q ∧
      (n.primeFactors ∩ P).card ≤ k ∧ (n.primeFactors ∩ Q).card ≤ 1 :=
    tao_support_at_cutoff t ht A hA x k hxk ((htpos k).trans hkx).le n (Set.mem_toFinset.mp hn)
  have he : Real.exp ((k : ℝ) ^ 2 / a) ≤ Real.exp (1 / c) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff₀ ha hc).mpr
    simpa only [one_mul, mul_comm] using hca
  have hδy0 : 0 ≤ δ * y := by dsimp [y]; positivity
  have hscaled : (δ * y) ^ 2 ≤ (∑ n ∈ S, (1 : ℝ) / n) ^ 2 :=
    pow_le_pow_left₀ hδy0 hδy _
  change (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (d : ℝ) * (∑ n ∈ S.filter (fun n => d ∣ n), (1 : ℝ) / n) ^ 2) ≤
    C * (∑ n ∈ S, (1 : ℝ) / n) ^ 2
  calc
    _ ≤ 8 * (1 + q) ^ 2 * (a ^ k / (k.factorial : ℝ)) ^ 2 * Real.exp ((k : ℝ) ^ 2 / a) :=
      finite_divisor_energy S _ P Q k hPQ hS ha hka
    _ ≤ 8 * (1 + q) ^ 2 * (a ^ k / (k.factorial : ℝ)) ^ 2 * Real.exp (1 / c) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = C * (δ * y) ^ 2 := by
      dsimp [C, y]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hscaled (by dsimp [C]; positivity)

end OMA.R_Erdos442_erdos_442_variants_tao_R1_H2_R1
