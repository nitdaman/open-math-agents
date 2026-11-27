import FormalConjectures.ErdosProblems.«442»

/-! Separate the logarithmic growth of Tao's explicit set from its weighted
divisor estimate, using the construction for parameter one in
https://arxiv.org/abs/2407.04226v1. -/

-- Reduction Erdos442.erdos_442.variants.tao.R1 of Erdős Problem 442 — tao
-- Credit: @dk8827
-- Each H becomes its own step once this file is accepted.

namespace OMA.R_Erdos442_erdos_442_variants_tao_R1

open Filter Asymptotics
open scoped BigOperators

/-- The logarithmic mass asymptotic for the squarefree numbers in Tao's construction. -/
def H1 : Prop :=
  ∀ (t : ℕ → ℝ) (A : Set ℕ),
    (∀ k, t k = Real.exp (Real.exp ((k : ℝ) ^ 2))) →
    (∀ n, n ∈ A ↔ Squarefree n ∧ ∃ k : ℕ, 1 ≤ k ∧
      t k < (n : ℝ) ∧ (n : ℝ) ≤ t (k + 1) ∧
      (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ t k)).card ≤ k ∧
      (n.primeFactors.filter (fun p : ℕ => t k < (p : ℝ))).card ≤ 1) →
    ∃ f : ℝ → ℝ, f =o[atTop] (1 : ℝ → ℝ) ∧
      ∀ᶠ x : ℝ in atTop,
        let L := Erdos442.Real.maxLogOne
        ∑ n ∈ (A ∩ Set.Icc 1 ⌊x⌋₊ : Set ℕ), (1 : ℝ) / n =
          Real.exp ((1 / 2 + f x) * √(L (L x)) * L (L (L x)))

/-- The separate divisor-mass estimate for the same explicit set.
The divisor weight can be its value rather than Euler's totient. -/
def H2 : Prop :=
  ∀ (t : ℕ → ℝ) (A : Set ℕ),
    (∀ k, t k = Real.exp (Real.exp ((k : ℝ) ^ 2))) →
    (∀ n, n ∈ A ↔ Squarefree n ∧ ∃ k : ℕ, 1 ≤ k ∧
      t k < (n : ℝ) ∧ (n : ℝ) ≤ t (k + 1) ∧
      (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ t k)).card ≤ k ∧
      (n.primeFactors.filter (fun p : ℕ => t k < (p : ℝ))).card ≤ 1) →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      let S := (A ∩ Set.Icc 1 ⌊x⌋₊ : Set ℕ).toFinset
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (d : ℝ) * (∑ n ∈ S.filter (fun n => d ∣ n), (1 : ℝ) / n) ^ 2 ≤
        C * (∑ n ∈ S, (1 : ℝ) / n) ^ 2

lemma finite_lcm_le_divisor {N : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 N) :
    ∑ nm ∈ S ×ˢ S, (1 : ℝ) / nm.1.lcm nm.2 ≤
      ∑ d ∈ Finset.Icc 1 N, (d : ℝ) * (∑ n ∈ S.filter (fun n => d ∣ n), (1 : ℝ) / n) ^ 2 := by
  classical
  let D := Finset.Icc 1 N
  let w (d n : ℕ) : ℝ := if d ∣ n then (1 : ℝ) / n else 0
  have hw (d n : ℕ) : 0 ≤ w d n := by
    dsimp [w]
    split <;> positivity
  rw [Finset.sum_product]
  calc
    _ ≤ ∑ n ∈ S, ∑ m ∈ S, ∑ d ∈ D, (d : ℝ) * w d n * w d m := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      have hnpos : 0 < n := (Finset.mem_Icc.mp (hS hn)).1
      have hmpos : 0 < m := (Finset.mem_Icc.mp (hS hm)).1
      have hg : n.gcd m ∈ D := Finset.mem_Icc.mpr
        ⟨Nat.gcd_pos_of_pos_left m hnpos, (Nat.gcd_le_left m hnpos).trans (Finset.mem_Icc.mp (hS hn)).2⟩
      have hmul : (n.gcd m : ℝ) * (n.lcm m : ℝ) = n * m := by exact_mod_cast Nat.gcd_mul_lcm n m
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      have hl0 : (n.lcm m : ℝ) ≠ 0 := by exact_mod_cast (Nat.lcm_pos hnpos hmpos).ne'
      calc
        _ = (n.gcd m : ℝ) * ((1 : ℝ) / n) * ((1 : ℝ) / m) := by
          field_simp
          nlinarith only [hmul]
        _ = (n.gcd m : ℝ) * w (n.gcd m) n * w (n.gcd m) m := by
          simp [w, Nat.gcd_dvd_left, Nat.gcd_dvd_right]
        _ ≤ _ := Finset.single_le_sum (f := fun d : ℕ => (d : ℝ) * w d n * w d m)
          (fun d _ => mul_nonneg (mul_nonneg (by positivity) (hw d n)) (hw d m)) hg
    _ = ∑ n ∈ S, ∑ d ∈ D, ∑ m ∈ S, (d : ℝ) * w d n * w d m :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ d ∈ D, ∑ n ∈ S, ∑ m ∈ S, (d : ℝ) * w d n * w d m := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hsum : (∑ n ∈ S.filter (fun n => d ∣ n), (1 : ℝ) / n) = ∑ n ∈ S, w d n := by
        rw [Finset.sum_filter]
      rw [hsum]
      calc
        _ = ∑ n ∈ S, ((d : ℝ) * w d n) * (∑ m ∈ S, w d m) :=
          Finset.sum_congr rfl (fun _ _ => (Finset.mul_sum _ _ _).symm)
        _ = (∑ n ∈ S, (d : ℝ) * w d n) * (∑ m ∈ S, w d m) := (Finset.sum_mul _ _ _).symm
        _ = _ := by rw [← Finset.mul_sum, mul_assoc, pow_two]

theorem main : H1 → H2 → type_of% @Erdos442.erdos_442.variants.tao := by
  intro hmass hdiv
  classical
  let t (k : ℕ) := Real.exp (Real.exp ((k : ℝ) ^ 2))
  let A : Set ℕ := {n | Squarefree n ∧ ∃ k : ℕ, 1 ≤ k ∧
    t k < (n : ℝ) ∧ (n : ℝ) ≤ t (k + 1) ∧
    (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ t k)).card ≤ k ∧
    (n.primeFactors.filter (fun p : ℕ => t k < (p : ℝ))).card ≤ 1}
  obtain ⟨f, hf, hfMass⟩ := hmass t A (fun _ => rfl) (fun _ => Iff.rfl)
  obtain ⟨C, hC, hbound⟩ := hdiv t A (fun _ => rfl) (fun _ => Iff.rfl)
  refine ⟨A, f, C, hC, hf, ?_⟩
  filter_upwards [hfMass, hbound] with x hx hxbound
  refine ⟨hx, ?_⟩
  rw [Set.toFinset_prod, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => by positivity))]
  apply (finite_lcm_le_divisor _ ?_).trans hxbound
  intro n hn
  have hmem := (Set.mem_toFinset.mp hn).2
  exact Finset.mem_Icc.mpr hmem

end OMA.R_Erdos442_erdos_442_variants_tao_R1
