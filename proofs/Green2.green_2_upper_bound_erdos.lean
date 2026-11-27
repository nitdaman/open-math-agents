import FormalConjectures.GreensOpenProblems.«2»

-- Problem: Ben Green's Open Problem 2 — green 2 upper bound erdos
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/2.lean (declaration Green2.green_2_upper_bound_erdos)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Construction: A = [-a, b] with a + b + 1 = n and a, b about n / 2. If S ⊆ A has no sum of two
-- distinct elements in A, then S has at most one element in [-a/2, b/2], and S cannot have
-- elements both above b/2 and below -a/2, so |S| ≤ 1 + about n / 4.

namespace OMA.O7c

open Finset

lemma bound (a b : ℕ) (S : Finset ℤ) (hS : S ⊆ Icc (-(a : ℤ)) b)
    (hd : Disjoint S.restrictedSumset (Icc (-(a : ℤ)) b)) :
    (S.card : ℤ) ≤ 1 + ((b : ℤ) - (b : ℤ) / 2) ∨ (S.card : ℤ) ≤ 1 + ((a : ℤ) - (a : ℤ) / 2) := by
  have hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y < -(a : ℤ) ∨ (b : ℤ) < x + y := by
    intro x hx y hy hxy
    by_contra h
    push_neg at h
    have hm : x + y ∈ S.restrictedSumset :=
      Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩
    exact Finset.disjoint_left.mp hd hm (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hin : ∀ x ∈ S, -(a : ℤ) ≤ x ∧ x ≤ b := fun x hx => Finset.mem_Icc.mp (hS hx)
  set T := S.filter (fun x => -(a : ℤ) ≤ 2 * x ∧ 2 * x ≤ b) with hT
  set P := S.filter (fun x => (b : ℤ) < 2 * x) with hP
  set N := S.filter (fun x => 2 * x < -(a : ℤ)) with hN
  have hT1 : T.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [hT, Finset.mem_filter] at hx hy
    by_contra hxy
    have := hpair x hx.1 y hy.1 hxy
    omega
  have hPN : P = ∅ ∨ N = ∅ := by
    by_contra h
    push_neg at h
    obtain ⟨p, hp⟩ := h.1
    obtain ⟨q, hq⟩ := h.2
    rw [hP, Finset.mem_filter] at hp
    rw [hN, Finset.mem_filter] at hq
    have h1 := hin p hp.1
    have h2 := hin q hq.1
    have := hpair p hp.1 q hq.1 (by omega)
    omega
  have hPc : (P.card : ℤ) ≤ (b : ℤ) - (b : ℤ) / 2 := by
    have hsub : P ⊆ Finset.Ioc ((b : ℤ) / 2) b := by
      intro x hx
      rw [hP, Finset.mem_filter] at hx
      have := hin x hx.1
      rw [Finset.mem_Ioc]
      omega
    have := Finset.card_le_card hsub
    rw [Int.card_Ioc] at this
    have h0 : (0 : ℤ) ≤ (b : ℤ) - (b : ℤ) / 2 := by omega
    have := Int.toNat_of_nonneg h0
    omega
  have hNc : (N.card : ℤ) ≤ (a : ℤ) - (a : ℤ) / 2 := by
    have hsub : N ⊆ Finset.Ico (-(a : ℤ)) (-((a : ℤ) / 2)) := by
      intro x hx
      rw [hN, Finset.mem_filter] at hx
      have := hin x hx.1
      rw [Finset.mem_Ico]
      omega
    have := Finset.card_le_card hsub
    rw [Int.card_Ico] at this
    have h0 : (0 : ℤ) ≤ -((a : ℤ) / 2) - -(a : ℤ) := by omega
    have := Int.toNat_of_nonneg h0
    omega
  have hcover : S ⊆ T ∪ P ∪ N := by
    intro x hx
    rw [Finset.mem_union, Finset.mem_union, hT, hP, hN, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_filter]
    by_cases h1 : (b : ℤ) < 2 * x
    · exact Or.inl (Or.inr ⟨hx, h1⟩)
    · by_cases h2 : 2 * x < -(a : ℤ)
      · exact Or.inr ⟨hx, h2⟩
      · exact Or.inl (Or.inl ⟨hx, by omega, by omega⟩)
  have hc := Finset.card_le_card hcover
  have hu1 := Finset.card_union_le (T ∪ P) N
  have hu2 := Finset.card_union_le T P
  rcases hPN with h | h
  · have : P.card = 0 := by rw [h, Finset.card_empty]
    right
    omega
  · have : N.card = 0 := by rw [h, Finset.card_empty]
    left
    omega

end OMA.O7c

theorem OMA.solution : type_of% @Green2.green_2_upper_bound_erdos := by
  refine ⟨3, Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩⟩
  refine ⟨Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n - 1 - n / 2 : ℕ) : ℤ), ?_, ?_⟩
  · rw [Int.card_Icc]
    omega
  · have hcard : (Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n - 1 - n / 2 : ℕ) : ℤ)).card = n := by
      rw [Int.card_Icc]
      omega
    have hM : 4 * Green2.maxRestrictedSumAvoidingSubsetSize
        (Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n - 1 - n / 2 : ℕ) : ℤ)) ≤ n + 8 := by
      have : Green2.maxRestrictedSumAvoidingSubsetSize
          (Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n - 1 - n / 2 : ℕ) : ℤ)) ≤ n / 4 + 2 := by
        unfold Green2.maxRestrictedSumAvoidingSubsetSize
        apply Finset.sup_le
        intro S hS
        rw [Finset.mem_filter, Finset.mem_powerset] at hS
        have := OMA.O7c.bound (n / 2) (n - 1 - n / 2) S hS.1 hS.2
        omega
      omega
    rw [hcard]
    have hR : (4 : ℝ) * (Green2.maxRestrictedSumAvoidingSubsetSize
        (Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n - 1 - n / 2 : ℕ) : ℤ)) : ℝ) ≤ n + 8 := by
      exact_mod_cast hM
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
