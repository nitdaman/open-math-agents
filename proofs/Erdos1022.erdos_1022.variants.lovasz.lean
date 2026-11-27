import FormalConjectures.ErdosProblems.«1022»
import Mathlib.Tactic

-- Problem: Erdős Problem 1022 — lovasz
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1022.lean:81 (declaration Erdos1022.erdos_1022.variants.lovasz)
-- Credit: @malikfassi (the owner of the agent is credited as the solver)
-- c = 1 works: if every nonempty X contains fewer than |X| sets of the family, the family has
-- fewer sets than vertices, so there are real weights on the vertices, not all zero, summing to
-- zero on every set (Seymour's argument). Colour by the sign of the weight; the sets on which
-- all weights vanish form a strictly smaller family, coloured by induction.
-- c > 1 fails: the triangle {0,1}, {0,2}, {1,2}.

namespace OMA.E1022L

/-- If every nonempty `X` contains fewer than `|X|` members of `F`, then `F` is 2-colourable. -/
theorem sparse_one (F : Finset (Finset ℕ)) :
    (∀ X : Finset ℕ, X.Nonempty → (F.filter (· ⊆ X)).card < X.card) →
      ∃ f : ℕ → Fin 2, ∀ A ∈ F, ∃ a ∈ A, ∃ b ∈ A, f a ≠ f b := by
  induction F using Finset.strongInduction with
  | H F ih =>
    intro hs
    by_cases hF : F = ∅
    · subst hF
      exact ⟨fun _ => 0, fun A hA => absurd hA (Finset.notMem_empty A)⟩
    obtain ⟨A0, hA0⟩ := Finset.nonempty_iff_ne_empty.2 hF
    -- the vertex set
    obtain ⟨V, hV⟩ : ∃ V : Finset ℕ, V = F.biUnion id := ⟨_, rfl⟩
    have hsubV : ∀ A ∈ F, A ⊆ V := by
      intro A hA
      rw [hV]
      exact Finset.subset_biUnion_of_mem id hA
    have hcard : F.card < V.card := by
      by_cases hVne : V.Nonempty
      · have h := hs V hVne
        have hfil : F.filter (· ⊆ V) = F := Finset.filter_true_of_mem hsubV
        rw [hfil] at h
        exact h
      · rw [Finset.not_nonempty_iff_eq_empty] at hVne
        have hA0e : A0 ⊆ ({0} : Finset ℕ) := by
          intro n hn
          have := hsubV A0 hA0 hn
          rw [hVne] at this
          exact absurd this (Finset.notMem_empty n)
        have h := hs {0} (Finset.singleton_nonempty 0)
        rw [Finset.card_singleton, Nat.lt_one_iff, Finset.card_eq_zero] at h
        have hmem : A0 ∈ F.filter (· ⊆ ({0} : Finset ℕ)) := Finset.mem_filter.2 ⟨hA0, hA0e⟩
        rw [h] at hmem
        exact absurd hmem (Finset.notMem_empty A0)
    -- weights
    have key : ∃ x : ↥V → ℝ, x ≠ 0 ∧
        ∀ A : ↥F, ∑ v : ↥V, (if v.1 ∈ A.1 then (1 : ℝ) else 0) * x v = 0 := by
      let M : Matrix ↥F ↥V ℝ := fun A v => if v.1 ∈ A.1 then 1 else 0
      have hninj : ¬ Function.Injective M.mulVecLin := by
        intro hinj
        have h := LinearMap.finrank_le_finrank_of_injective hinj
        rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
          Fintype.card_coe, Fintype.card_coe] at h
        omega
      rw [injective_iff_map_eq_zero] at hninj
      push_neg at hninj
      obtain ⟨x, hx0, hxne⟩ := hninj
      refine ⟨x, hxne, fun A => ?_⟩
      exact congrFun hx0 A
    obtain ⟨x, hxne, hx0⟩ := key
    obtain ⟨x', hx'⟩ : ∃ x' : ℕ → ℝ, x' = fun n => if h : n ∈ V then x ⟨n, h⟩ else 0 := ⟨_, rfl⟩
    have hx'v : ∀ v : ↥V, x' v.1 = x v := by
      intro v
      rw [hx']
      simp [v.2]
    have hsum : ∀ A ∈ F, ∑ n ∈ A, x' n = 0 := by
      intro A hA
      have hAV : A ⊆ V := hsubV A hA
      calc ∑ n ∈ A, x' n = ∑ n ∈ V ∩ A, x' n := by rw [Finset.inter_eq_right.2 hAV]
        _ = ∑ n ∈ V, (if n ∈ A then x' n else 0) := (Finset.sum_ite_mem V A x').symm
        _ = ∑ v : ↥V, (if v.1 ∈ A then x' v.1 else 0) :=
            (Finset.sum_coe_sort V (fun n => if n ∈ A then x' n else 0)).symm
        _ = ∑ v : ↥V, (if v.1 ∈ A then (1 : ℝ) else 0) * x v := by
            refine Finset.sum_congr rfl (fun v _ => ?_)
            rw [hx'v v]
            split_ifs <;> simp
        _ = 0 := hx0 ⟨A, hA⟩
    -- the sets on which all weights vanish
    have hG : F.filter (fun A => ∀ n ∈ A, x' n = 0) ⊂ F := by
      rw [Finset.filter_ssubset]
      obtain ⟨v, hv⟩ := Function.ne_iff.1 hxne
      have hvV : v.1 ∈ F.biUnion id := by
        rw [← hV]
        exact v.2
      obtain ⟨A, hA, hvA⟩ := Finset.mem_biUnion.1 hvV
      refine ⟨A, hA, fun hall => hv ?_⟩
      have := hall v.1 hvA
      rw [hx'v v] at this
      exact this
    obtain ⟨f₀, hf₀⟩ := ih _ hG (by
      intro X hX
      refine lt_of_le_of_lt (Finset.card_le_card ?_) (hs X hX)
      intro A hA
      rw [Finset.mem_filter] at hA ⊢
      exact ⟨(Finset.mem_filter.1 hA.1).1, hA.2⟩)
    refine ⟨fun n => if 0 < x' n then 0 else if x' n < 0 then 1 else f₀ n, fun A hA => ?_⟩
    by_cases hAz : ∀ n ∈ A, x' n = 0
    · obtain ⟨a, ha, b, hb, hab⟩ := hf₀ A (Finset.mem_filter.2 ⟨hA, hAz⟩)
      refine ⟨a, ha, b, hb, ?_⟩
      simp only [hAz a ha, hAz b hb, lt_self_iff_false, if_false]
      exact hab
    · push_neg at hAz
      obtain ⟨n, hn, hnz⟩ := hAz
      have hpos : ∃ a ∈ A, 0 < x' a := by
        by_contra hcon
        push_neg at hcon
        have := (Finset.sum_eq_zero_iff_of_nonpos hcon).1 (hsum A hA)
        exact hnz (this n hn)
      have hneg : ∃ b ∈ A, x' b < 0 := by
        by_contra hcon
        push_neg at hcon
        have := (Finset.sum_eq_zero_iff_of_nonneg hcon).1 (hsum A hA)
        exact hnz (this n hn)
      obtain ⟨a, ha, hapos⟩ := hpos
      obtain ⟨b, hb, hbneg⟩ := hneg
      refine ⟨a, ha, b, hb, ?_⟩
      have hb' : ¬ 0 < x' b := not_lt.2 hbneg.le
      simp only [hapos, hb', hbneg, if_true, if_false]
      decide

/-- The triangle. -/
def tri : Finset (Finset ℕ) := {{0, 1}, {0, 2}, {1, 2}}

lemma tri_mem (A : Finset ℕ) (hA : A ∈ tri) : A = {0, 1} ∨ A = {0, 2} ∨ A = {1, 2} := by
  simpa [tri] using hA

lemma tri_card : tri.card = 3 := by decide

lemma pair_ne (f : ℕ → Fin 2) (u v : ℕ)
    (h : ∃ x ∈ ({u, v} : Finset ℕ), ∃ y ∈ ({u, v} : Finset ℕ), f x ≠ f y) : f u ≠ f v := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    first | exact hxy | exact hxy.symm | exact absurd rfl hxy

lemma fin2tri : ∀ a b c : Fin 2, a ≠ b → a ≠ c → b ≠ c → False := by decide

lemma tri_sparse (X : Finset ℕ) (hX : X.Nonempty) : (tri.filter (· ⊆ X)).card ≤ X.card := by
  have hXpos := Finset.card_pos.2 hX
  have one : ∀ (E : Finset ℕ), tri.filter (· ⊆ X) ⊆ {E} → (tri.filter (· ⊆ X)).card ≤ X.card := by
    intro E hsub
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    omega
  by_cases h0 : 0 ∈ X
  · by_cases h1 : 1 ∈ X
    · by_cases h2 : 2 ∈ X
      · have h3 : ({0, 1, 2} : Finset ℕ) ⊆ X := by
          intro n hn
          simp only [Finset.mem_insert, Finset.mem_singleton] at hn
          rcases hn with rfl | rfl | rfl <;> assumption
        have h4 := Finset.card_le_card h3
        have h5 : (tri.filter (· ⊆ X)).card ≤ tri.card := Finset.card_filter_le _ _
        have h6 := tri_card
        have h7 : ({0, 1, 2} : Finset ℕ).card = 3 := by decide
        omega
      · apply one {0, 1}
        intro A hA
        obtain ⟨hAT, hAX⟩ := Finset.mem_filter.1 hA
        rcases tri_mem A hAT with rfl | rfl | rfl
        · simp
        · exact absurd (hAX (by simp)) h2
        · exact absurd (hAX (by simp)) h2
    · apply one {0, 2}
      intro A hA
      obtain ⟨hAT, hAX⟩ := Finset.mem_filter.1 hA
      rcases tri_mem A hAT with rfl | rfl | rfl
      · exact absurd (hAX (by simp)) h1
      · simp
      · exact absurd (hAX (by simp)) h1
  · apply one {1, 2}
    intro A hA
    obtain ⟨hAT, hAX⟩ := Finset.mem_filter.1 hA
    rcases tri_mem A hAT with rfl | rfl | rfl
    · exact absurd (hAX (by simp)) h0
    · exact absurd (hAX (by simp)) h0
    · simp

end OMA.E1022L

open OMA.E1022L in
theorem OMA.solution : type_of% @Erdos1022.erdos_1022.variants.lovasz := by
  constructor
  · show Erdos1022.SparseImpliesPropertyB 2 1
    intro F _ hs
    apply sparse_one F
    intro X hX
    have h := hs X hX
    rw [one_mul] at h
    unfold Finset.hypergraphInduce at h
    exact_mod_cast h
  · intro c hc
    by_contra hlt
    rw [not_le] at hlt
    have hc' : Erdos1022.SparseImpliesPropertyB 2 c := hc
    have hB := hc' tri ?_ ?_
    · obtain ⟨f, hf⟩ := hB
      have h01 := pair_ne f 0 1 (hf {0, 1} (by simp [tri]))
      have h02 := pair_ne f 0 2 (hf {0, 2} (by simp [tri]))
      have h12 := pair_ne f 1 2 (hf {1, 2} (by simp [tri]))
      exact fin2tri _ _ _ h01 h02 h12
    · intro A hA
      rcases tri_mem A hA with rfl | rfl | rfl <;> decide
    · intro X hX
      have hle := tri_sparse X hX
      have hXpos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hX
      have hle' : ((tri.hypergraphInduce X).card : ℝ) ≤ (X.card : ℝ) := by
        unfold Finset.hypergraphInduce
        exact_mod_cast hle
      have := mul_pos (sub_pos.2 hlt) hXpos
      linarith
