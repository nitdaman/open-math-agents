import FormalConjectures.GreensOpenProblems.«18»

-- Problem: Ben Green's Open Problem 18 — bmz corners
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/18.lean:82 (declaration Green18.green_18.bmz_corners)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMAGreen18

open Finset SimpleGraph SimpleGraph.TripartiteFromTriangles Sum3

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Triangle indices `(a, b, a * b)` for `(a, b) ∈ A`. -/
def tri (A : Finset (G × G)) : Finset (G × G × G) :=
  A.map ⟨fun p => (p.1, p.2, p.1 * p.2), by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
    simp only [Prod.mk.injEq] at h
    simp [h.1, h.2.1]⟩

lemma mem_tri {A : Finset (G × G)} {a b c : G} :
    (a, b, c) ∈ tri A ↔ (a, b) ∈ A ∧ c = a * b := by
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hxy, he⟩ := mem_map.1 h
    have e1 : x = a := congrArg Prod.fst he
    have e2 : y = b := congrArg (fun q => q.2.1) he
    have e3 : x * y = c := congrArg (fun q => q.2.2) he
    subst e1 e2 e3
    exact ⟨hxy, rfl⟩
  · rintro ⟨h, rfl⟩
    exact mem_map.2 ⟨(a, b), h, rfl⟩

lemma card_tri (A : Finset (G × G)) : #(tri A) = #A := card_map _

instance (A : Finset (G × G)) : ExplicitDisjoint (tri A) := by
  constructor
  · intro a b c a' h h'
    rw [mem_tri] at h h'
    have := h.2.symm.trans h'.2
    exact mul_right_cancel this
  · intro a b c b' h h'
    rw [mem_tri] at h h'
    have := h.2.symm.trans h'.2
    exact mul_left_cancel this
  · intro a b c c' h h'
    rw [mem_tri] at h h'
    rw [h.2, h'.2]

/-- All corner-like triples (including trivial `g = 1`). -/
def S (A : Finset (G × G)) : Finset (G × G × G) :=
  (univ : Finset (G × G × G)).filter
    fun p => (p.1, p.2.1) ∈ A ∧ (p.1 * p.2.2, p.2.1) ∈ A ∧ (p.1, p.2.2 * p.2.1) ∈ A

lemma card_S_le (A : Finset (G × G)) : #(S A) ≤ Green18.numBmzCorners A + #A := by
  have hsub : S A ⊆ ((univ : Finset (G × G × G)).filter
      fun p => p.2.2 ≠ 1 ∧ (p.1, p.2.1) ∈ A ∧ (p.1 * p.2.2, p.2.1) ∈ A ∧
        (p.1, p.2.2 * p.2.1) ∈ A) ∪ A.image (fun q => (q.1, q.2, (1 : G))) := by
    rintro ⟨x, y, g⟩ hp
    simp only [S, mem_filter, mem_univ, true_and] at hp
    by_cases hg : g = 1
    · subst hg
      apply mem_union_right
      exact mem_image.2 ⟨(x, y), hp.1, rfl⟩
    · apply mem_union_left
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨hg, hp⟩
  calc #(S A) ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := by
      unfold Green18.numBmzCorners
      exact Nat.add_le_add le_rfl card_image_le

lemma cliques_sub (A : Finset (G × G)) :
    (graph (tri A)).cliqueFinset 3 ⊆
      (S A).image (fun p => ({in₀ p.1, in₁ p.2.1, in₂ (p.1 * p.2.2 * p.2.1)} :
        Finset (G ⊕ G ⊕ G))) := by
  intro s hs
  rw [mem_cliqueFinset_iff, is3Clique_iff] at hs
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hs
  obtain ⟨a, b, c, hset, hab, hac, hbc⟩ := graph_triple hxy hxz hyz
  rw [← hset]
  rw [Graph.in₀₁_iff] at hab
  rw [Graph.in₀₂_iff] at hac
  rw [Graph.in₁₂_iff] at hbc
  obtain ⟨c1, h1⟩ := hab
  obtain ⟨b2, h2⟩ := hac
  obtain ⟨a3, h3⟩ := hbc
  rw [mem_tri] at h1 h2 h3
  refine mem_image.2 ⟨(a, b, a⁻¹ * c * b⁻¹), ?_, ?_⟩
  · simp only [S, mem_filter, mem_univ, true_and]
    refine ⟨h1.1, ?_, ?_⟩
    · have : a * (a⁻¹ * c * b⁻¹) = a3 := by rw [h3.2]; group
      rw [this]; exact h3.1
    · have : a⁻¹ * c * b⁻¹ * b = b2 := by rw [h2.2]; group
      rw [this]; exact h2.1
  · simp only
    have : a * (a⁻¹ * c * b⁻¹) * b = c := by group
    rw [this]

end OMAGreen18

open OMAGreen18 Finset SimpleGraph in
theorem OMA.solution : type_of% @Green18.green_18.bmz_corners := by
  intro α hα
  set δ := triangleRemovalBound (α / 9) with hδdef
  have hδ : 0 < δ := triangleRemovalBound_pos (by positivity)
  refine ⟨δ, hδ, ⌈1 / δ⌉₊, ?_⟩
  intro G _ _ _ A hG hA
  set n := Fintype.card G with hn
  have hn1 : (1 : ℝ) ≤ δ * n := by
    have h1 : (1 / δ : ℝ) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hG)
    rw [div_le_iff₀ hδ] at h1
    linarith
  have hfar : (SimpleGraph.TripartiteFromTriangles.graph (tri A)).FarFromTriangleFree (α / 9) := by
    apply SimpleGraph.TripartiteFromTriangles.farFromTriangleFree
    rw [card_tri]
    push_cast
    rw [← hn]
    nlinarith
  have h1 := hfar.le_card_cliqueFinset
  have h2 := Finset.card_le_card (cliques_sub A)
  have h3 := (Finset.card_image_le (s := S A) (f := fun p => ({Sum3.in₀ p.1, Sum3.in₁ p.2.1, Sum3.in₂ (p.1 * p.2.2 * p.2.1)} : Finset (G ⊕ G ⊕ G)))).trans (card_S_le A)
  have hcard : Fintype.card (G ⊕ G ⊕ G) = 3 * n := by
    simp [Fintype.card_sum, hn]; ring
  rw [hcard] at h1
  have h4 : ((#((SimpleGraph.TripartiteFromTriangles.graph (tri A)).cliqueFinset 3) : ℕ) : ℝ)
      ≤ (Green18.numBmzCorners A : ℝ) + n ^ 2 := by
    have hAc : #A ≤ n ^ 2 := by
      have := Finset.card_le_univ A
      simpa [Fintype.card_prod, hn, sq] using this
    have := h2.trans h3
    have : (#((SimpleGraph.TripartiteFromTriangles.graph (tri A)).cliqueFinset 3) : ℝ)
        ≤ (Green18.numBmzCorners A : ℝ) + (#A : ℝ) := by exact_mod_cast this
    have : (#A : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hAc
    linarith
  have hn0 : (0 : ℝ) ≤ n := by positivity
  push_cast at h1
  have h5 : (n : ℝ) ^ 2 ≤ δ * n ^ 3 := by nlinarith [sq_nonneg (n : ℝ)]
  nlinarith [pow_nonneg hn0 3, mul_pos hδ hδ]
