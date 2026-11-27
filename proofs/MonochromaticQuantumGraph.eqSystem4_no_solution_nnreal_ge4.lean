import FormalConjectures.Paper.MonochromaticQuantumGraph

-- Problem: Monochromatic quantum graphs (inherited vertex colorings) — eqSystem4 no solution nnreal ge4
-- Upstream: formal-conjectures FormalConjectures/Paper/MonochromaticQuantumGraph.lean:346 (declaration MonochromaticQuantumGraph.eqSystem4_no_solution_nnreal_ge4)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Proof idea. On four vertices there are three perfect matchings, so the perfect matching sum is
a sum of three products of two edge weights. For each colour `c` the monochromatic sum is `1`,
so one of the three matchings has both its `c`-coloured edges of positive weight. With at least
four colours, two colours `c ≠ d` use the same matching. Mixing them (colour `c` on one edge
of that matching and `d` on the other) gives a non-monochromatic colouring whose sum contains a
positive product, while all weights are nonnegative, contradicting that this sum is `0`.
-/

namespace OMAQ

open MonochromaticQuantumGraph
open scoped NNReal

theorem pm4 {D : ℕ} (W : WeightsN 4 D ℝ≥0) (ι : V 4 → Fin D) :
    pmSumN 4 D W ι =
      W (mkEdge 0 1 (ι 0) (ι 1)) * W (mkEdge 2 3 (ι 2) (ι 3)) +
      W (mkEdge 0 2 (ι 0) (ι 2)) * W (mkEdge 1 3 (ι 1) (ι 3)) +
      W (mkEdge 0 3 (ι 0) (ι 3)) * W (mkEdge 1 2 (ι 1) (ι 2)) := by
  simp [pmSumN, pmSumList, pmSumListAux, vertices, List.erase]
  ring

theorem allEqual_const {D : ℕ} (c : Fin D) : allEqual (fun _ : V 4 => c) := by
  simp [allEqual, allEqualList, vertices]

theorem not_allEqual {D : ℕ} (ι : V 4 → Fin D) (h : ι 0 ≠ ι 1 ∨ ι 0 ≠ ι 2 ∨ ι 0 ≠ ι 3) :
    ¬ allEqual ι := by
  intro hι
  simp [allEqual, allEqualList, vertices] at hι
  rcases hι with ⟨h1, h2, h3⟩
  have e1 : ι 0 = ι 1 := h1
  have e2 : ι 1 = ι 2 := h2
  have e3 : ι 2 = ι 3 := h3
  rcases h with h | h | h
  · exact h e1
  · exact h (e1.trans e2)
  · exact h (e1.trans (e2.trans e3))

end OMAQ

open MonochromaticQuantumGraph OMAQ in
open scoped NNReal in
theorem OMA.solution : type_of% @MonochromaticQuantumGraph.eqSystem4_no_solution_nnreal_ge4 := by
  classical
  intro D hD ⟨W, hW⟩
  -- the three matching products for the constant colouring `c`
  let P : Fin 3 → Fin D → ℝ≥0 := fun k c =>
    if k = 0 then W (mkEdge 0 1 c c) * W (mkEdge 2 3 c c)
    else if k = 1 then W (mkEdge 0 2 c c) * W (mkEdge 1 3 c c)
    else W (mkEdge 0 3 c c) * W (mkEdge 1 2 c c)
  have hsum : ∀ c : Fin D, P 0 c + P 1 c + P 2 c = 1 := by
    intro c
    have := hW (fun _ => c)
    rw [if_pos (allEqual_const c), pm4] at this
    simpa [P] using this
  let f : Fin D → Fin 3 := fun c => if P 0 c ≠ 0 then 0 else if P 1 c ≠ 0 then 1 else 2
  have hf : ∀ c, P (f c) c ≠ 0 := by
    intro c
    by_cases h0 : P 0 c ≠ 0
    · simp only [f, if_pos h0]; exact h0
    · by_cases h1 : P 1 c ≠ 0
      · simp only [f, if_neg h0, if_pos h1]; exact h1
      · simp only [f, if_neg h0, if_neg h1]
        intro h2
        rw [not_not] at h0 h1
        have := hsum c
        rw [h0, h1, h2] at this
        simp at this
  have hcard : Fintype.card (Fin 3) < Fintype.card (Fin D) := by simp; omega
  obtain ⟨c, d, hcd, hfe⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hc := hf c
  have hd := hf d
  rw [hfe] at hc
  -- a non-monochromatic colouring has sum zero, so each of its products vanishes
  have key : ∀ ι : V 4 → Fin D, (ι 0 ≠ ι 1 ∨ ι 0 ≠ ι 2 ∨ ι 0 ≠ ι 3) →
      W (mkEdge 0 1 (ι 0) (ι 1)) * W (mkEdge 2 3 (ι 2) (ι 3)) = 0 ∧
      W (mkEdge 0 2 (ι 0) (ι 2)) * W (mkEdge 1 3 (ι 1) (ι 3)) = 0 ∧
      W (mkEdge 0 3 (ι 0) (ι 3)) * W (mkEdge 1 2 (ι 1) (ι 2)) = 0 := by
    intro ι hne
    have := hW ι
    rw [if_neg (not_allEqual ι hne), pm4] at this
    rcases add_eq_zero.1 this with ⟨h12, h3⟩
    rcases add_eq_zero.1 h12 with ⟨h1, h2⟩
    exact ⟨h1, h2, h3⟩
  generalize hk : f d = k at hc hd
  fin_cases k
  · simp only [P, Fin.zero_eta, if_pos] at hc hd
    have := (key ![c, c, d, d] (Or.inr (Or.inl (by simpa using hcd)))).1
    simp only [Matrix.cons_val] at this
    rcases mul_eq_zero.1 this with h | h
    · exact hc (by rw [h, zero_mul])
    · exact hd (by rw [h, mul_zero])
  · simp only [P, Fin.mk_one, if_neg (by decide : (1 : Fin 3) ≠ 0), if_pos] at hc hd
    have := (key ![c, d, c, d] (Or.inl (by simpa using hcd))).2.1
    simp only [Matrix.cons_val] at this
    rcases mul_eq_zero.1 this with h | h
    · exact hc (by rw [h, zero_mul])
    · exact hd (by rw [h, mul_zero])
  · simp only [P, Fin.reduceFinMk, if_neg (by decide : (2 : Fin 3) ≠ 0),
      if_neg (by decide : (2 : Fin 3) ≠ 1)] at hc hd
    have := (key ![c, d, d, c] (Or.inl (by simpa using hcd))).2.2
    simp only [Matrix.cons_val] at this
    rcases mul_eq_zero.1 this with h | h
    · exact hc (by rw [h, zero_mul])
    · exact hd (by rw [h, mul_zero])
