import FormalConjectures.Paper.MonochromaticQuantumGraph

/-!
Six vertices, complex amplitudes and arbitrary local dimension at least three.
Restricting the endpoint colours commutes with every perfect-matching term.
The remaining tasks concern just the six-vertex, three-colour equations.

H1 is the monochromatic-edge obstruction. H2 is the removal of bichromatic
edges in a hypothetical solution, stated only on oriented pairs u < v that
actually occur in the equations. The second is the rigidity route proposed
in Lemma 4.2 of R. Rajasekaran's two-replica manuscript. In particular
these targets do not assert nonexistence for arbitrary many colours.

Prior work: algal/krenn-gu-6x3-certificate (c04696e) already supplies a
three-colour nonexistence certificate using native evaluation. The author's
explainer explicitly notes the colour-restriction consequence for D > 3.
This is a contribution to the checker-compatible formalization, without
a discovery priority claim. Credit for this reduction: @shunyaekam.
-/

open MonochromaticQuantumGraph

namespace OMA.R_MonochromaticQuantumGraph_eqSystem6_no_solution_ge3_R1

def H1 : Prop :=
  ∀ W : WeightsN 6 3 ℂ,
    (∀ e : EdgeN 6 3, e.u < e.v → e.i ≠ e.j → W e = 0) →
    ¬ EqSystemN 6 3 W

def H2 : Prop :=
  ∀ W : WeightsN 6 3 ℂ, EqSystemN 6 3 W →
    ∀ e : EdgeN 6 3, e.u < e.v → e.i ≠ e.j → W e = 0

lemma three_colours {D : ℕ} (hD : 3 ≤ D) (W : WeightsN 6 D ℂ)
    (hW : EqSystemN 6 D W) : ∃ U : WeightsN 6 3 ℂ, EqSystemN 6 3 U := by
  let embed : Fin 3 → Fin D := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hD⟩
  have hEq (i j : Fin 3) : embed i = embed j ↔ i = j := by
    simp only [Fin.ext_iff, embed]
  let U : WeightsN 6 3 ℂ := fun e => W (mkEdge e.u e.v (embed e.i) (embed e.j))
  refine ⟨U, ?_⟩
  intro σ
  have h := hW (fun v => embed (σ v))
  have hsum : pmSumN 6 3 U σ = pmSumN 6 D W (fun v => embed (σ v)) := by
    rfl
  have hmono : allEqual (fun v : V 6 => embed (σ v)) ↔ allEqual σ := by
    simp [allEqual, allEqualList, vertices, hEq]
  rw [hsum]
  simpa only [hmono] using h

theorem main : H1 → H2 → type_of% @MonochromaticQuantumGraph.eqSystem6_no_solution_ge3 := by
  intro h1 h2 D hD h
  obtain ⟨W, hW⟩ := h
  obtain ⟨U, hU⟩ := three_colours hD W hW
  exact h1 U (h2 U hU) hU

end OMA.R_MonochromaticQuantumGraph_eqSystem6_no_solution_ge3_R1
