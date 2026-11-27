import FormalConjectures.ErdosProblems.«751»

-- Reduction Erdos751.erdos_751.parts.i.R1 of Erdős Problem 751 — i
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open SimpleGraph

namespace OMA.R_Erdos751_erdos_751_parts_i_R1

/-- Finite critical subgraphs: every finite graph that is not 3-colourable contains a subgraph
that is 2-connected (more than two vertices, and deleting any one vertex leaves it connected)
with every vertex having at least three neighbours inside the subgraph. -/
def H1 : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V), ¬ G.Colorable 3 →
    ∃ G' : G.Subgraph, 2 < Nat.card G'.verts ∧
      (∀ x : G'.verts, (G'.coe.induce {x}ᶜ).Connected) ∧
      (∀ x : G'.verts, 3 ≤ Nat.card (G'.coe.neighborSet x))

/-- Bondy and Vince: a finite 2-connected graph with minimum degree at least 3 has two cycle
lengths `m < m'` with `m' ≤ m + 2`. -/
def H2 : Prop :=
  ∀ (W : Type) [Finite W] (H : SimpleGraph W), 2 < Nat.card W →
    (∀ x : W, (H.induce {x}ᶜ).Connected) →
    (∀ x : W, 3 ≤ Nat.card (H.neighborSet x)) →
    ∃ m ∈ H.cycleLengths, ∃ m' ∈ H.cycleLengths, m < m' ∧ m' ≤ m + 2

lemma cycleLengths_coe_subset {V : Type} (G : SimpleGraph V) (G' : G.Subgraph) :
    G'.coe.cycleLengths ⊆ G.cycleLengths := by
  rintro m ⟨a, w, hw, rfl⟩
  exact ⟨(a : V), w.map G'.hom,
    (Walk.isCycle_map_iff_of_injective (f := G'.hom) Subgraph.hom_injective).mpr hw,
    Walk.length_map _ w⟩

theorem main : H1 → H2 → type_of% @Erdos751.erdos_751.parts.i := by
  intro hH1 hH2
  unfold H1 at hH1
  unfold H2 at hH2
  intro h
  obtain ⟨V, G, hχ, hgap⟩ := h 3
  have hnc : ¬ G.Colorable 3 := fun hc => by
    have := hc.chromaticNumber_le
    rw [hχ] at this
    exact absurd this (by norm_num)
  -- compactness: a non-3-colourable graph has a finite non-3-colourable subgraph
  have hfin : ∃ G' : G.Subgraph, G'.verts.Finite ∧ ¬ G'.coe.Colorable 3 := by
    by_contra hne
    push_neg at hne
    apply hnc
    have key : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe →g completeGraph (Fin 3) :=
      fun G' hG' => Classical.choice (hne G' hG')
    obtain ⟨φ⟩ := nonempty_hom_of_forall_finite_subgraph_hom key
    exact ⟨φ⟩
  obtain ⟨G', hG'fin, hG'nc⟩ := hfin
  haveI : Finite G'.verts := hG'fin.to_subtype
  -- H1 on the finite subgraph gives a 2-connected subgraph of minimum degree 3
  obtain ⟨G'', h2c, hcon, hdeg⟩ := hH1 G'.verts G'.coe hG'nc
  -- H2 gives the two cycle lengths
  obtain ⟨m, hm, m', hm', hlt, hle⟩ := hH2 G''.verts G''.coe h2c hcon hdeg
  -- cycles of G'' are cycles of G' and then of G
  have hA : ∀ n ∈ G''.coe.cycleLengths, n ∈ G.cycleLengths :=
    fun n hn => cycleLengths_coe_subset G G' (cycleLengths_coe_subset G'.coe G'' hn)
  have h1 := hgap m (hA m hm) m' (hA m' hm') hlt
  omega

end OMA.R_Erdos751_erdos_751_parts_i_R1
