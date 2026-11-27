import FormalConjectures.WrittenOnTheWallII.GraphConjecture372

-- Reduction WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1 of Written on the Wall II - Conjecture 372 — regularized
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Split by the path cover number

If the path cover number is at most two, the factor `max 1 (p - 1)` is one, and the
claim is the two-path case `H1`. If it is at least three, the factor is at least two,
and the claim follows from `H2`: every tree satisfies `τ ≤ 2 γ_t`.

`H2` has a short proof. Root the tree and take a minimum total dominating set `D`.
Let `P` be the set of vertices outside `D` that have a child outside `D`. Then `D ∪ P`
is a vertex cover. Each `u ∈ P` with such a child `v` maps to a child of `v` in `D`
(it exists, since the parent `u` of `v` is not in `D`). This map is injective, so
`|P| ≤ |D|`.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1

open SimpleGraph

/-- The two-path case: a tree of order at least two with path cover number at most
two has vertex cover number at most its total domination number. -/
def H1 : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (T : SimpleGraph α), T.IsTree →
    2 ≤ Fintype.card α → T.pathCoverNumber ≤ 2 →
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber

/-- Every tree of order at least two has vertex cover number at most twice its total
domination number. -/
def H2 : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (T : SimpleGraph α), T.IsTree →
    2 ≤ Fintype.card α →
    T.vertexCoverNum.toNat ≤ 2 * T.totalDominationNumber

section transfer

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {K : SimpleGraph W}

omit [Fintype V] [DecidableEq V] [Fintype W] in

lemma tds_map (e : G ≃g K) (n : ℕ) (h : ∃ D : Finset V, G.IsTotalNDominatingSet n D) :
    ∃ D : Finset W, K.IsTotalNDominatingSet n D := by
  obtain ⟨D, hD, hc⟩ := h
  refine ⟨D.map e.toEquiv.toEmbedding, ?_, by simpa using hc⟩
  intro v
  obtain ⟨w, hw, hadj⟩ := hD (e.symm v)
  refine ⟨e w, ?_, ?_⟩
  · simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe]
    exact ⟨w, hw, rfl⟩
  · have := e.map_adj_iff.mpr hadj
    simpa using this

lemma tdn_congr (e : G ≃g K) : G.totalDominationNumber = K.totalDominationNumber := by
  unfold totalDominationNumber
  congr 1
  ext n
  exact ⟨tds_map e n, tds_map e.symm n⟩

lemma pc_map (e : G ≃g K) (k : ℕ)
    (h : ∃ P : Finset (Finset V), P.card = k ∧ G.IsPathCover P) :
    ∃ P : Finset (Finset W), P.card = k ∧ K.IsPathCover P := by
  obtain ⟨P, hk, hdisj, hcov, hpath⟩ := h
  have hinj : Function.Injective (fun s : Finset V => s.map e.toEquiv.toEmbedding) :=
    Finset.map_injective _
  refine ⟨P.image (fun s => s.map e.toEquiv.toEmbedding), ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, hk]
  · intro s1 hs1 s2 hs2 hne
    obtain ⟨t1, ht1, rfl⟩ := Finset.mem_image.mp hs1
    obtain ⟨t2, ht2, rfl⟩ := Finset.mem_image.mp hs2
    have : t1 ≠ t2 := fun h => hne (h ▸ rfl)
    exact (Finset.disjoint_map _).mpr (hdisj t1 ht1 t2 ht2 this)
  · intro v _
    have := hcov (Finset.mem_univ (e.symm v))
    obtain ⟨s, hs, hv⟩ := Finset.mem_biUnion.mp this
    refine Finset.mem_biUnion.mpr ⟨s.map e.toEquiv.toEmbedding, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [id, Finset.mem_map_equiv]
    exact hv
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨u, v, p, hp, rfl⟩ := hpath t ht
    refine ⟨e u, e v, p.map e.toHom, hp.map e.injective, ?_⟩
    ext x
    simp only [Finset.mem_map_equiv, List.mem_toFinset, Walk.support_map, List.mem_map]
    constructor
    · intro h
      exact ⟨e.symm x, h, by simp⟩
    · rintro ⟨a, ha, rfl⟩
      convert ha
      exact e.symm_apply_apply a

lemma pcn_congr (e : G ≃g K) : G.pathCoverNumber = K.pathCoverNumber := by
  unfold pathCoverNumber
  congr 1
  ext k
  exact ⟨pc_map e k, pc_map e.symm k⟩

end transfer

theorem main : H1 → H2 → type_of% @WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized := by
  intro h1 h2 α _ _ T hT hn
  let e := Fintype.equivFin α
  let i : T ≃g T.map e.toEmbedding := SimpleGraph.Iso.map e T
  have hT' : (T.map e.toEmbedding).IsTree := i.isTree_iff.mp hT
  have hn' : 2 ≤ Fintype.card (Fin (Fintype.card α)) := by simpa using hn
  rw [vertexCoverNum_congr i, tdn_congr i, pcn_congr i]
  by_cases hp : (T.map e.toEmbedding).pathCoverNumber ≤ 2
  · have hm : max 1 ((T.map e.toEmbedding).pathCoverNumber - 1) = 1 := by omega
    rw [hm, Nat.mul_one]
    exact h1 _ _ hT' hn' hp
  · have hm : 2 ≤ max 1 ((T.map e.toEmbedding).pathCoverNumber - 1) := by omega
    calc (T.map e.toEmbedding).vertexCoverNum.toNat
        ≤ 2 * (T.map e.toEmbedding).totalDominationNumber := h2 _ _ hT' hn'
      _ = (T.map e.toEmbedding).totalDominationNumber * 2 := Nat.mul_comm _ _
      _ ≤ (T.map e.toEmbedding).totalDominationNumber *
          max 1 ((T.map e.toEmbedding).pathCoverNumber - 1) := Nat.mul_le_mul_left _ hm

end OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1
