import FormalConjectures.ErdosProblems.«1034»
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
A rational-parameter version of the construction of Ma and Tang [MaTa25].
See https://staff.ustc.edu.cn/~jiema/Erdos-1034.pdf.
-/

open Filter Finset SimpleGraph
open scoped BigOperators

namespace TriangleTwoNeighbors

private def size (b : ℕ) (i : Fin 7) : ℕ :=
  if i = 6 then 682 * b else 1026 * b

private abbrev Blocks (b : ℕ) := Σ i : Fin 7, Fin (size b i)

private abbrev Vertex (b r : ℕ) := Fin (3162 * b) ⊕ (Blocks b ⊕ Fin r)

private def graph (b r : ℕ) : SimpleGraph (Vertex b r) where
  Adj u v := match u, v with
    | .inl _, .inr (.inl _) => True
    | .inr (.inl _), .inl _ => True
    | .inr (.inl u), .inr (.inl v) => u.1 = v.1 ∧ u ≠ v
    | _, _ => False
  symm := ⟨by
    rintro (u | (u | u)) (v | (v | v)) <;> simp [eq_comm]⟩
  loopless := ⟨by rintro (u | (u | u)) <;> simp⟩

private instance (b r : ℕ) : DecidableRel (graph b r).Adj := by
  rintro (u | (u | u)) (v | (v | v)) <;> dsimp [graph] <;> infer_instance

private def centerEmbedding (b r : ℕ) : Fin (3162 * b) ↪ Vertex b r :=
  ⟨Sum.inl, Sum.inl_injective⟩

private def blockEmbedding (b r : ℕ) : Blocks b ↪ Vertex b r :=
  ⟨fun v => Sum.inr (Sum.inl v),
    fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩

private def localEmbedding (b r : ℕ) (i : Fin 7) : Fin (size b i) ↪ Vertex b r :=
  ⟨fun x => blockEmbedding b r ⟨i, x⟩, fun _ _ h => by
    simpa using (blockEmbedding b r).injective h⟩

private lemma blockEmbedding_apply (b r : ℕ) (v : Blocks b) :
    blockEmbedding b r v = Sum.inr (Sum.inl v) := rfl

private lemma localEmbedding_apply (b r : ℕ) (i : Fin 7) (x : Fin (size b i)) :
    localEmbedding b r i x = Sum.inr (Sum.inl ⟨i, x⟩) := rfl

private def center (b r : ℕ) : Finset (Vertex b r) :=
  univ.map (centerEmbedding b r)

private def allBlocks (b r : ℕ) : Finset (Vertex b r) :=
  univ.map (blockEmbedding b r)

private def localBlock (b r : ℕ) (i : Fin 7) : Finset (Vertex b r) :=
  univ.map (localEmbedding b r i)

private lemma mem_local {b r : ℕ} (v : Blocks b) (i : Fin 7) :
    blockEmbedding b r v ∈ localBlock b r i ↔ v.1 = i := by
  constructor
  · intro h
    obtain ⟨w, _, hw⟩ := Finset.mem_map.1 h
    have he : (⟨i, w⟩ : Blocks b) = v := (blockEmbedding b r).injective hw
    exact (congrArg Sigma.fst he).symm
  · rcases v with ⟨j, w⟩
    intro hj
    change j = i at hj
    subst j
    exact Finset.mem_map.2 ⟨w, Finset.mem_univ _, rfl⟩

private lemma center_disjoint_local (b r : ℕ) (i : Fin 7) :
    Disjoint (center b r) (localBlock b r i) := by
  refine Finset.disjoint_left.2 ?_
  intro v hv hw
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hv
  obtain ⟨x, _, hx⟩ := Finset.mem_map.1 hw
  cases hx

private lemma sum_size (b : ℕ) : (∑ i : Fin 7, size b i) = 6838 * b := by
  norm_num [Fin.sum_univ_succ, size, Fin.ext_iff]
  omega

private lemma vertex_card (b r : ℕ) : Fintype.card (Vertex b r) = 10000 * b + r := by
  simp only [Vertex, Blocks, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, sum_size]
  omega

private lemma center_degree (b r : ℕ) (a : Fin (3162 * b)) :
    (graph b r).degree (Sum.inl a) = 6838 * b := by
  have h : (graph b r).neighborFinset (Sum.inl a) = allBlocks b r := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    rcases x with x | (x | x)
    · change False ↔ (Sum.inl x : Vertex b r) ∈ allBlocks b r
      simp [allBlocks, Finset.mem_map, blockEmbedding_apply]
    · change True ↔ (Sum.inr (Sum.inl x) : Vertex b r) ∈ allBlocks b r
      exact ⟨fun _ => Finset.mem_map.2 ⟨x, Finset.mem_univ _, rfl⟩, fun _ => trivial⟩
    · change False ↔ (Sum.inr (Sum.inr x) : Vertex b r) ∈ allBlocks b r
      simp [allBlocks, Finset.mem_map, blockEmbedding_apply]
  simp [SimpleGraph.degree, h, allBlocks, Blocks, Fintype.card_sigma, sum_size]

private lemma block_degree (b r : ℕ) (v : Blocks b) :
    (graph b r).degree (blockEmbedding b r v) = 3162 * b + (size b v.1 - 1) := by
  let L := localBlock b r v.1
  have hv : blockEmbedding b r v ∈ L := (mem_local v v.1).2 rfl
  have h : (graph b r).neighborFinset (blockEmbedding b r v) =
      center b r ∪ L.erase (blockEmbedding b r v) := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    rcases x with x | (x | x)
    · change True ↔ (Sum.inl x : Vertex b r) ∈ center b r ∪ L.erase _
      exact ⟨fun _ => Finset.mem_union_left _ (Finset.mem_map.2 ⟨x, Finset.mem_univ _, rfl⟩),
        fun _ => trivial⟩
    · change (v.1 = x.1 ∧ v ≠ x) ↔ blockEmbedding b r x ∈ center b r ∪ L.erase _
      have hcenter : blockEmbedding b r x ∉ center b r := by
        simp [center, centerEmbedding, blockEmbedding, Finset.mem_map]
      have hne : blockEmbedding b r x ≠ blockEmbedding b r v ↔ x ≠ v :=
        (blockEmbedding b r).injective.ne_iff
      simp only [Finset.mem_union, hcenter, false_or, Finset.mem_erase, hne, L, mem_local]
      exact ⟨fun ⟨hs, hd⟩ => ⟨hd.symm, hs.symm⟩, fun ⟨hd, hs⟩ => ⟨hs.symm, hd.symm⟩⟩
    · change False ↔ (Sum.inr (Sum.inr x) : Vertex b r) ∈ center b r ∪ L.erase _
      simp [center, centerEmbedding, L, localBlock, Finset.mem_map, localEmbedding_apply]
  have hdisj : Disjoint (center b r) (L.erase (blockEmbedding b r v)) :=
    (center_disjoint_local b r v.1).mono_right (Finset.erase_subset _ _)
  rw [SimpleGraph.degree, h, Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hv]
  simp [center, L, localBlock]

private lemma padding_degree (b r : ℕ) (v : Fin r) :
    (graph b r).degree (Sum.inr (Sum.inr v)) = 0 := by
  have h : (graph b r).neighborFinset (Sum.inr (Sum.inr v)) = ∅ := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    rcases x with x | (x | x) <;> exact iff_of_false id (Finset.notMem_empty _)
  rw [SimpleGraph.degree, h, Finset.card_empty]

/-- The degree sum counts cross edges twice and the ordered pairs within each clique. -/
private lemma twice_edges (b r : ℕ) (hb : 1 ≤ b) :
    2 * ((graph b r).edgeSet.ncard : ℝ) =
      50024692 * (b : ℝ) ^ 2 - 6838 * (b : ℝ) := by
  have h := (graph b r).sum_degrees_eq_twice_card_edges
  simp only [Vertex, Fintype.sum_sum_type] at h
  have hblocks (v : Blocks b) :
      (graph b r).degree (Sum.inr (Sum.inl v)) = 3162 * b + (size b v.1 - 1) :=
    block_degree b r v
  simp only [center_degree, hblocks, padding_degree, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_zero, add_zero] at h
  change 3162 * b * (6838 * b) +
    (∑ v : Σ i : Fin 7, Fin (size b i), (3162 * b + (size b v.1 - 1))) =
    2 * ((graph b r).edgeFinset.card) at h
  simp only [Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  norm_num [Fin.sum_univ_succ, size] at h
  have hbig : 1 ≤ 1026 * b := by omega
  have hsmall : 1 ≤ 682 * b := by omega
  have hr := congrArg (fun x : ℕ => (x : ℝ)) h
  push_cast [Nat.cast_sub hbig, Nat.cast_sub hsmall] at hr
  change _ = 2 * ((graph b r).edgeFinset.card : ℝ) at hr
  rw [Set.ncard_eq_toFinset_card']
  change 2 * ((graph b r).edgeFinset.card : ℝ) = _
  linarith only [hr]

private def region (b r : ℕ) (i : Fin 7) : Finset (Vertex b r) :=
  center b r ∪ localBlock b r i

private lemma adjacent_to_block {b r : ℕ} {i : Fin 7} {v : Blocks b} (hv : v.1 = i)
    {y : Vertex b r} (hy : (graph b r).Adj y (blockEmbedding b r v)) :
    y ∈ region b r i := by
  rcases y with y | (y | y)
  · exact Finset.mem_union_left _ (Finset.mem_map.2 ⟨y, Finset.mem_univ _, rfl⟩)
  · have hy' : y.1 = v.1 := hy.1
    exact Finset.mem_union_right _ ((mem_local y i).2 (hy'.trans hv))
  · exact False.elim hy

private lemma triangle_bound {b r : ℕ} {T Y : Finset (Vertex b r)}
    (hT : (graph b r).IsNClique 3 T) (hY : Erdos1034.JoinedToTwo (graph b r) T Y) :
    Y.card ≤ 4188 * b := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (by rw [hT.card_eq]; decide)
  have huvAdj := hT.isClique hu hv huv
  have hblock : ∃ t : Blocks b, blockEmbedding b r t ∈ T := by
    rcases u with u | (u | u)
    · rcases v with v | (v | v)
      · exact False.elim huvAdj
      · exact ⟨v, hv⟩
      · exact False.elim huvAdj
    · exact ⟨u, hu⟩
    · rcases v with v | (v | v) <;> exact False.elim huvAdj
  obtain ⟨t, ht⟩ := hblock
  let i := t.1
  have hregion : T ⊆ region b r i := by
    intro x hx
    by_cases he : x = blockEmbedding b r t
    · subst x
      exact Finset.mem_union_right _ ((mem_local t i).2 rfl)
    · exact adjacent_to_block rfl (hT.isClique hx ht he)
  have hsub : Y ⊆ region b r i := by
    intro y hy
    by_contra hnot
    obtain ⟨x, hx, z, hz, hxz, hyx, hyz⟩ := hY y hy
    have hcenter {w : Vertex b r} (hw : w ∈ T) (hyw : (graph b r).Adj y w) :
        ∃ a : Fin (3162 * b), w = Sum.inl a := by
      rcases w with w | (w | w)
      · exact ⟨w, rfl⟩
      · have hwr := Finset.mem_union.1 (hregion hw)
        have hnc : blockEmbedding b r w ∉ center b r := by
          simp [center, centerEmbedding, blockEmbedding, Finset.mem_map]
        have hwi : w.1 = i := (mem_local w i).1 (hwr.resolve_left hnc)
        exact False.elim (hnot (adjacent_to_block hwi hyw))
      · rcases y with y | (y | y) <;> exact False.elim hyw
    obtain ⟨a, rfl⟩ := hcenter hx hyx
    obtain ⟨c, rfl⟩ := hcenter hz hyz
    exact hT.isClique hx hz hxz
  calc
    Y.card ≤ (region b r i).card := Finset.card_le_card hsub
    _ ≤ (center b r).card + (localBlock b r i).card := Finset.card_union_le _ _
    _ = 3162 * b + size b i := by simp [center, localBlock]
    _ ≤ 4188 * b := by unfold size; split <;> omega

private lemma edge_threshold (n b r : ℕ) (hb : 5000 ≤ b) (hn : n < 10000 * (b + 1)) :
    (n : ℝ) ^ 2 / 4 < ((graph b r).edgeSet.ncard : ℝ) := by
  have h := twice_edges b r (by omega)
  have hbR : (5000 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := by linarith
  have hnR : (n : ℝ) < 10000 * ((b : ℝ) + 1) := by exact_mod_cast hn
  have hsum : (0 : ℝ) < 10000 * ((b : ℝ) + 1) + (n : ℝ) := by positivity
  have hsq := mul_pos (sub_pos.mpr hnR) hsum
  have hgap : (10000 : ℝ) < 24692 * (b : ℝ) - 100006838 := by linarith
  have hp := mul_pos (sub_pos.mpr hgap) hbpos
  nlinarith only [h, hsq, hp, hbR]

end TriangleTwoNeighbors

open TriangleTwoNeighbors in
theorem OMA.solution : type_of% @Erdos1034.erdos_1034.variants.upper_bound := by
  intro ε hε
  filter_upwards [Filter.eventually_ge_atTop (50000000 : ℕ)] with n hn
  let b := n / 10000
  let r := n - 10000 * b
  have hb : 5000 ≤ b := by dsimp [b]; omega
  have hl : 10000 * b ≤ n := Nat.mul_div_le _ _
  have hu : n < 10000 * (b + 1) := Nat.lt_mul_div_succ _ (by decide)
  have hc : Fintype.card (Vertex b r) = n := by rw [vertex_card]; dsimp [r]; omega
  let e := Fintype.equivFinOfCardEq hc
  let G := (graph b r).comap e.symm
  let I : G ≃g graph b r := SimpleGraph.Iso.comap e.symm (graph b r)
  classical
  refine ⟨G, ?_, ?_⟩
  · have he : G.edgeSet.ncard = (graph b r).edgeSet.ncard := by
      rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
      exact I.card_edgeFinset_eq
    rw [he]
    exact edge_threshold n b r hb hu
  · intro T hT Y hY
    have ht : (graph b r).IsNClique 3 (T.map e.symm.toEmbedding) := by
      refine ⟨?_, (Finset.card_map _).trans hT.card_eq⟩
      intro x hx y hy hxy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.1 hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hy
      exact hT.isClique hu hv (fun huv => hxy (congrArg e.symm huv))
    have hy : Erdos1034.JoinedToTwo (graph b r) (T.map e.symm.toEmbedding)
        (Y.map e.symm.toEmbedding) := by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hy
      obtain ⟨u, hu, w, hw, huw, hvu, hvw⟩ := hY v hv
      exact ⟨e.symm u, Finset.mem_map.2 ⟨u, hu, rfl⟩,
        e.symm w, Finset.mem_map.2 ⟨w, hw, rfl⟩,
        fun h => huw (e.symm.injective h), hvu, hvw⟩
    have hh := triangle_bound ht hy
    rw [Finset.card_map] at hh
    have hhR : (Y.card : ℝ) ≤ 4188 * (b : ℝ) := by exact_mod_cast hh
    have hlR : (10000 : ℝ) * (b : ℝ) ≤ n := by exact_mod_cast hl
    have hs : Real.sqrt (5 / 2) ≤ (15812 : ℝ) / 10000 := by
      rw [Real.sqrt_le_iff]
      norm_num
    have hcoeff : (4188 : ℝ) / 10000 ≤ 2 - Real.sqrt (5 / 2) + ε := by linarith
    calc
      (Y.card : ℝ) ≤ 4188 * (b : ℝ) := hhR
      _ ≤ (4188 / 10000 : ℝ) * (n : ℝ) := by linarith
      _ ≤ (2 - Real.sqrt (5 / 2) + ε) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n)