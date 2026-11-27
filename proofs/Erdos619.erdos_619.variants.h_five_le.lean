import FormalConjectures.ErdosProblems.«619»

/-!
The star extension follows Erdős, Gyárfás and Ruszinkó, Theorems 4.2 and 4.4.
See https://users.renyi.hu/~gyarfas/Cikkek/90_howtodecrease.pdf.
-/

open Finset SimpleGraph

namespace TriangleFreeDiameterFive

variable {V : Type*} [DecidableEq V]

/-- A maximal independent set dominates the finite set in which it was chosen. -/
private lemma indep_dominates (G : SimpleGraph V) (C : Finset V) :
    ∃ S ⊆ C, G.IsIndepSet (S : Set V) ∧
      ∀ v ∈ C, v ∈ S ∨ ∃ x ∈ S, G.Adj v x := by
  classical
  let family : Finset (Finset V) := C.powerset.filter fun (S : Finset V) => G.IsIndepSet (S : Set V)
  have hne : family.Nonempty := ⟨∅, by simp [family, SimpleGraph.isIndepSet_iff]⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image family Finset.card hne
  have hmem := Finset.mem_filter.1 hS
  have hsub : S ⊆ C := Finset.mem_powerset.1 hmem.1
  have hi : G.IsIndepSet (S : Set V) := hmem.2
  refine ⟨S, hsub, hi, ?_⟩
  intro v hv
  by_cases hvS : v ∈ S
  · exact Or.inl hvS
  · right
    by_contra! hn
    have hnew : G.IsIndepSet (↑(insert v S) : Set V) := by
      intro x hx y hy hxy hAdj
      change x ∈ insert v S at hx
      change y ∈ insert v S at hy
      rcases Finset.mem_insert.1 hx with hxv | hxS
      · subst x
        rcases Finset.mem_insert.1 hy with hyv | hyS
        · exact hxy hyv.symm
        · exact hn y hyS hAdj
      · rcases Finset.mem_insert.1 hy with hyv | hyS
        · subst y
          exact hn x hxS hAdj.symm
        · exact hi hxS hyS hxy hAdj
    have hnewMem : insert v S ∈ family :=
      Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.insert_subset_iff.2 ⟨hv, hsub⟩), hnew⟩
    have hcard := hmax (insert v S) hnewMem
    rw [Finset.card_insert_of_notMem hvS] at hcard
    omega

/-- A maximal independent set and its complement both dominate a graph without isolates. -/
private lemma small_dominating [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hAdj : ∀ v, ∃ w, G.Adj v w) :
    ∃ C : Finset V, C.Nonempty ∧ 2 * C.card ≤ Fintype.card V ∧
      ∀ v, ∃ c ∈ C, G.edist v c ≤ 1 := by
  classical
  obtain ⟨S, _, hi, hs⟩ := indep_dominates G (univ : Finset V)
  let T := (univ : Finset V) \ S
  have hdS (v : V) : ∃ c ∈ S, G.edist v c ≤ 1 := by
    rcases hs v (Finset.mem_univ _) with hv | ⟨c, hc, hvc⟩
    · exact ⟨v, hv, by simp⟩
    · exact ⟨c, hc, G.edist_le_one_iff_adj_or_eq.2 (Or.inl hvc)⟩
  have hdT (v : V) : ∃ c ∈ T, G.edist v c ≤ 1 := by
    by_cases hv : v ∈ S
    · obtain ⟨w, hw⟩ := hAdj v
      have hn : w ∉ S := by
        intro hwS
        exact hi hv hwS hw.ne hw
      exact ⟨w, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hn⟩,
        G.edist_le_one_iff_adj_or_eq.2 (Or.inl hw)⟩
    · exact ⟨v, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hv⟩, by simp⟩
  have hcard : T.card + S.card = Fintype.card V := by
    simpa [T] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  let v : V := Classical.choice inferInstance
  obtain ⟨s, hsS, _⟩ := hdS v
  obtain ⟨t, htT, _⟩ := hdT v
  by_cases hc : S.card ≤ T.card
  · exact ⟨S, ⟨s, hsS⟩, by omega, hdS⟩
  · exact ⟨T, ⟨t, htT⟩, by omega, hdT⟩

private def starEdges (p : V) (S : Finset V) : Finset (Sym2 V) :=
  S.image fun x => s(p, x)

private def extend (G : SimpleGraph V) (F : Finset (Sym2 V)) : SimpleGraph V :=
  G ⊔ SimpleGraph.fromEdgeSet (F : Set (Sym2 V))

omit [DecidableEq V] in
private lemma le_extend (G : SimpleGraph V) (F : Finset (Sym2 V)) : G ≤ extend G F :=
  le_sup_left

private lemma star_adj_iff {G : SimpleGraph V} {p x y : V} {S : Finset V} (hp : p ∉ S) :
    (extend G (starEdges p S)).Adj x y ↔
      G.Adj x y ∨ (x = p ∧ y ∈ S) ∨ (y = p ∧ x ∈ S) := by
  simp only [extend, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
    starEdges, Finset.mem_image, Sym2.eq_iff]
  constructor
  · rintro (h | ⟨⟨v, hv, h | h⟩, _⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h.1.symm, h.2 ▸ hv⟩)
    · exact Or.inr (Or.inr ⟨h.1.symm, h.2 ▸ hv⟩)
  · rintro (h | ⟨rfl, hy⟩ | ⟨rfl, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨y, hy, Or.inl ⟨rfl, rfl⟩⟩, fun h => hp (h ▸ hy)⟩
    · exact Or.inr ⟨⟨x, hx, Or.inr ⟨rfl, rfl⟩⟩, fun h => hp (h ▸ hx)⟩

omit [DecidableEq V] in
private lemma adj_le_one {G : SimpleGraph V} {x y : V} (h : G.Adj x y) :
    G.edist x y ≤ 1 :=
  G.edist_le_one_iff_adj_or_eq.2 (Or.inl h)

omit [DecidableEq V] in
private lemma via {G : SimpleGraph V} {x y z : V} {a b : ℕ∞}
    (hxy : G.edist x y ≤ a) (hyz : G.edist y z ≤ b) :
    G.edist x z ≤ a + b :=
  G.edist_triangle.trans (add_le_add hxy hyz)

/-- All new triangles would contain the pivot, where the old and new neighbors are independent. -/
private lemma star_cliqueFree {G : SimpleGraph V} (hG : G.CliqueFree 3)
    {p : V} {S : Finset V} (hp : p ∉ S) (hi : G.IsIndepSet (S : Set V))
    (hfar : ∀ x ∈ S, 2 < G.edist p x) :
    (extend G (starEdges p S)).CliqueFree 3 := by
  let H := extend G (starEdges p S)
  have hnotpivot {x y : V} (hx : x ≠ p) (hy : y ≠ p) (hadj : H.Adj x y) :
      G.Adj x y := by
    rcases (star_adj_iff hp).1 hadj with hg | ⟨h, _⟩ | ⟨h, _⟩
    · exact hg
    · exact False.elim (hx h)
    · exact False.elim (hy h)
  have hpivot {x : V} (hadj : H.Adj p x) : G.Adj p x ∨ x ∈ S := by
    rcases (star_adj_iff hp).1 hadj with hg | ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl hg
    · exact Or.inr h
    · exact False.elim (hp h)
  have hnone {x y : V} (hpx : H.Adj p x) (hpy : H.Adj p y) (hxy : H.Adj x y) : False := by
    have he := hnotpivot hpx.ne.symm hpy.ne.symm hxy
    rcases hpivot hpx with hx | hx <;> rcases hpivot hpy with hy | hy
    · exact hG _ (SimpleGraph.is3Clique_triple_iff.2 ⟨hx, hy, he⟩)
    · have h : G.edist p y ≤ 2 := via (adj_le_one hx) (adj_le_one he)
      exact (hfar y hy).not_ge h
    · have h : G.edist p x ≤ 2 := via (adj_le_one hy) (adj_le_one he.symm)
      exact (hfar x hx).not_ge h
    · exact hi hx hy he.ne he
  intro T hT
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := SimpleGraph.is3Clique_iff.1 hT
  by_cases hx : x = p
  · subst x
    exact hnone hxy hxz hyz
  by_cases hy : y = p
  · subst y
    exact hnone hxy.symm hyz hxz
  by_cases hz : z = p
  · subst z
    exact hnone hxz.symm hyz.symm hxy
  exact hG _ (SimpleGraph.is3Clique_triple_iff.2
    ⟨hnotpivot hx hy hxy, hnotpivot hx hz hxz, hnotpivot hy hz hyz⟩)


private lemma extend_union (G : SimpleGraph V) (E F : Finset (Sym2 V)) :
    extend G (E ∪ F) = extend (extend G E) F := by
  simp [extend, sup_assoc]

/-- Bring a specified set of centers to pairwise distance at most three. -/
private lemma close_centers (C : Finset V) (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    ∃ F : Finset (Sym2 V), F.card ≤ C.card - 1 ∧ (extend G F).CliqueFree 3 ∧
      ∀ x ∈ C, ∀ y ∈ C, (extend G F).edist x y ≤ 3 := by
  classical
  induction C using Finset.strongInductionOn generalizing G with
  | _ C ih =>
    by_cases hC : C = ∅
    · subst C
      refine ⟨∅, by simp, ?_, by simp⟩
      simpa [extend] using hG
    obtain ⟨p, hpC⟩ := Finset.nonempty_iff_ne_empty.2 hC
    let A := C.filter fun x => 2 < G.edist p x
    obtain ⟨S, hSA, hInd, hdom⟩ := indep_dominates G A
    have hSC : S ⊆ C := hSA.trans (Finset.filter_subset _ _)
    have hfar (x : V) (hx : x ∈ S) : 2 < G.edist p x := (Finset.mem_filter.1 (hSA hx)).2
    have hpS : p ∉ S := by
      intro hp
      simpa using hfar p hp
    let E := starEdges p S
    let H := extend G E
    have hH : H.CliqueFree 3 := star_cliqueFree hG hpS hInd hfar
    have hstep (x : V) (hx : x ∈ S) : H.Adj p x :=
      (star_adj_iff hpS).2 (Or.inr (Or.inl ⟨rfl, hx⟩))
    have hnear (x : V) (hx : x ∈ C) : H.edist p x ≤ 2 := by
      by_cases hf : 2 < G.edist p x
      · have hxA : x ∈ A := Finset.mem_filter.2 ⟨hx, hf⟩
        rcases hdom x hxA with hs | ⟨z, hz, hxz⟩
        · exact (adj_le_one (hstep x hs)).trans (by decide)
        · exact via (adj_le_one (hstep z hz)) (adj_le_one ((le_extend G E) hxz.symm))
      · exact (SimpleGraph.edist_anti (le_extend G E)).trans (le_of_not_gt hf)
    let D := insert p S
    let R := C \ D
    have hDC : D ⊆ C := Finset.insert_subset_iff.2 ⟨hpC, hSC⟩
    have hR : R ⊂ C := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.sdiff_subset, ?_⟩
      intro he
      exact (Finset.mem_sdiff.1 (show p ∈ R from he.symm ▸ hpC)).2 (Finset.mem_insert_self _ _)
    have hremoved (x : V) (hx : x ∈ D) (y : V) (hy : y ∈ C) :
        H.edist x y ≤ 3 := by
      rcases Finset.mem_insert.1 hx with rfl | hs
      · exact (hnear y hy).trans (by decide)
      · exact via (adj_le_one (hstep x hs).symm) (hnear y hy)
    obtain ⟨F, hFcard, hFtri, hFdist⟩ := ih R hR H hH
    have hcard : R.card + (S.card + 1) = C.card := by
      have hc := Finset.card_sdiff_add_card_eq_card hDC
      simpa [R, D, Finset.card_insert_of_notMem hpS] using hc
    have hEcard : E.card ≤ S.card := Finset.card_image_le
    refine ⟨E ∪ F, ?_, ?_, ?_⟩
    · have h := Finset.card_union_le E F
      omega
    · rw [extend_union]
      exact hFtri
    · rw [extend_union]
      intro x hx y hy
      by_cases hxD : x ∈ D
      · exact (SimpleGraph.edist_anti (le_extend H F)).trans (hremoved x hxD y hy)
      by_cases hyD : y ∈ D
      · rw [SimpleGraph.edist_comm]
        exact (SimpleGraph.edist_anti (le_extend H F)).trans (hremoved y hyD x hx)
      · exact hFdist x (Finset.mem_sdiff.2 ⟨hx, hxD⟩) y (Finset.mem_sdiff.2 ⟨hy, hyD⟩)

omit [DecidableEq V] in
private lemma new_edges_le (G : SimpleGraph V) (F : Finset (Sym2 V)) :
    ((extend G F) \ G).edgeSet.ncard ≤ F.card := by
  have h : ((extend G F) \ G).edgeSet ⊆ (F : Set (Sym2 V)) := by
    rw [extend, SimpleGraph.edgeSet_sdiff, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet]
    intro e he
    rcases he.1 with hg | hf
    · exact False.elim (he.2 hg)
    · exact hf.1
  simpa using Set.ncard_le_ncard h

end TriangleFreeDiameterFive

open TriangleFreeDiameterFive in
theorem OMA.solution : type_of% @Erdos619.erdos_619.variants.h_five_le := by
  intro V _ G hG htri
  classical
  let hNonempty : Nonempty V := hG.nonempty
  by_cases hType : Nontrivial V
  · obtain ⟨C, hC, hcard, hdom⟩ :=
      small_dominating G (fun v => hG.preconnected.exists_adj_of_nontrivial v)
    obtain ⟨F, hFcard, hFtri, hFdist⟩ := close_centers C G htri
    let H := extend G F
    have hle : G ≤ H := le_extend G F
    have hdiam : H.ediam ≤ 5 := by
      apply ediam_le_of_edist_le
      intro u v
      obtain ⟨x, hx, hux⟩ := hdom u
      obtain ⟨y, hy, hvy⟩ := hdom v
      have hu : H.edist u x ≤ 1 := (SimpleGraph.edist_anti hle).trans hux
      have hv : H.edist y v ≤ 1 := by
        rw [SimpleGraph.edist_comm]
        exact (SimpleGraph.edist_anti hle).trans hvy
      exact via (via hu (hFdist x hx y hy)) hv
    have hinf : Erdos619.minNewEdges 5 G ≤ ((H \ G).edgeSet.ncard) :=
      Nat.sInf_le ⟨H, hle, hFtri, hdiam, rfl⟩
    have hbudget := hinf.trans (new_edges_le G F)
    have hCcard := Finset.card_pos.2 hC
    have hn : 2 * Erdos619.minNewEdges 5 G + 1 ≤ Fintype.card V := by omega
    have hnR : (2 : ℝ) * (Erdos619.minNewEdges 5 G : ℝ) + 1 ≤ Fintype.card V := by
      exact_mod_cast hn
    linarith
  · have hSub : Subsingleton V := not_nontrivial_iff_subsingleton.1 hType
    have hdiam : G.ediam ≤ 5 := by rw [ediam_eq_zero_of_subsingleton]; decide
    have hzero : Erdos619.minNewEdges 5 G ≤ 0 :=
      Nat.sInf_le ⟨G, le_rfl, htri, hdiam, by simp⟩
    have hcard : 1 ≤ Fintype.card V := Fintype.card_pos
    have hcardR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
    rw [Nat.le_zero.1 hzero, Nat.cast_zero]
    linarith