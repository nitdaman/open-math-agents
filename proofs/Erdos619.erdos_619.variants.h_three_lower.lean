import FormalConjectures.ErdosProblems.«619»
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
The diameter-three counting argument follows Alon, Gyárfás and Ruszinkó,
*Decreasing the Diameter of Bounded Degree Graphs*, Theorem 2.3.
See https://web.math.princeton.edu/~nalon/PDFS/agr6.pdf.
-/

open Finset SimpleGraph
open scoped BigOperators

namespace DiameterThreeLower

variable {V : Type*} [Fintype V]

private def componentVertices (R : SimpleGraph V) :
    V ≃ Σ C : R.ConnectedComponent, C :=
  { toFun := fun v => ⟨R.connectedComponentMk v, ⟨v, rfl⟩⟩
    invFun := fun x => x.2.val
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨C, v, hv⟩
      change R.connectedComponentMk v = C at hv
      subst C
      rfl }

private def componentEdge (R : SimpleGraph V) :
    (Σ C : R.ConnectedComponent, C.toSimpleGraph.edgeSet) → R.edgeSet :=
  fun ⟨C, e, he⟩ => ⟨Sym2.map Subtype.val e, by
    induction e using Sym2.inductionOn
    exact he⟩

omit [Fintype V] in
private lemma componentEdge_injective (R : SimpleGraph V) :
    Function.Injective (componentEdge R) := by
  rintro ⟨C, e, he⟩ ⟨D, f, hf⟩ h
  have hm : Sym2.map Subtype.val e = Sym2.map Subtype.val f := congrArg Subtype.val h
  have hCD : C = D := by
    clear h he hf
    revert hm
    induction e using Sym2.inductionOn with
    | _ a b =>
      induction f using Sym2.inductionOn with
      | _ c d =>
        intro hm
        rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at hm
        rcases hm with ⟨hm, _⟩ | ⟨hm, _⟩
        · exact a.property.symm.trans ((congrArg R.connectedComponentMk hm).trans c.property)
        · exact a.property.symm.trans ((congrArg R.connectedComponentMk hm).trans d.property)
  subst D
  have hEF := Sym2.map.injective Subtype.val_injective hm
  subst f
  rfl

/-- Each tree component can account for one missing edge. -/
private lemma edges_with_tree_roots (R : SimpleGraph V) (X : Finset V)
    (hX : ∀ C : R.ConnectedComponent, C.toSimpleGraph.IsTree → ∃ x ∈ X, x ∈ C) :
    Fintype.card V ≤ R.edgeSet.ncard + X.card := by
  classical
  let : Fintype R.ConnectedComponent := Fintype.ofFinite _
  let (C : R.ConnectedComponent) : Fintype C := Fintype.ofFinite _
  let (C : R.ConnectedComponent) : Fintype C.toSimpleGraph.edgeSet := Fintype.ofFinite _
  let : Fintype R.edgeSet := Fintype.ofFinite _
  let T : Finset R.ConnectedComponent := univ.filter fun C => C.toSimpleGraph.IsTree
  have hC (C : R.ConnectedComponent) :
      Fintype.card C ≤ Fintype.card C.toSimpleGraph.edgeSet +
        (if C.toSimpleGraph.IsTree then 1 else 0) := by
    have hn := C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hn
    by_cases ht : C.toSimpleGraph.IsTree
    · simpa [ht] using hn
    · have hne : Fintype.card C.toSimpleGraph.edgeSet + 1 ≠ Fintype.card C := by
        intro he
        apply ht
        refine (SimpleGraph.isTree_iff_connected_and_card).2 ⟨C.connected_toSimpleGraph, ?_⟩
        simpa only [Nat.card_eq_fintype_card] using he
      simp only [ht, if_false, add_zero]
      omega
  have hv : Fintype.card V = ∑ C : R.ConnectedComponent, Fintype.card C := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (componentVertices R)
  have he : (∑ C : R.ConnectedComponent, Fintype.card C.toSimpleGraph.edgeSet) ≤
      R.edgeSet.ncard := by
    rw [← Fintype.card_sigma, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective _ (componentEdge_injective R)
  have hroot (C : T) : ∃ x ∈ X, x ∈ (C : R.ConnectedComponent) :=
    hX C (Finset.mem_filter.1 C.property).2
  choose root hrootX hrootC using hroot
  let f : T → X := fun C => ⟨root C, hrootX C⟩
  have hf : Function.Injective f := by
    intro C D h
    apply Subtype.ext
    have heq : root C = root D := congrArg Subtype.val h
    have hC' : R.connectedComponentMk (root C) = C.val := hrootC C
    have hD' : R.connectedComponentMk (root D) = D.val := hrootC D
    exact hC'.symm.trans (heq ▸ hD')
  have ht := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe, Fintype.card_coe] at ht
  have hs : (∑ C : R.ConnectedComponent, if C.toSimpleGraph.IsTree then (1 : ℕ) else 0) =
      T.card := by
    rw [← Finset.sum_filter]
    simp [T]
  have hh := Finset.sum_le_sum (s := (univ : Finset R.ConnectedComponent)) (fun C _ => hC C)
  rw [← hv, Finset.sum_add_distrib, hs] at hh
  omega

private lemma trees_have_leaf (R : SimpleGraph V) (C : R.ConnectedComponent)
    (ht : C.toSimpleGraph.IsTree) :
    ∃ x ∈ C, ∀ a b, R.Adj x a → R.Adj x b → a = b := by
  classical
  let : Fintype C := Fintype.ofFinite _
  let : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  have liftAdj {x : C} {a b : V} (ha : R.Adj x.val a) (hb : R.Adj x.val b) :
      C.toSimpleGraph.Adj x ⟨a, C.mem_supp_of_adj_mem_supp x.property ha⟩ ∧
      C.toSimpleGraph.Adj x ⟨b, C.mem_supp_of_adj_mem_supp x.property hb⟩ := ⟨ha, hb⟩
  by_cases hn : Nontrivial C
  · obtain ⟨x, hx⟩ := ht.exists_vert_degree_one_of_nontrivial
    obtain ⟨w, _, hw⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.1 hx
    refine ⟨x.val, x.property, fun a b ha hb => ?_⟩
    obtain ⟨ha', hb'⟩ := liftAdj ha hb
    exact congrArg Subtype.val ((hw _ ha').trans (hw _ hb').symm)
  · have hs : Subsingleton C := not_nontrivial_iff_subsingleton.1 hn
    obtain ⟨x⟩ := C.connected_toSimpleGraph.nonempty
    refine ⟨x.val, x.property, fun a b ha hb => ?_⟩
    exact congrArg Subtype.val (hs.elim
      ⟨a, C.mem_supp_of_adj_mem_supp x.property ha⟩
      ⟨b, C.mem_supp_of_adj_mem_supp x.property hb⟩)


private lemma roots_exist (R : SimpleGraph V) :
    ∃ T : Finset V,
      (∀ C : R.ConnectedComponent, C.toSimpleGraph.IsTree → ∃ x ∈ T, x ∈ C) ∧
      (∀ x ∈ T, ∀ a b, R.Adj x a → R.Adj x b → a = b) ∧
      Set.InjOn R.connectedComponentMk (T : Set V) := by
  classical
  let K := {C : R.ConnectedComponent // C.toSimpleGraph.IsTree}
  let : Fintype K := Fintype.ofFinite _
  have h (C : K) := trees_have_leaf R C.val C.property
  choose root hC hleaf using h
  let T := univ.image root
  refine ⟨T, ?_, ?_, ?_⟩
  · intro C ht
    exact ⟨root ⟨C, ht⟩, Finset.mem_image_of_mem root (Finset.mem_univ _), hC _⟩
  · intro x hx
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.1 hx
    exact hleaf C
  · intro x hx y hy he
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.1 hy
    have h1 : R.connectedComponentMk (root C) = C.val := hC C
    have h2 : R.connectedComponentMk (root D) = D.val := hC D
    exact congrArg root (Subtype.ext (h1.symm.trans (he.trans h2)))

private def inside (R : SimpleGraph V) (X : Finset V) : SimpleGraph V where
  Adj x y := R.Adj x y ∧ x ∈ X ∧ y ∈ X
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

private def outside (R : SimpleGraph V) (X : Finset V) : SimpleGraph V where
  Adj x y := R.Adj x y ∧ ¬ (x ∈ X ∧ y ∈ X)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun he => h.2 ⟨he.2, he.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

private lemma edge_split (R : SimpleGraph V) (X : Finset V) :
    R.edgeSet.ncard = (outside R X).edgeSet.ncard + (inside R X).edgeSet.ncard := by
  classical
  have he : (outside R X).edgeSet ∪ (inside R X).edgeSet = R.edgeSet := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp only [Set.mem_union, SimpleGraph.mem_edgeSet]
      change ((R.Adj x y ∧ ¬ (x ∈ X ∧ y ∈ X)) ∨ (R.Adj x y ∧ x ∈ X ∧ y ∈ X)) ↔ R.Adj x y
      tauto
  have hd : Disjoint (outside R X).edgeSet (inside R X).edgeSet := by
    apply Set.disjoint_left.2
    intro e
    induction e using Sym2.inductionOn with
    | _ x y =>
      intro ho hi
      exact ho.2 hi.2
  rw [← he, Set.ncard_union_eq hd]

omit [Fintype V] in
private lemma outside_tree_roots (R : SimpleGraph V) (X : Finset V)
    (hX : ∀ C : R.ConnectedComponent, C.toSimpleGraph.IsTree → ∃ x ∈ X, x ∈ C) :
    ∀ C : (outside R X).ConnectedComponent, C.toSimpleGraph.IsTree → ∃ x ∈ X, x ∈ C := by
  intro C ht
  by_contra! hbad
  let R' := outside R X
  have hstep {v w : V} (hv : v ∈ C) (he : R.Adj v w) : R'.Adj v w :=
    ⟨he, fun h => hbad v h.1 hv⟩
  have hreach {v w : V} (p : R.Walk v w) : v ∈ C → w ∈ C := by
    induction p with
    | nil => exact id
    | cons h _ ih =>
      exact fun hv => ih (C.mem_supp_of_adj_mem_supp hv (hstep hv h))
  obtain ⟨u, hu⟩ := C.nonempty_supp
  let D := R.connectedComponentMk u
  have hsub : D.supp ⊆ C.supp := by
    intro v hv
    obtain ⟨p⟩ := D.reachable_of_mem_supp (show u ∈ D from rfl) hv
    exact hreach p hu
  let f : D.toSimpleGraph →g C.toSimpleGraph :=
    { toFun := fun v => ⟨v.val, hsub v.property⟩
      map_rel' := by
        intro x y h
        exact hstep (hsub x.property) h }
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (congrArg (fun v : C => v.val) h)
  have htD : D.toSimpleGraph.IsTree :=
    ⟨D.connected_toSimpleGraph, ht.isAcyclic.comap f hf⟩
  obtain ⟨v, hvX, hvD⟩ := hX D htD
  exact hbad v hvX (hsub hvD)


private noncomputable def closedOne (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact univ.filter fun y => x = y ∨ G.Adj x y

private lemma mem_closedOne {G : SimpleGraph V} {x y : V} :
    y ∈ closedOne G x ↔ x = y ∨ G.Adj x y := by
  classical
  simp [closedOne]

private lemma closedOne_symm {G : SimpleGraph V} {x y : V}
    (hy : y ∈ closedOne G x) : x ∈ closedOne G y := by
  rcases mem_closedOne.1 hy with he | h
  · exact mem_closedOne.2 (Or.inl he.symm)
  · exact mem_closedOne.2 (Or.inr h.symm)

private def pathOne {n : ℕ} (x : Fin n) : Finset (Fin n) :=
  {x, ⟨x.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩,
    if h : x.val + 1 < n then ⟨x.val + 1, h⟩ else x}

private lemma pathOne_card {n : ℕ} (x : Fin n) : (pathOne x).card ≤ 3 := by
  unfold pathOne
  apply (Finset.card_insert_le _ _).trans
  exact Nat.add_le_add_right ((Finset.card_insert_le _ _).trans (by simp)) _

private lemma mem_pathOne {n : ℕ} {x y : Fin n} (h : x = y ∨ (pathGraph n).Adj x y) :
    y ∈ pathOne x := by
  rcases h with rfl | h
  · simp [pathOne]
  rcases pathGraph_adj.1 h with h | h
  · have hlt : x.val + 1 < n := h ▸ y.isLt
    have he : y = ⟨x.val + 1, hlt⟩ := Fin.ext h.symm
    simp [pathOne, hlt, he]
  · have he : y = ⟨x.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩ := by
      apply Fin.ext
      change y.val = x.val - 1
      omega
    simp [pathOne, he]

private noncomputable def rootsNear (H : SimpleGraph V) (T : Finset V) (x : V) : Finset V :=
  by classical exact T ∩ closedOne H x

private lemma mem_rootsNear {H : SimpleGraph V} {T : Finset V} {x y : V} :
    y ∈ rootsNear H T x ↔ y ∈ T ∧ y ∈ closedOne H x := by
  classical
  simp [rootsNear]

private lemma closedOne_card_at_root {n : ℕ} {H R : SimpleGraph (Fin n)}
    (hs : ∀ ⦃x y⦄, H.Adj x y → (pathGraph n).Adj x y ∨ R.Adj x y)
    {x : Fin n} (hroot : ∀ a b, R.Adj x a → R.Adj x b → a = b) :
    (closedOne H x).card ≤ 4 := by
  classical
  let A := univ.filter (R.Adj x)
  have hc : A.card ≤ 1 := Finset.card_le_one_iff.2 fun {a b} ha hb =>
    hroot a b (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
  have hsub : closedOne H x ⊆ pathOne x ∪ A := by
    intro y hy
    rcases mem_closedOne.1 hy with he | hadj
    · exact Finset.mem_union_left _ (mem_pathOne (Or.inl he))
    · rcases hs hadj with hb | hr
      · exact Finset.mem_union_left _ (mem_pathOne (Or.inr hb))
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hr⟩)
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hp := pathOne_card x
  omega

private lemma rootsNear_card {n : ℕ} {H R : SimpleGraph (Fin n)} {T : Finset (Fin n)}
    (hs : ∀ ⦃x y⦄, H.Adj x y → (pathGraph n).Adj x y ∨ R.Adj x y)
    (hroot : Set.InjOn R.connectedComponentMk (T : Set (Fin n))) (x : Fin n) :
    (rootsNear H T x).card ≤ 4 := by
  classical
  let A := T.filter (R.Adj x)
  have hc : A.card ≤ 1 := by
    refine Finset.card_le_one_iff.2 fun {a b} ha hb => ?_
    obtain ⟨haT, haR⟩ := Finset.mem_filter.1 ha
    obtain ⟨hbT, hbR⟩ := Finset.mem_filter.1 hb
    exact hroot haT hbT (SimpleGraph.ConnectedComponent.sound (haR.symm.reachable.trans hbR.reachable))
  have hsub : rootsNear H T x ⊆ pathOne x ∪ A := by
    intro y hy
    obtain ⟨hyT, hyH⟩ := mem_rootsNear.1 hy
    rcases mem_closedOne.1 hyH with he | hadj
    · exact Finset.mem_union_left _ (mem_pathOne (Or.inl he))
    · rcases hs hadj with hb | hr
      · exact Finset.mem_union_left _ (mem_pathOne (Or.inr hb))
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hyT, hr⟩)
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hp := pathOne_card x
  omega

/-- A short walk can be padded by repetitions to have two specified internal vertices. -/
private lemma padded_walk {H : SimpleGraph V} {u v : V} (w : H.Walk u v) (hw : w.length ≤ 3) :
    ∃ a b, a ∈ closedOne H u ∧ b ∈ closedOne H a ∧ v ∈ closedOne H b := by
  cases w with
  | nil => exact ⟨_, _, mem_closedOne.2 (Or.inl rfl), mem_closedOne.2 (Or.inl rfl),
      mem_closedOne.2 (Or.inl rfl)⟩
  | @cons u a v h w =>
    cases w with
    | nil => exact ⟨_, _, mem_closedOne.2 (Or.inr h), mem_closedOne.2 (Or.inl rfl),
        mem_closedOne.2 (Or.inl rfl)⟩
    | @cons _ b _ ha w =>
      cases w with
      | nil => exact ⟨_, _, mem_closedOne.2 (Or.inr h), mem_closedOne.2 (Or.inr ha),
          mem_closedOne.2 (Or.inl rfl)⟩
      | @cons _ c _ hb w =>
        cases w with
        | nil => exact ⟨_, _, mem_closedOne.2 (Or.inr h), mem_closedOne.2 (Or.inr ha),
            mem_closedOne.2 (Or.inr hb)⟩
        | cons hc w =>
          simp only [SimpleGraph.Walk.length_cons] at hw
          omega

private noncomputable def rootNeighborhood [DecidableEq V] (H : SimpleGraph V) (T : Finset V) :
    Finset V :=
  T.biUnion (closedOne H)

private lemma mem_rootNeighborhood [DecidableEq V] {H : SimpleGraph V} {T : Finset V} {x : V} :
    x ∈ rootNeighborhood H T ↔ ∃ u ∈ T, x ∈ closedOne H u :=
  Finset.mem_biUnion

private lemma rootNeighborhood_card {n : ℕ} {H R : SimpleGraph (Fin n)}
    (hs : ∀ ⦃x y⦄, H.Adj x y → (pathGraph n).Adj x y ∨ R.Adj x y)
    {T : Finset (Fin n)} (hT : ∀ x ∈ T, ∀ a b, R.Adj x a → R.Adj x b → a = b) :
    (rootNeighborhood H T).card ≤ T.card * 4 := by
  classical
  exact Finset.card_biUnion_le_card_mul _ _ _ fun x hx => closedOne_card_at_root hs (hT x hx)

/-- Count ordered root pairs by the middle step of a walk of length at most three. -/
private lemma pair_count {n : ℕ} (H R : SimpleGraph (Fin n))
    (hs : ∀ ⦃x y⦄, H.Adj x y → (pathGraph n).Adj x y ∨ R.Adj x y)
    (hd : H.ediam ≤ 3) (T : Finset (Fin n))
    (hT : ∀ x ∈ T, ∀ a b, R.Adj x a → R.Adj x b → a = b)
    (hI : Set.InjOn R.connectedComponentMk (T : Set (Fin n))) :
    T.card * T.card ≤ 48 * T.card + 32 * (inside R (rootNeighborhood H T)).edgeSet.ncard := by
  classical
  let X := rootNeighborhood H T
  let easyFrom (u : Fin n) :=
    (closedOne H u).biUnion fun a => (pathOne a).biUnion fun b => rootsNear H T b
  let easy := T.biUnion fun u => ({u} : Finset (Fin n)) ×ˢ easyFrom u
  let A : Finset (Fin n × Fin n) := univ.filter fun ab => (inside R X).Adj ab.1 ab.2
  let hard := A.biUnion fun ab => rootsNear H T ab.1 ×ˢ rootsNear H T ab.2
  have heasy : easy.card ≤ T.card * 48 := by
    apply Finset.card_biUnion_le_card_mul
    intro u hu
    simp only [Finset.card_product, Finset.card_singleton, one_mul]
    have h : (easyFrom u).card ≤ (closedOne H u).card * 12 := by
      apply Finset.card_biUnion_le_card_mul
      intro a _
      have h : ((pathOne a).biUnion fun b => rootsNear H T b).card ≤ (pathOne a).card * 4 :=
        Finset.card_biUnion_le_card_mul (pathOne a) (fun b => rootsNear H T b) 4
          (fun b _ => rootsNear_card hs hI b)
      have hp := pathOne_card a
      omega
    have hp := closedOne_card_at_root hs (hT u hu)
    omega
  have hA : A.card = 2 * (inside R X).edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    exact (inside R X).two_mul_card_edgeFinset.symm
  have hhard : hard.card ≤ A.card * 16 := by
    apply Finset.card_biUnion_le_card_mul
    intro ab _
    rw [Finset.card_product]
    exact Nat.mul_le_mul (rootsNear_card hs hI ab.1) (rootsNear_card hs hI ab.2)
  have hcover : T ×ˢ T ⊆ easy ∪ hard := by
    rintro ⟨u, v⟩ huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.1 huv
    have hvd := (SimpleGraph.ediam_le_iff.1 hd) u v
    have hnTop : H.edist u v ≠ ⊤ := fun he => by simp [he] at hvd
    obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top hnTop
    have hw3 : w.length ≤ 3 := by
      rw [← hw] at hvd
      exact_mod_cast hvd
    obtain ⟨a, b, ha, hab, hb⟩ := padded_walk w hw3
    have HEasy (hab' : b ∈ pathOne a) : (u, v) ∈ easy :=
      Finset.mem_biUnion.2 ⟨u, hu, Finset.mem_product.2 ⟨Finset.mem_singleton_self _,
        Finset.mem_biUnion.2 ⟨a, ha, Finset.mem_biUnion.2 ⟨b, hab', mem_rootsNear.2 ⟨hv, hb⟩⟩⟩⟩⟩
    rcases mem_closedOne.1 hab with he | h
    · exact Finset.mem_union_left _ (HEasy (mem_pathOne (Or.inl he)))
    rcases hs h with hg | hr
    · exact Finset.mem_union_left _ (HEasy (mem_pathOne (Or.inr hg)))
    · have hAX : a ∈ X := mem_rootNeighborhood.2 ⟨u, hu, ha⟩
      have hBX : b ∈ X := mem_rootNeighborhood.2 ⟨v, hv, closedOne_symm hb⟩
      have hAB : (a, b) ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, hr, hAX, hBX⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(a, b), hAB,
        Finset.mem_product.2 ⟨mem_rootsNear.2 ⟨hu, closedOne_symm ha⟩, mem_rootsNear.2 ⟨hv, hb⟩⟩⟩)
  have h := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  rw [Finset.card_product] at h
  change T.card * T.card ≤ 48 * T.card + 32 * (inside R X).edgeSet.ncard
  omega


private lemma extension_edges {n : ℕ} (H : SimpleGraph (Fin n)) (hd : H.ediam ≤ 3) :
    n ≤ (H \ pathGraph n).edgeSet.ncard + 704 := by
  let R := H \ pathGraph n
  have hs ⦃x y : Fin n⦄ (hxy : H.Adj x y) : (pathGraph n).Adj x y ∨ R.Adj x y := by
    classical
    by_cases hb : (pathGraph n).Adj x y
    · exact Or.inl hb
    · exact Or.inr ⟨hxy, hb⟩
  obtain ⟨T, hroots, hleaf, hinj⟩ := roots_exist R
  let X := rootNeighborhood H T
  have hX (C : R.ConnectedComponent) (hc : C.toSimpleGraph.IsTree) : ∃ x ∈ X, x ∈ C := by
    obtain ⟨x, hxT, hxC⟩ := hroots C hc
    exact ⟨x, mem_rootNeighborhood.2 ⟨x, hxT, mem_closedOne.2 (Or.inl rfl)⟩, hxC⟩
  have hcount := edges_with_tree_roots (outside R X) X (outside_tree_roots R X hX)
  rw [Fintype.card_fin] at hcount
  have hXcard : X.card ≤ T.card * 4 := rootNeighborhood_card hs hleaf
  have hpair : T.card * T.card ≤ 48 * T.card + 32 * (inside R X).edgeSet.ncard :=
    pair_count H R hs hd T hleaf hinj
  have hsplit := edge_split R X
  change n ≤ R.edgeSet.ncard + 704
  by_cases hT : T.card ≤ 176
  · omega
  · have hdense : T.card * 176 ≤ T.card * T.card :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_comm T.card 176] at hdense
    omega

private def parityGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x.val % 2 ≠ y.val % 2
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

private lemma path_le_parity (n : ℕ) : pathGraph n ≤ parityGraph n := by
  intro x y h
  change x.val % 2 ≠ y.val % 2
  rcases pathGraph_adj.1 h with h | h <;> omega

private lemma parity_triangle_free (n : ℕ) : (parityGraph n).CliqueFree 3 := by
  intro T hT
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := SimpleGraph.is3Clique_iff.1 hT
  change x.val % 2 ≠ y.val % 2 at hxy
  change x.val % 2 ≠ z.val % 2 at hxz
  change y.val % 2 ≠ z.val % 2 at hyz
  omega

private lemma parity_diameter (n : ℕ) (hn : 2 ≤ n) : (parityGraph n).ediam ≤ 3 := by
  apply SimpleGraph.ediam_le_of_edist_le
  intro x y
  by_cases hxy : x.val % 2 = y.val % 2
  · have hz : ∃ z : Fin n, x.val % 2 ≠ z.val % 2 := by
      by_cases hx : x.val % 2 = 0
      · exact ⟨⟨1, by omega⟩, by change x.val % 2 ≠ 1; omega⟩
      · exact ⟨⟨0, by omega⟩, hx⟩
    obtain ⟨z, hxz⟩ := hz
    have hzy : z.val % 2 ≠ y.val % 2 := fun he => hxz (hxy.trans he.symm)
    have hxz' : (parityGraph n).edist x z = 1 :=
      SimpleGraph.edist_eq_one_iff_adj.2 hxz
    have hzy' : (parityGraph n).edist z y = 1 :=
      SimpleGraph.edist_eq_one_iff_adj.2 hzy
    calc
      (parityGraph n).edist x y ≤ (parityGraph n).edist x z + (parityGraph n).edist z y :=
        SimpleGraph.edist_triangle
      _ ≤ 3 := by rw [hxz', hzy']; decide
  · have h : (parityGraph n).edist x y = 1 := SimpleGraph.edist_eq_one_iff_adj.2 hxy
    rw [h]
    decide

end DiameterThreeLower

open DiameterThreeLower in
theorem OMA.solution : type_of% @Erdos619.erdos_619.variants.h_three_lower := by
  refine ⟨704, by norm_num, fun n hn => ?_⟩
  have hconn : (pathGraph n).Connected := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact pathGraph_connected k
  have htri := (parity_triangle_free n).anti (path_le_parity n)
  refine ⟨Fin n, inferInstance, pathGraph n, Fintype.card_fin n, hconn, htri, ?_⟩
  by_cases hsmall : n ≤ 704
  · have hR : (n : ℝ) ≤ 704 := by exact_mod_cast hsmall
    have h0 : (0 : ℝ) ≤ Erdos619.minNewEdges 3 (pathGraph n) := Nat.cast_nonneg _
    linarith
  · have hnonempty : {k : ℕ | ∃ H : SimpleGraph (Fin n),
        pathGraph n ≤ H ∧ H.CliqueFree 3 ∧ H.ediam ≤ 3 ∧
        (H \ pathGraph n).edgeSet.ncard = k}.Nonempty :=
      ⟨_, parityGraph n, path_le_parity n, parity_triangle_free n, parity_diameter n (by omega), rfl⟩
    obtain ⟨H, _, _, hd, hEq⟩ := Nat.sInf_mem hnonempty
    change (H \ pathGraph n).edgeSet.ncard = Erdos619.minNewEdges 3 (pathGraph n) at hEq
    have h := extension_edges H hd
    rw [hEq] at h
    have hR : (n : ℝ) ≤ (Erdos619.minNewEdges 3 (pathGraph n) : ℝ) + 704 := by
      exact_mod_cast h
    linarith