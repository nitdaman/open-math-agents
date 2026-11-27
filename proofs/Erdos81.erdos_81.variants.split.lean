import FormalConjectures.ErdosProblems.«81»
import Mathlib.Algebra.Group.Fin.Basic

/-! Chen, Erdős and Ordman, Clique partitions of split graphs (1994).
https://ordman.net/MathResearch/CEOClique_Parts.pdf
We combine their matching assignments into a single completion and counting argument. -/

open Finset SimpleGraph
open scoped Classical

namespace SplitCliques

variable {V : Type} [Fintype V]

private noncomputable def graphEdges (G : SimpleGraph V) : Finset (Finset V) :=
  (Finset.univ.powersetCard 2).filter fun e => G.IsClique (e : Set V)

omit [Fintype V] in
private noncomputable def covered (P : Finset (Finset V)) : Finset (Finset V) :=
  P.biUnion fun s => s.powersetCard 2

private lemma mem_graphEdges {G : SimpleGraph V} {e : Finset V} :
    e ∈ graphEdges G ↔ e.card = 2 ∧ G.IsClique (e : Set V) := by
  simp [graphEdges, Finset.mem_powersetCard]

omit [Fintype V] in
private lemma mem_covered {P : Finset (Finset V)} {e : Finset V} :
    e ∈ covered P ↔ ∃ s ∈ P, e ⊆ s ∧ e.card = 2 := by
  simp [covered, Finset.mem_biUnion, Finset.mem_powersetCard]

omit [Fintype V] in
private lemma pair_subset {x y : V} {S : Finset V} :
    ({x, y} : Finset V) ⊆ S ↔ x ∈ S ∧ y ∈ S := by
  rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]

private lemma covered_subset {G : SimpleGraph V} {P : Finset (Finset V)}
    (h : ∀ s ∈ P, G.IsClique (s : Set V)) : covered P ⊆ graphEdges G := by
  intro e he
  obtain ⟨s, hs, hsub, hcard⟩ := mem_covered.mp he
  exact mem_graphEdges.mpr ⟨hcard, SimpleGraph.IsClique.subset (Finset.coe_subset.mpr hsub) (h s hs)⟩

-- Any uncovered edge can finish the partition as a two-vertex clique.
private lemma complete_partition (G : SimpleGraph V) (Q : Finset (Finset V))
    (hQ : ∀ s ∈ Q, 2 ≤ s.card ∧ G.IsClique (s : Set V))
    (huniq : (Q : Set (Finset V)).PairwiseDisjoint fun s => s.powersetCard 2) :
    ∃ P : Finset (Finset V), G.IsCliqueEdgePartition P ∧
      P.card + (covered Q).card ≤ Q.card + (graphEdges G).card := by
  let E := graphEdges G
  let R := E \ covered Q
  let P := Q ∪ R
  have hr : R.card + (covered Q).card = E.card :=
    Finset.card_sdiff_add_card_eq_card (covered_subset fun s hs => (hQ s hs).2)
  refine ⟨P, ⟨?_, ?_⟩, ?_⟩
  · intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact hQ s hs
    · obtain ⟨hcard, hclique⟩ := mem_graphEdges.mp (Finset.mem_sdiff.mp hs).1
      exact ⟨hcard.ge, hclique⟩
  · intro x y hxy
    let e : Finset V := {x, y}
    have he : e.card = 2 := Finset.card_pair hxy.ne
    have hx : x ∈ e := by simp [e]
    have hy : y ∈ e := by simp [e]
    have hE : e ∈ E := by
      apply mem_graphEdges.mpr
      refine ⟨he, ?_⟩
      simp only [e, Finset.coe_pair, SimpleGraph.isClique_pair]
      exact fun _ => hxy
    have unique_in_Q {s t : Finset V} (hs : s ∈ Q) (ht : t ∈ Q)
        (hse : e ⊆ s) (hte : e ⊆ t) : s = t := by
      by_contra hne
      exact Finset.disjoint_left.mp (huniq hs ht hne)
        (Finset.mem_powersetCard.mpr ⟨hse, he⟩) (Finset.mem_powersetCard.mpr ⟨hte, he⟩)
    have singleton_edge {s : Finset V} (hs : s ∈ R) (hs' : e ⊆ s) : s = e := by
      have hc := (mem_graphEdges.mp (Finset.mem_sdiff.mp hs).1).1
      exact (Finset.eq_of_subset_of_card_le hs' (by rw [he, hc])).symm
    by_cases hu : e ∈ covered Q
    · obtain ⟨s, hs, hse, _⟩ := mem_covered.mp hu
      refine ⟨s, ⟨Finset.mem_union_left _ hs, hse hx, hse hy⟩, ?_⟩
      rintro t ⟨ht, htx, hty⟩
      have hte : e ⊆ t := pair_subset.mpr ⟨htx, hty⟩
      rcases Finset.mem_union.mp ht with ht | ht
      · exact unique_in_Q ht hs hte hse
      · have hte' := singleton_edge ht hte
        exact ((Finset.mem_sdiff.mp ht).2 (hte' ▸ hu)).elim
    · have heR : e ∈ R := Finset.mem_sdiff.mpr ⟨hE, hu⟩
      refine ⟨e, ⟨Finset.mem_union_right _ heR, hx, hy⟩, ?_⟩
      rintro t ⟨ht, htx, hty⟩
      have hte : e ⊆ t := pair_subset.mpr ⟨htx, hty⟩
      rcases Finset.mem_union.mp ht with ht | ht
      · exact (hu (mem_covered.mpr ⟨t, ht, hte, he⟩)).elim
      · exact singleton_edge ht hte
  · have hp : P.card ≤ Q.card + R.card := Finset.card_union_le _ _
    change P.card + (covered Q).card ≤ Q.card + E.card
    omega

omit [Fintype V] in
-- Picking the q smallest values bounds the total cost of the selected vertices.
private lemma select_small_average (I : Finset V) (f : V → ℕ) {q : ℕ} (hq : q ≤ I.card) :
    ∃ Q ⊆ I, Q.card = q ∧ I.card * (∑ x ∈ Q, f x) ≤ q * ∑ x ∈ I, f x := by
  have hn : (I.powersetCard q).Nonempty := Finset.powersetCard_nonempty.mpr hq
  obtain ⟨Q, hQ, hmin⟩ := Finset.exists_min_image (I.powersetCard q) (fun s => ∑ x ∈ s, f x) hn
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hQ
  let R := I \ Q
  have hpair (x) (hx : x ∈ Q) (y) (hy : y ∈ R) : f x ≤ f y := by
    have hy' := Finset.mem_sdiff.mp hy
    let Q' := insert y (Q.erase x)
    have hQ's : Q' ⊆ I :=
      Finset.insert_subset_iff.mpr ⟨hy'.1, (Finset.erase_subset _ _).trans hsub⟩
    have hn' : y ∉ Q.erase x := fun h => hy'.2 (Finset.mem_of_mem_erase h)
    have hQ'c : Q'.card = q := by
      rw [Finset.card_insert_of_notMem hn', Finset.card_erase_of_mem hx]
      have hp := Finset.card_pos.mpr ⟨x, hx⟩
      omega
    have h := hmin Q' (Finset.mem_powersetCard.mpr ⟨hQ's, hQ'c⟩)
    change (∑ x ∈ Q, f x) ≤ ∑ x ∈ insert y (Q.erase x), f x at h
    rw [Finset.sum_insert hn'] at h
    have hh := Finset.sum_erase_add _ f hx
    omega
  have hprod : R.card * (∑ x ∈ Q, f x) ≤ Q.card * (∑ y ∈ R, f y) := by
    calc
      _ = ∑ x ∈ Q, ∑ y ∈ R, f x := by
        simp only [Finset.sum_const, Nat.nsmul_eq_mul, Finset.mul_sum]
      _ ≤ ∑ x ∈ Q, ∑ y ∈ R, f y :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpair x hx y hy
      _ = _ := by simp only [Finset.sum_const, Nat.nsmul_eq_mul]
  have hd : R.card + Q.card = I.card := Finset.card_sdiff_add_card_eq_card hsub
  have hs : (∑ x ∈ R, f x) + ∑ x ∈ Q, f x = ∑ x ∈ I, f x :=
    Finset.sum_sdiff hsub
  refine ⟨Q, hsub, hcard, ?_⟩
  rw [← hcard, ← hd, ← hs]
  rw [add_mul, mul_add]
  exact Nat.add_le_add_right hprod _

omit [Fintype V] in
private noncomputable def missingDegree (G : SimpleGraph V) (A : Finset V) (u : V) : ℕ :=
  (A.filter fun v => ¬ G.Adj u v).card

omit [Fintype V] in
private noncomputable def missing (G : SimpleGraph V) (I A : Finset V) : ℕ :=
  ∑ u ∈ I, missingDegree G A u

omit [Fintype V] in
private lemma card_missing (G : SimpleGraph V) (I A : Finset V) :
    (((I ×ˢ A).filter fun p => ¬ G.Adj p.1 p.2)).card = missing G I A := by
  rw [Finset.card_filter, Finset.sum_product]
  simp only [missing, missingDegree, Finset.card_filter]

private lemma remaining_edges (G : SimpleGraph V) (A I : Finset V)
    (hCover : ∀ x, x ∈ A ∨ x ∈ I) (hI : G.IsIndepSet (I : Set V))
    (K F : Finset (Finset V))
    (hInternal : ∀ e ⊆ A, e.card = 2 → e ∈ covered K ∨ e ∈ F) :
    (graphEdges G \ covered K).card + missing G I A ≤ I.card * A.card + F.card := by
  let X := ((I ×ˢ A).filter fun p => G.Adj p.1 p.2).image
    (fun p : V × V => ({p.1, p.2} : Finset V))
  have hx : X.card + missing G I A ≤ I.card * A.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := I ×ˢ A) (p := fun p => G.Adj p.1 p.2)
    rw [Finset.card_product, card_missing] at h
    exact (Nat.add_le_add_right Finset.card_image_le _).trans h.le
  have hsub : graphEdges G \ covered K ⊆ X ∪ F := by
    intro e he
    obtain ⟨hE, hK⟩ := Finset.mem_sdiff.mp he
    obtain ⟨hc, hclique⟩ := mem_graphEdges.mp hE
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hc
    have hadj := hclique (by simp : u ∈ (({u, v} : Finset V) : Set V))
      (by simp : v ∈ (({u, v} : Finset V) : Set V)) huv
    rcases hCover u with hu | hu <;> rcases hCover v with hv | hv
    · exact Finset.mem_union_right _ ((hInternal _ (pair_subset.mpr ⟨hu, hv⟩) hc).resolve_left hK)
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(v, u),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv, hu⟩, hadj.symm⟩, Finset.pair_comm _ _⟩)
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(u, v),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hadj⟩, rfl⟩)
    · exact (hI hu hv huv hadj).elim
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

-- Give one matching to each selected vertex. A missing leg invalidates at most one of its triangles.
private lemma triangles_from_matchings (G : SimpleGraph V) (A Q : Finset V) {q : ℕ}
    (hA : G.IsClique (A : Set V)) (hAQ : Disjoint A Q) (hQ : Q.card = q)
    {J : Type} [Fintype J] (base : J → Finset V) (color : J → Fin q)
    (hbase : ∀ j, (base j).card = 2 ∧ base j ⊆ A) (hinj : Function.Injective base)
    (hmatch : ∀ j k, color j = color k → ∀ x ∈ base j, x ∈ base k → j = k)
    (K : Finset (Finset V)) (hK : ∀ s ∈ K, 2 ≤ s.card ∧ s ⊆ A)
    (hKdis : (K : Set (Finset V)).PairwiseDisjoint fun s => s.powersetCard 2)
    (hbaseK : ∀ j, base j ∉ covered K) :
    ∃ P : Finset (Finset V), G.IsCliqueEdgePartition P ∧
      P.card + 2 * Fintype.card J ≤ K.card + (graphEdges G \ covered K).card + 2 * missing G Q A := by
  let e : ↥Q ≃ Fin q := Q.equivFin.trans (finCongr hQ)
  let assign (c : Fin q) : V := (e.symm c).val
  have haQ (c : Fin q) : assign c ∈ Q := (e.symm c).property
  have haNot (c : Fin q) : assign c ∉ A :=
    fun h => Finset.disjoint_left.mp hAQ h (haQ c)
  have haInj : Function.Injective assign := fun _ _ h => e.symm.injective (Subtype.ext h)
  let tri (j : J) : Finset V := insert (assign (color j)) (base j)
  have htriA (j : J) {x : V} (hx : x ∈ A) : x ∈ tri j ↔ x ∈ base j := by
    rw [Finset.mem_insert]
    exact or_iff_right fun h => haNot (color j) (h ▸ hx)
  have htriI (j : J) {x : V} (hx : x ∉ A) : x ∈ tri j ↔ x = assign (color j) := by
    rw [Finset.mem_insert]
    exact or_iff_left fun h => hx ((hbase j).2 h)
  have htriCard (j : J) : (tri j).card = 3 := by
    rw [Finset.card_insert_of_notMem (fun h => haNot (color j) ((hbase j).2 h)), (hbase j).1]
  have htriInj : Function.Injective tri := by
    intro j k h
    apply hinj
    ext x
    by_cases hx : x ∈ A
    · rw [← htriA j hx, h, htriA k hx]
    · exact iff_of_false (fun h => hx ((hbase j).2 h)) (fun h => hx ((hbase k).2 h))
  let valid (j : J) : Prop := ∀ x ∈ base j, G.Adj (assign (color j)) x
  let good := Finset.univ.filter valid
  let bad := Finset.univ.filter fun j => ¬ valid j
  let T := good.image tri
  have hTcard : T.card = good.card := Finset.card_image_of_injective _ htriInj
  have hJcard : good.card + bad.card = Fintype.card J := by
    simpa only [Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset J)) (p := valid))
  have hbad : bad.card ≤ missing G Q A := by
    have hex (j : ↥bad) : ∃ x ∈ base j.val, ¬ G.Adj (assign (color j.val)) x := by
      have hh : ¬ valid j.val := (Finset.mem_filter.mp j.property).2
      simpa [valid] using hh
    choose miss hmiss hnoAdj using hex
    let W := (Q ×ˢ A).filter fun p => ¬ G.Adj p.1 p.2
    let f : ↥bad ↪ ↥W :=
      ⟨fun j => ⟨(assign (color j.val), miss j), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨haQ _, (hbase j.val).2 (hmiss j)⟩, hnoAdj j⟩⟩, by
        intro j k h
        have hpair := congrArg Subtype.val h
        have hc := haInj (congrArg Prod.fst hpair)
        have hx : miss j = miss k := congrArg Prod.snd hpair
        exact Subtype.ext (hmatch j.val k.val hc (miss j) (hmiss j) (hx.symm ▸ hmiss k))⟩
    have hh := Fintype.card_le_of_embedding f
    simpa only [Fintype.card_coe, W, card_missing] using hh
  have hTclique (s : Finset V) (hs : s ∈ T) : 2 ≤ s.card ∧ G.IsClique (s : Set V) := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    refine ⟨by rw [htriCard]; decide, ?_⟩
    have hv := (Finset.mem_filter.mp hj).2
    intro x hx y hy hne
    change x ∈ tri j at hx
    change y ∈ tri j at hy
    rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
    · exact (hne rfl).elim
    · exact hv y hy
    · exact (hv x hx).symm
    · exact hA ((hbase j).2 hx) ((hbase j).2 hy) hne
  have hTdis : (T : Set (Finset V)).PairwiseDisjoint fun s => s.powersetCard 2 := by
    intro s hs t ht hne
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    obtain ⟨h₁, hc⟩ := Finset.mem_powersetCard.mp h₁
    obtain ⟨h₂, _⟩ := Finset.mem_powersetCard.mp h₂
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
    obtain ⟨hxj, hyj⟩ := pair_subset.mp h₁
    obtain ⟨hxk, hyk⟩ := pair_subset.mp h₂
    apply hne
    congr 1
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · apply hinj
      have hsubj := pair_subset.mpr ⟨(htriA j hx).mp hxj, (htriA j hy).mp hyj⟩
      have hsubk := pair_subset.mpr ⟨(htriA k hx).mp hxk, (htriA k hy).mp hyk⟩
      have he₁ : ({x, y} : Finset V) = base j :=
        Finset.eq_of_subset_of_card_le hsubj (by rw [(hbase j).1, Finset.card_pair hxy])
      have he₂ : ({x, y} : Finset V) = base k :=
        Finset.eq_of_subset_of_card_le hsubk (by rw [(hbase k).1, Finset.card_pair hxy])
      exact he₁.symm.trans he₂
    · have hc := haInj (((htriI j hy).mp hyj).symm.trans ((htriI k hy).mp hyk))
      exact hmatch j k hc x ((htriA j hx).mp hxj) ((htriA k hx).mp hxk)
    · have hc := haInj (((htriI j hx).mp hxj).symm.trans ((htriI k hx).mp hxk))
      exact hmatch j k hc y ((htriA j hy).mp hyj) ((htriA k hy).mp hyk)
    · exact (hxy (((htriI j hx).mp hxj).trans ((htriI j hy).mp hyj).symm)).elim
  have hKT (s : Finset V) (hs : s ∈ K) (t : Finset V) (ht : t ∈ T) :
      Disjoint (s.powersetCard 2) (t.powersetCard 2) := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hws, hwc⟩ := Finset.mem_powersetCard.mp h₁
    have hwt := (Finset.mem_powersetCard.mp h₂).1
    have hwb : w ⊆ base j := fun x hx => (htriA j ((hK s hs).2 (hws hx))).mp (hwt hx)
    have he : w = base j := Finset.eq_of_subset_of_card_le hwb (by rw [hwc, (hbase j).1])
    exact hbaseK j (mem_covered.mpr ⟨s, hs, he ▸ hws, (hbase j).1⟩)
  have hUnion : ((K ∪ T : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint
      fun s => s.powersetCard 2 := by
    intro s hs t ht hne
    rcases Finset.mem_union.mp hs with hs | hs <;> rcases Finset.mem_union.mp ht with ht | ht
    · exact hKdis hs ht hne
    · exact hKT _ hs _ ht
    · exact (hKT _ ht _ hs).symm
    · exact hTdis hs ht hne
  have hclique : ∀ s ∈ K ∪ T, 2 ≤ s.card ∧ G.IsClique (s : Set V) := by
    intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact ⟨(hK s hs).1, SimpleGraph.IsClique.subset (Finset.coe_subset.mpr (hK s hs).2) hA⟩
    · exact hTclique s hs
  obtain ⟨P, hP, hcount⟩ := complete_partition G (K ∪ T) hclique hUnion
  have hcovUnion : covered (K ∪ T) = covered K ∪ covered T := by
    unfold covered
    rw [Finset.union_biUnion]
  have hcovDis : Disjoint (covered K) (covered T) := by
    refine Finset.disjoint_left.mpr fun w h₁ h₂ => ?_
    obtain ⟨s, hs, hws, hc⟩ := mem_covered.mp h₁
    obtain ⟨t, ht, hwt, _⟩ := mem_covered.mp h₂
    exact Finset.disjoint_left.mp (hKT s hs t ht)
      (Finset.mem_powersetCard.mpr ⟨hws, hc⟩) (Finset.mem_powersetCard.mpr ⟨hwt, hc⟩)
  have hcovT : (covered T).card = T.card * 3 := by
    rw [covered, Finset.card_biUnion hTdis]
    rw [← Finset.sum_const_nat]
    intro s hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    rw [Finset.card_powersetCard, htriCard]
    decide
  rw [hcovUnion, Finset.card_union_of_disjoint hcovDis, hcovT] at hcount
  have hkCut : (graphEdges G \ covered K).card + (covered K).card = (graphEdges G).card :=
    Finset.card_sdiff_add_card_eq_card (covered_subset fun s hs => (hclique s (Finset.mem_union_left _ hs)).2)
  have hU := Finset.card_union_le K T
  exact ⟨P, hP, by omega⟩

private lemma baseline (G : SimpleGraph V) (A I : Finset V) (hA : G.IsClique (A : Set V))
    (hI : G.IsIndepSet (I : Set V)) (hCover : ∀ x, x ∈ A ∨ x ∈ I) :
    ∃ P : Finset (Finset V), G.IsCliqueEdgePartition P ∧
      P.card + missing G I A ≤ I.card * A.card + 1 := by
  let K : Finset (Finset V) := ({A} : Finset (Finset V)).filter fun s => 2 ≤ s.card
  have hK (s : Finset V) (hs : s ∈ K) : 2 ≤ s.card ∧ G.IsClique (s : Set V) := by
    obtain ⟨hs', hc⟩ := Finset.mem_filter.mp hs
    rw [Finset.mem_singleton.mp hs'] at hc ⊢
    exact ⟨hc, hA⟩
  have hdisj : (K : Set (Finset V)).PairwiseDisjoint fun s => s.powersetCard 2 := by
    intro s hs t ht hne
    exact (hne ((Finset.mem_singleton.mp (Finset.mem_filter.mp hs).1).trans
      (Finset.mem_singleton.mp (Finset.mem_filter.mp ht).1).symm)).elim
  have hk : K.card ≤ 1 :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_singleton _)
  have hr := remaining_edges G A I hCover hI K ∅ (by
    intro e he hc
    left
    exact mem_covered.mpr ⟨A, Finset.mem_filter.mpr ⟨by simp, hc ▸ Finset.card_le_card he⟩, he, hc⟩)
  obtain ⟨P, hP, hp⟩ := complete_partition G K hK hdisj
  have hcard := Finset.card_sdiff_add_card_eq_card
    (covered_subset (G := G) fun s hs => (hK s hs).2)
  exact ⟨P, hP, by simp only [Finset.card_empty, Nat.add_zero] at hr; omega⟩

omit [Fintype V] in
private lemma pair_through {s : Finset V} {x : V} (hs : s.card = 2) (hx : x ∈ s) :
    ∃ y, x ≠ y ∧ s = {x, y} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b, hab, rfl⟩
  · exact ⟨a, hab.symm, Finset.pair_comm _ _⟩

-- The modular sum of the endpoints colors the edges of the clique into matchings.
private lemma full_clique_matches (G : SimpleGraph V) (A I : Finset V)
    (hA : G.IsClique (A : Set V)) (hI : G.IsIndepSet (I : Set V))
    (hCover : ∀ x, x ∈ A ∨ x ∈ I) (hAI : Disjoint A I)
    (ha : 0 < A.card) (hab : A.card ≤ I.card) :
    ∃ (P : Finset (Finset V)) (z : ℕ), G.IsCliqueEdgePartition P ∧
      I.card * z ≤ A.card * missing G I A ∧
      P.card + missing G I A + A.card.choose 2 ≤ I.card * A.card + 2 * z := by
  obtain ⟨Q, hQI, hQ, hm⟩ := select_small_average I (missingDegree G A) hab
  let J : Type := ↥(A.powersetCard 2)
  let _ : NeZero A.card := ⟨ha.ne'⟩
  let label (x : V) : Fin A.card := if h : x ∈ A then A.equivFin ⟨x, h⟩ else 0
  have hLabel {x y : V} (hx : x ∈ A) (hy : y ∈ A) (h : label x = label y) : x = y := by
    have hh : A.equivFin ⟨x, hx⟩ = A.equivFin ⟨y, hy⟩ := by
      simpa only [label, dif_pos hx, dif_pos hy] using h
    exact congrArg Subtype.val (A.equivFin.injective hh)
  let color (j : J) := ∑ x ∈ j.val, label x
  have hbase (j : J) : j.val.card = 2 ∧ j.val ⊆ A := by
    have hh := Finset.mem_powersetCard.mp j.property
    exact ⟨hh.2, hh.1⟩
  have hmatch (j k : J) (hc : color j = color k) (x : V)
      (hj : x ∈ j.val) (hk : x ∈ k.val) : j = k := by
    obtain ⟨y, hxy, hj'⟩ := pair_through (hbase j).1 hj
    obtain ⟨z, hxz, hk'⟩ := pair_through (hbase k).1 hk
    have hyA : y ∈ A := (hbase j).2 (hj'.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    have hzA : z ∈ A := (hbase k).2 (hk'.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
    change (∑ u ∈ j.val, label u) = ∑ u ∈ k.val, label u at hc
    have hy : x ∉ ({y} : Finset V) := by simpa only [Finset.mem_singleton] using hxy
    have hz : x ∉ ({z} : Finset V) := by simpa only [Finset.mem_singleton] using hxz
    rw [hj', hk', Finset.sum_insert hy, Finset.sum_insert hz, Finset.sum_singleton,
      Finset.sum_singleton] at hc
    have he : y = z := hLabel hyA hzA (add_left_cancel hc)
    exact Subtype.ext (hj'.trans (he ▸ hk'.symm))
  have hDis : Disjoint A Q := Finset.disjoint_left.mpr fun _ hx hy =>
    Finset.disjoint_left.mp hAI hx (hQI hy)
  obtain ⟨P, hP, hp⟩ := triangles_from_matchings G A Q hA hDis hQ
    (fun j : J => j.val) color hbase Subtype.val_injective hmatch ∅ (by simp)
    (by simp [Set.PairwiseDisjoint, Set.Pairwise]) (by simp [covered])
  have hr := remaining_edges G A I hCover hI ∅ (A.powersetCard 2)
    (fun e he hc => Or.inr (Finset.mem_powersetCard.mpr ⟨he, hc⟩))
  simp only [covered, Finset.biUnion_empty, Finset.sdiff_empty, Finset.card_empty, Nat.zero_add,
    J, Fintype.card_coe, Finset.card_powersetCard] at hp hr
  exact ⟨P, missing G Q A, hP, hm, by omega⟩

-- Keep two clique blocks and partition the edges between them into cyclic matchings.
private lemma half_clique_matches (G : SimpleGraph V) (A I : Finset V)
    (hA : G.IsClique (A : Set V)) (hI : G.IsIndepSet (I : Set V))
    (hCover : ∀ x, x ∈ A ∨ x ∈ I) (hAI : Disjoint A I)
    {p : ℕ} (hp : 0 < p) (ha : A.card = p + p) :
    ∃ (P : Finset (Finset V)) (z : ℕ), G.IsCliqueEdgePartition P ∧
      I.card * z ≤ min p I.card * missing G I A ∧
      P.card + missing G I A + 2 * (p * min p I.card) ≤
        2 + I.card * A.card + p ^ 2 + 2 * z := by
  let q := min p I.card
  obtain ⟨Q, hQI, hQ, hz⟩ := select_small_average I (missingDegree G A) (q := q) (min_le_right _ _)
  let _ : NeZero p := ⟨hp.ne'⟩
  let e : (Fin p ⊕ Fin p) ≃ ↥A :=
    (finSumFinEquiv.trans (finCongr ha.symm)).trans A.equivFin.symm
  let left (i : Fin p) := (e (Sum.inl i)).val
  let right (i : Fin p) := (e (Sum.inr i)).val
  have hleft (i : Fin p) : left i ∈ A := (e (Sum.inl i)).property
  have hright (i : Fin p) : right i ∈ A := (e (Sum.inr i)).property
  have leftInj : Function.Injective left :=
    fun _ _ h => Sum.inl.inj (e.injective (Subtype.ext h))
  have rightInj : Function.Injective right :=
    fun _ _ h => Sum.inr.inj (e.injective (Subtype.ext h))
  have different (i j : Fin p) : left i ≠ right j :=
    fun h => by
      have he : (Sum.inl i : Fin p ⊕ Fin p) = Sum.inr j := e.injective (Subtype.ext h)
      cases he
  let L := Finset.univ.image left
  let R := Finset.univ.image right
  have hLR : Disjoint L R := by
    refine Finset.disjoint_left.mpr fun x hL hR => ?_
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp hR
    exact different i j he.symm
  have hL : L ⊆ A := fun x hx => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hleft i
  have hR : R ⊆ A := fun x hx => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hright i
  have hBoth (x : V) (hx : x ∈ A) : x ∈ L ∨ x ∈ R := by
    obtain ⟨s, hs⟩ := e.surjective ⟨x, hx⟩
    cases s with
    | inl i => exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, congrArg Subtype.val hs⟩)
    | inr i => exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, congrArg Subtype.val hs⟩)
  let K := ({L, R} : Finset (Finset V)).filter fun S => 2 ≤ S.card
  have hK (s : Finset V) (hs : s ∈ K) : 2 ≤ s.card ∧ s ⊆ A := by
    obtain ⟨hs, hc⟩ := Finset.mem_filter.mp hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact ⟨hc, hL⟩
    · exact ⟨hc, hR⟩
  have hKdis : (K : Set (Finset V)).PairwiseDisjoint fun S => S.powersetCard 2 := by
    intro s hs t ht hne
    have hs' := (Finset.mem_filter.mp hs).1
    have ht' := (Finset.mem_filter.mp ht).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs' ht'
    have hsimp : Disjoint (L.powersetCard 2) (R.powersetCard 2) := by
      refine Finset.disjoint_left.mpr fun S hSL hSR => ?_
      obtain ⟨hSL, hSc⟩ := Finset.mem_powersetCard.mp hSL
      have hSR := (Finset.mem_powersetCard.mp hSR).1
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      exact Finset.disjoint_left.mp hLR (hSL hx) (hSR hx)
    rcases hs' with rfl | rfl <;> rcases ht' with rfl | rfl
    · exact (hne rfl).elim
    · exact hsimp
    · exact hsimp.symm
    · exact (hne rfl).elim
  let F := (Finset.univ : Finset (Fin p × Fin p)).image fun x => ({left x.1, right x.2} : Finset V)
  have hF : F.card ≤ p ^ 2 := by
    exact Finset.card_image_le.trans_eq (by simp [Fintype.card_prod, pow_two])
  have hInternal (S : Finset V) (hS : S ⊆ A) (hcard : S.card = 2) :
      S ∈ covered K ∨ S ∈ F := by
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hxA : x ∈ A := hS (by simp)
    have hyA : y ∈ A := hS (by simp)
    rcases hBoth x hxA with hx | hx <;> rcases hBoth y hyA with hy | hy
    · left
      have hs := pair_subset.mpr ⟨hx, hy⟩
      exact mem_covered.mpr ⟨L, Finset.mem_filter.mpr ⟨by simp, hcard ▸ Finset.card_le_card hs⟩,
        hs, hcard⟩
    · right
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
    · right
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, Finset.pair_comm _ _⟩
    · left
      have hs := pair_subset.mpr ⟨hx, hy⟩
      exact mem_covered.mpr ⟨R, Finset.mem_filter.mpr ⟨by simp, hcard ▸ Finset.card_le_card hs⟩,
        hs, hcard⟩
  let col : Fin q ↪ Fin p := Fin.castLEEmb (min_le_left _ _)
  let pr (j : Fin p × Fin q) : Fin p := col j.2 - j.1
  let base (j : Fin p × Fin q) : Finset V := {left j.1, right (pr j)}
  have hbase (j : Fin p × Fin q) : (base j).card = 2 ∧ base j ⊆ A :=
    ⟨Finset.card_pair (different _ _), pair_subset.mpr ⟨hleft _, hright _⟩⟩
  have hbaseK (j : Fin p × Fin q) : base j ∉ covered K := by
    intro h
    obtain ⟨S, hS, hsub, _⟩ := mem_covered.mp h
    obtain ⟨hl, hr⟩ := pair_subset.mp hsub
    have hs := (Finset.mem_filter.mp hS).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact Finset.disjoint_left.mp hLR hr (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)
    · exact Finset.disjoint_left.mp hLR (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩) hl
  have hbinj : Function.Injective base := by
    intro j k h
    have hl : left j.1 ∈ base k := h ▸ (by simp [base] : left j.1 ∈ base j)
    have hr : right (pr j) ∈ base k := h ▸ (by simp [base] : right (pr j) ∈ base j)
    simp only [base, Finset.mem_insert, Finset.mem_singleton] at hl hr
    have hi : j.1 = k.1 := leftInj (hl.resolve_right (different _ _))
    have hp' : pr j = pr k := rightInj (hr.resolve_left (different _ _).symm)
    have hc : j.2 = k.2 := by
      change col j.2 - j.1 = col k.2 - k.1 at hp'
      rw [hi] at hp'
      exact col.injective (sub_left_injective hp')
    exact Prod.ext hi hc
  have hmatch (j k : Fin p × Fin q) (hc : j.2 = k.2) (x : V)
      (hJ : x ∈ base j) (hK : x ∈ base k) : j = k := by
    simp only [base, Finset.mem_insert, Finset.mem_singleton] at hJ hK
    apply Prod.ext _ hc
    rcases hJ with hj | hj <;> rcases hK with hk | hk
    · exact leftInj (hj.symm.trans hk)
    · exact (different _ _ (hj.symm.trans hk)).elim
    · exact (different _ _ (hk.symm.trans hj)).elim
    · have hp' := rightInj (hj.symm.trans hk)
      change col j.2 - j.1 = col k.2 - k.1 at hp'
      rw [hc] at hp'
      exact sub_right_injective hp'
  have hDis : Disjoint A Q := Finset.disjoint_left.mpr fun _ hx hy =>
    Finset.disjoint_left.mp hAI hx (hQI hy)
  obtain ⟨P, hP, hcount⟩ :=
    triangles_from_matchings G A Q hA hDis hQ base Prod.snd hbase hbinj hmatch K hK hKdis hbaseK
  have hrest := remaining_edges G A I hCover hI K F hInternal
  have hKbound : K.card ≤ 2 := (Finset.card_filter_le _ _).trans Finset.card_le_two
  simp only [Fintype.card_prod, Fintype.card_fin] at hcount
  change P.card + 2 * (p * min p I.card) ≤ _ at hcount
  exact ⟨P, missing G Q A, hP, hz, by omega⟩


private lemma weighted_cost {a b q miss selected result keep bases slots : ℝ}
    (hb : 0 < b) (hSlope : b ≤ 2 * q) (hm : miss ≤ a * b / 4)
    (hsel : b * selected ≤ q * miss)
    (hresult : result + miss + 2 * slots ≤ keep + b * a + bases + 2 * selected) :
    result ≤ keep + 3 * a * b / 4 + bases - 2 * slots + a * q / 2 := by
  by_contra hn
  have h₁ := mul_le_mul_of_nonneg_left hresult hb.le
  have h₂ := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hSlope)
  have h₃ := mul_lt_mul_of_pos_left (lt_of_not_ge hn) hb
  nlinarith only [h₁, h₂, h₃, hsel]

private lemma choose_two_real {k : ℕ} (hk : 0 < k) :
    (k.choose 2 : ℝ) = ((k : ℝ) ^ 2 - k) / 2 := by
  have hh : k.choose 2 * 2 = k * (k - 1) := by
    rw [Nat.choose_two_right, Nat.div_mul_cancel (Nat.even_mul_pred_self k).two_dvd]
  have hR : (k.choose 2 : ℝ) * 2 = (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hh
  rw [Nat.cast_sub (Nat.succ_le_of_lt hk), Nat.cast_one] at hR
  nlinarith only [hR]

private lemma even_split_bound (G : SimpleGraph V) (A I : Finset V)
    (hA : G.IsClique (A : Set V)) (hI : G.IsIndepSet (I : Set V))
    (hCover : ∀ x, x ∈ A ∨ x ∈ I) (hAI : Disjoint A I) (he : Even A.card) :
    ∃ P : Finset (Finset V), G.IsCliqueEdgePartition P ∧
      (P.card : ℝ) ≤ 3 * ((A.card : ℝ) + I.card) ^ 2 / 16 + ((A.card : ℝ) + I.card) / 2 + 2 := by
  let a : ℝ := A.card
  let b : ℝ := I.card
  let M : ℝ := missing G I A
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hprod : 3 * a * b / 4 ≤ 3 * (a + b) ^ 2 / 16 := by nlinarith [sq_nonneg (a - b)]
  obtain ⟨P₀, hP₀, hc₀⟩ := baseline G A I hA hI hCover
  have h₀ : (P₀.card : ℝ) + M ≤ b * a + 1 := by
    dsimp [a, b, M]
    exact_mod_cast hc₀
  by_cases hbig : a * b / 4 ≤ M
  · exact ⟨P₀, hP₀, by change _ ≤ 3 * (a + b) ^ 2 / 16 + (a + b) / 2 + 2; nlinarith only [h₀, hbig, hprod, ha, hb]⟩
  have hquarter : M ≤ a * b / 4 := (lt_of_not_ge hbig).le
  have ha' : 0 < a := by by_contra! hh; have hz : a = 0 := le_antisymm hh ha; simp only [hz, zero_mul, zero_div] at hbig; exact hbig hM
  have hb' : 0 < b := by by_contra! hh; have hz : b = 0 := le_antisymm hh hb; simp only [hz, mul_zero, zero_div] at hbig; exact hbig hM
  have hAn : 0 < A.card := by dsimp [a] at ha'; exact_mod_cast ha'
  by_cases hab : A.card ≤ I.card
  · obtain ⟨P, z, hP, hsel, hcount⟩ := full_clique_matches G A I hA hI hCover hAI hAn hab
    have hselR : b * (z : ℝ) ≤ a * M := by dsimp [a, b, M]; exact_mod_cast hsel
    have hcountR : (P.card : ℝ) + M + (A.card.choose 2 : ℝ) ≤ b * a + 2 * (z : ℝ) := by
      dsimp [a, b, M]
      exact_mod_cast hcount
    have hchoose : (A.card.choose 2 : ℝ) = (a ^ 2 - a) / 2 := choose_two_real hAn
    by_cases hsmall : 2 * a ≤ b
    · have hz : 2 * (z : ℝ) ≤ M := by
        by_contra hn
        have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hn) hb'
        have hh' := mul_nonneg hM (sub_nonneg.mpr hsmall)
        nlinarith only [hselR, hh, hh']
      have htarget : a * b - a ^ 2 / 2 ≤ (a + b) ^ 2 / 6 := by
        nlinarith [sq_nonneg (b - 2 * a)]
      exact ⟨P, hP, by change _ ≤ 3 * (a + b) ^ 2 / 16 + (a + b) / 2 + 2; nlinarith only
        [hchoose, hcountR, hz, htarget, sq_nonneg (a + b), hb]⟩
    · have hc : (P.card : ℝ) + M + 2 * (A.card.choose 2 : ℝ) ≤
          0 + b * a + (A.card.choose 2 : ℝ) + 2 * (z : ℝ) := by linarith only [hcountR]
      have hcost := weighted_cost hb' (le_of_not_ge hsmall) hquarter hselR hc
      exact ⟨P, hP, by change _ ≤ 3 * (a + b) ^ 2 / 16 + (a + b) / 2 + 2; nlinarith only [hcost, hchoose, hprod, hb]⟩
  obtain ⟨p, hp⟩ := he
  have hp' : 0 < p := by omega
  have hap : a = (p : ℝ) + p := by dsimp [a]; exact_mod_cast hp
  obtain ⟨P, z, hP, hsel, hcount⟩ := half_clique_matches G A I hA hI hCover hAI hp' hp
  by_cases hpb : p ≤ I.card
  · rw [min_eq_left hpb] at hsel hcount
    have hselR : b * (z : ℝ) ≤ (p : ℝ) * M := by dsimp [b, M]; exact_mod_cast hsel
    have hcountR : (P.card : ℝ) + M + 2 * ((p : ℝ) ^ 2) ≤
        2 + b * a + (p : ℝ) ^ 2 + 2 * (z : ℝ) := by
      dsimp [a, b, M]
      simp only [pow_two] at hcount ⊢
      exact_mod_cast hcount
    have hsl : b ≤ 2 * (p : ℝ) := by
      have hh : I.card ≤ 2 * p := by omega
      dsimp [b]
      exact_mod_cast hh
    have hcost := weighted_cost hb' hsl hquarter hselR hcountR
    have heq : a * (p : ℝ) / 2 = (p : ℝ) ^ 2 := by rw [hap]; ring
    exact ⟨P, hP, by change _ ≤ 3 * (a + b) ^ 2 / 16 + (a + b) / 2 + 2; nlinarith only [hcost, heq, hprod, ha, hb]⟩
  · rw [min_eq_right (by omega : I.card ≤ p)] at hsel hcount
    have hselR : b * (z : ℝ) ≤ b * M := by dsimp [b, M]; exact_mod_cast hsel
    have hz : (z : ℝ) ≤ M := by
      by_contra hn
      exact (mul_lt_mul_of_pos_left (lt_of_not_ge hn) hb').not_ge hselR
    have hcountR : (P.card : ℝ) + M + 2 * ((p : ℝ) * b) ≤
        2 + b * a + (p : ℝ) ^ 2 + 2 * (z : ℝ) := by
      dsimp [a, b, M]
      exact_mod_cast hcount
    have hc : (P.card : ℝ) ≤ (p : ℝ) ^ 2 + M + 2 := by
      rw [hap] at hcountR
      nlinarith only [hcountR, hz]
    have havg : (a * b + (p : ℝ) ^ 2) / 2 ≤ (a + b) ^ 2 / 6 := by
      rw [hap]
      nlinarith [sq_nonneg ((p : ℝ) - b)]
    by_cases hle : (P.card : ℝ) ≤ P₀.card
    · exact ⟨P, hP, by change _ ≤ 3 * (a + b) ^ 2 / 16 + (a + b) / 2 + 2; nlinarith only
        [hc, h₀, havg, hle, sq_nonneg (a + b), ha, hb]⟩
    · exact ⟨P₀, hP₀, by change _ ≤ 3 * (a + b) ^ 2 / 16 + (a + b) / 2 + 2; nlinarith only
        [hc, h₀, havg, le_of_not_ge hle, sq_nonneg (a + b), ha, hb]⟩


-- Add one vertex to the clique when its size is odd, then restrict the partition.
private def paddedGraph (G : SimpleGraph V) (A : Finset V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some x, some y => G.Adj x y
    | none, some y => y ∈ A
    | some x, none => x ∈ A
    | none, none => False
  symm := ⟨by
    intro x y
    cases x <;> cases y
    · exact id
    · exact id
    · exact id
    · exact fun h => h.symm⟩
  loopless := ⟨by
    intro x
    cases x with
    | none => exact id
    | some x => exact G.irrefl⟩

private lemma restrict_partition (G : SimpleGraph V) (A : Finset V)
    (P : Finset (Finset (Option V))) (hP : (paddedGraph G A).IsCliqueEdgePartition P) :
    ∃ P' : Finset (Finset V), G.IsCliqueEdgePartition P' ∧ P'.card ≤ P.card := by
  let proj (s : Finset (Option V)) : Finset V := Finset.univ.filter fun x => some x ∈ s
  let P' := (P.image proj).filter fun s => 2 ≤ s.card
  have hmem {s : Finset (Option V)} {x : V} : x ∈ proj s ↔ some x ∈ s := by simp [proj]
  refine ⟨P', ⟨?_, ?_⟩, (Finset.card_filter_le _ _).trans Finset.card_image_le⟩
  · intro t ht
    obtain ⟨hs, hcard⟩ := Finset.mem_filter.mp ht
    obtain ⟨s, hsP, rfl⟩ := Finset.mem_image.mp hs
    refine ⟨hcard, ?_⟩
    intro u hu v hv hne
    exact (hP.1 s hsP).2 (hmem.mp hu) (hmem.mp hv) (fun he => hne (Option.some.inj he))
  · intro u v huv
    have huv' : (paddedGraph G A).Adj (some u) (some v) := huv
    obtain ⟨s, ⟨hs, hu, hv⟩, huniq⟩ := hP.2 (some u) (some v) huv'
    have hcard : 2 ≤ (proj s).card := by
      have hh := Finset.card_le_card (Finset.insert_subset (hmem.mpr hu) (Finset.singleton_subset_iff.mpr (hmem.mpr hv)))
      simpa only [Finset.card_pair huv.ne] using hh
    have ht : proj s ∈ P' := Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem proj hs, hcard⟩
    refine ⟨proj s, ⟨ht, hmem.mpr hu, hmem.mpr hv⟩, ?_⟩
    rintro t ⟨ht, htu, htv⟩
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht).1
    exact congrArg proj (huniq s' ⟨hs', hmem.mp htu, hmem.mp htv⟩)

private lemma split_bound (G : SimpleGraph V) (hG : G.IsSplitGraph) (hn : 0 < Fintype.card V) :
    ∃ P : Finset (Finset V), G.IsCliqueEdgePartition P ∧
      (P.card : ℝ) ≤ 3 * (Fintype.card V : ℝ) ^ 2 / 16 + 4 * (Fintype.card V : ℝ) := by
  obtain ⟨S, hS, hSc⟩ := hG
  let A := S.toFinset
  let I := Sᶜ.toFinset
  have hA : G.IsClique (A : Set V) := by simpa [A] using hS
  have hI : G.IsIndepSet (I : Set V) := by simpa [I] using hSc
  have hCover (x : V) : x ∈ A ∨ x ∈ I := by simpa only [A, I, Set.mem_toFinset, Set.mem_compl_iff] using em (x ∈ S)
  have hAI : Disjoint A I := by simp [A, I, Finset.disjoint_left]
  have hsum : A.card + I.card = Fintype.card V := by
    have hu : A ∪ I = Finset.univ := by
      ext x
      simp [hCover x]
    rw [← Finset.card_union_of_disjoint hAI, hu, Finset.card_univ]
  have hsumR : (A.card : ℝ) + I.card = Fintype.card V := by exact_mod_cast hsum
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Nat.succ_le_of_lt hn
  by_cases he : Even A.card
  · obtain ⟨P, hP, hbound⟩ := even_split_bound G A I hA hI hCover hAI he
    rw [hsumR] at hbound
    exact ⟨P, hP, by linarith only [hbound, hnR]⟩
  let i : V ↪ Option V := ⟨Option.some, fun _ _ hh => Option.some.inj hh⟩
  let A' : Finset (Option V) := insert none (A.map i)
  let I' : Finset (Option V) := I.map i
  have hmap (T : Finset V) (x : V) : some x ∈ T.map i ↔ x ∈ T := by
    change i x ∈ T.map i ↔ x ∈ T
    exact Finset.mem_map' i
  have hAsome {x : V} : some x ∈ A' ↔ x ∈ A := by
    simp only [A', Finset.mem_insert, Option.some_ne_none, false_or, hmap]
  have hIsome {x : V} : some x ∈ I' ↔ x ∈ I := hmap I x
  have hAnone : (none : Option V) ∈ A' := by simp [A']
  have hInone : (none : Option V) ∉ I' := by simp [I', i]
  have hA' : (paddedGraph G A).IsClique (A' : Set (Option V)) := by
    intro x hx y hy hxy
    cases x with
    | none =>
      cases y with
      | none => exact (hxy rfl).elim
      | some y => exact hAsome.mp hy
    | some x =>
      cases y with
      | none => exact hAsome.mp hx
      | some y => exact hA (hAsome.mp hx) (hAsome.mp hy) (fun he => hxy (congrArg some he))
  have hI' : (paddedGraph G A).IsIndepSet (I' : Set (Option V)) := by
    intro x hx y hy hxy
    cases x with
    | none => exact (hInone hx).elim
    | some x =>
      cases y with
      | none => exact (hInone hy).elim
      | some y => exact hI (hIsome.mp hx) (hIsome.mp hy) (fun he => hxy (congrArg some he))
  have hCover' (x : Option V) : x ∈ A' ∨ x ∈ I' := by
    cases x with
    | none => exact Or.inl hAnone
    | some x => simpa only [hAsome, hIsome] using hCover x
  have hAI' : Disjoint A' I' := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    cases x with
    | none => exact hInone hy
    | some x => exact Finset.disjoint_left.mp hAI (hAsome.mp hx) (hIsome.mp hy)
  have hAcard : A'.card = A.card + 1 := by
    simp [A', i, Finset.card_insert_of_notMem]
  have hIcard : I'.card = I.card := Finset.card_map i
  have he' : Even A'.card := by
    rw [hAcard, Nat.even_iff]
    rw [Nat.even_iff] at he
    omega
  obtain ⟨P', hP', hbound⟩ := even_split_bound (paddedGraph G A) A' I' hA' hI' hCover' hAI' he'
  obtain ⟨P, hP, hcard⟩ := restrict_partition G A P' hP'
  have hcardR : (P.card : ℝ) ≤ P'.card := by exact_mod_cast hcard
  have hsum' : (A'.card : ℝ) + I'.card = (Fintype.card V : ℝ) + 1 := by
    rw [hAcard, hIcard, Nat.cast_add, Nat.cast_one]
    linarith only [hsumR]
  rw [hsum'] at hbound
  exact ⟨P, hP, by nlinarith only [hbound, hcardR, hnR]⟩

end SplitCliques

theorem OMA.solution : type_of% @Erdos81.erdos_81.variants.split := by
  classical
  refine ⟨4, ?_⟩
  intro n G hG
  cases n with
  | zero =>
    refine ⟨∅, ⟨by simp, ?_⟩, by simp⟩
    intro u
    exact Fin.elim0 u
  | succ n =>
    simpa only [Fintype.card_fin] using SplitCliques.split_bound G hG (by simp)