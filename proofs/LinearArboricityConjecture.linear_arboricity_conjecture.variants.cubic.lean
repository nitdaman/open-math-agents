import FormalConjectures.Wikipedia.LinearArboricityConjecture
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Operations

/-! Akiyama, Exoo and Harary, Covering and packing in graphs IV.
https://doi.org/10.1002/net.3230110108
A maximal matching and Hall's theorem give an initial two-coloring.
We move edges between the colors until both classes are forests. -/

open Finset SimpleGraph LinearArboricityConjecture
open scoped Classical

namespace CubicArboricity

variable {V : Type} [Fintype V]

private noncomputable def degreeN (G : SimpleGraph V) (v : V) : ℕ :=
  (G.neighborSet v).ncard

omit [Fintype V] in
private lemma card_neighbors (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    (G.neighborFinset v).card = degreeN G v := by
  calc
    _ = ((G.neighborFinset v : Finset V) : Set V).ncard := by rw [Set.ncard_coe_finset]
    _ = _ := congrArg Set.ncard (G.coe_neighborFinset v)

omit [Fintype V] in
private lemma degreeN_eq_degree (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    degreeN G v = G.degree v := (card_neighbors G v).symm

private lemma degreeN_pos_of_adj (G : SimpleGraph V) {v w : V} (h : G.Adj v w) :
    0 < degreeN G v := by
  rw [← card_neighbors G v]
  exact Finset.card_pos.mpr ⟨w, (G.mem_neighborFinset v w).mpr h⟩

private lemma neighbor_subset {G H : SimpleGraph V} (h : G ≤ H) (v : V) :
    G.neighborFinset v ⊆ H.neighborFinset v := by
  intro w hw
  exact (H.mem_neighborFinset v w).mpr (h ((G.mem_neighborFinset v w).mp hw))

private lemma degree_le_of_le {G H : SimpleGraph V} (h : G ≤ H) (v : V) :
    degreeN G v ≤ degreeN H v := by
  simpa only [card_neighbors] using Finset.card_le_card (neighbor_subset h v)

private lemma degree_sup_le (G H : SimpleGraph V) (v : V) :
    degreeN (G ⊔ H) v ≤ degreeN G v + degreeN H v := by
  rw [← card_neighbors, neighborFinset_sup]
  simpa only [card_neighbors] using
    Finset.card_union_le (G.neighborFinset v) (H.neighborFinset v)

private lemma degree_sdiff (G H : SimpleGraph V) (h : H ≤ G) (v : V) :
    degreeN (G \ H) v = degreeN G v - degreeN H v := by
  rw [← card_neighbors, neighborFinset_sdiff, Finset.card_sdiff_of_subset (neighbor_subset h v)]
  simp only [card_neighbors]

private lemma add_edge_degree_le (G : SimpleGraph V) (a b v : V) :
    degreeN (G ⊔ SimpleGraph.edge a b) v ≤ degreeN G v + 1 := by
  apply (degree_sup_le G (SimpleGraph.edge a b) v).trans
  apply Nat.add_le_add_left
  rw [← card_neighbors (SimpleGraph.edge a b) v, Finset.card_le_one]
  intro x hx y hy
  have hx' := (mem_neighborFinset _ v x).mp hx
  have hy' := (mem_neighborFinset _ v y).mp hy
  rw [SimpleGraph.edge_adj] at hx' hy'
  rcases hx'.1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases hy'.1 with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;> grind

private lemma add_edge_degree_unchanged (G : SimpleGraph V) (a b v : V)
    (ha : v ≠ a) (hb : v ≠ b) :
    degreeN (G ⊔ SimpleGraph.edge a b) v = degreeN G v := by
  have he : (SimpleGraph.edge a b).neighborFinset v = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := (mem_neighborFinset _ v x).mp hx
    rw [SimpleGraph.edge_adj] at h
    rcases h.1 with ⟨h, _⟩ | ⟨h, _⟩
    · exact ha h
    · exact hb h
  rw [← card_neighbors, neighborFinset_sup, he, Finset.union_empty,
    card_neighbors]

private lemma degree_two_of_neighbors (G : SimpleGraph V) {v x y : V}
    (hx : G.Adj v x) (hy : G.Adj v y) (hne : x ≠ y) :
    2 ≤ degreeN G v := by
  rw [← card_neighbors]
  have h : ({x, y} : Finset V) ⊆ G.neighborFinset v := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, mem_neighborFinset, hx, hy,
      and_self]
  have hc := Finset.card_le_card h
  have hne' : x ∉ ({y} : Finset V) := by simpa only [Finset.mem_singleton] using hne
  rw [Finset.card_insert_of_notMem hne', Finset.card_singleton] at hc
  exact hc

private lemma neighbors_eq (G : SimpleGraph V) {v x y : V}
    (h : degreeN G v ≤ 1) (hx : G.Adj v x) (hy : G.Adj v y) : x = y := by
  by_contra hne
  have := degree_two_of_neighbors G hx hy hne
  omega

private lemma neighbor_eq_of_degree_two (G : SimpleGraph V) {v a b c : V}
    (h : degreeN G v ≤ 2) (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) : c = a ∨ c = b := by
  by_contra! hne
  have hs : ({c, a, b} : Finset V) ⊆ G.neighborFinset v := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, mem_neighborFinset, ha, hb, hc,
      and_self]
  have hc' := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem (by simp [hne.1, hne.2]),
    Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hab),
    Finset.card_singleton, card_neighbors] at hc'
  omega

private lemma cycle_degree (G : SimpleGraph V) {v : V}
    {p : G.Walk v v} (hc : p.IsCycle) : 2 ≤ degreeN G v :=
  degree_two_of_neighbors G (p.adj_snd hc.not_nil) (p.adj_penultimate hc.not_nil).symm
    hc.snd_ne_penultimate

private lemma path_component_closed (G : SimpleGraph V) (hmax : ∀ v, degreeN G v ≤ 2)
    {a b : V} (hab : a ≠ b) (ha : degreeN G a ≤ 1) (hb : degreeN G b ≤ 1)
    {p : G.Walk a b} (hp : p.IsPath)
    {x y : V} (hx : x ∈ p.support) (hxy : G.Adj x y) : y ∈ p.support := by
  obtain ⟨i, rfl, hi⟩ := (Walk.mem_support_iff_exists_getVert.mp hx)
  have hpn : ¬ p.Nil := Walk.not_nil_of_ne hab
  have hpl : 0 < p.length := Walk.not_nil_iff_lt_length.mp hpn
  rcases i with _ | i
  · simp only [Walk.getVert_zero] at hxy
    have he := neighbors_eq G ha hxy (p.adj_snd hpn)
    rw [he]
    exact p.getVert_mem_support 1
  by_cases hend : i + 1 = p.length
  · have hxe : p.getVert (i + 1) = b := by rw [hend, Walk.getVert_length]
    rw [hxe] at hxy
    have he := neighbors_eq G hb hxy (p.adj_penultimate hpn).symm
    rw [he]
    exact p.getVert_mem_support (p.length - 1)
  have hi₁ : i < p.length := by omega
  have hi₂ : i + 1 < p.length := by omega
  have hprev := (p.adj_getVert_succ hi₁).symm
  have hnext := p.adj_getVert_succ hi₂
  have hne : p.getVert i ≠ p.getVert (i + 1 + 1) := by
    intro he
    have hh := hp.getVert_injOn (show i ∈ {j | j ≤ p.length} from hi₁.le)
      (show i + 1 + 1 ∈ {j | j ≤ p.length} from by exact Nat.succ_le_of_lt hi₂) he
    omega
  rcases neighbor_eq_of_degree_two G (hmax _) hprev hnext hxy hne with he | he
  · rw [he]; exact p.getVert_mem_support i
  · rw [he]; exact p.getVert_mem_support (i + 1 + 1)

private lemma reachable_low_degree_unique (G : SimpleGraph V) (hmax : ∀ v, degreeN G v ≤ 2)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (ha : degreeN G a ≤ 1)
    (hb : degreeN G b ≤ 1) (hc : degreeN G c ≤ 1)
    (habR : G.Reachable a b) (hacR : G.Reachable a c) : b = c := by
  obtain ⟨p, hp⟩ := habR.exists_isPath
  have hclosed {x y : V} (hx : x ∈ p.support) (hxy : G.Adj x y) : y ∈ p.support :=
    path_component_closed G hmax hab ha hb hp hx hxy
  obtain ⟨q⟩ := hacR
  have hmem {x y : V} (q : G.Walk x y) (hx : x ∈ p.support) : y ∈ p.support := by
    induction q with
    | nil => exact hx
    | cons hadj q ih => exact ih (hclosed hx hadj)
  obtain ⟨i, hci, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hmem q p.start_mem_support)
  by_cases hi0 : i = 0
  · exact (hac ((by simpa only [hi0, Walk.getVert_zero] using hci : a = c))).elim
  by_cases hie : i = p.length
  · simpa only [hie, Walk.getVert_length] using hci
  have hi₁ : i - 1 < p.length := by omega
  have hi₂ : i < p.length := lt_of_le_of_ne hi hie
  have hprev := (p.adj_getVert_succ hi₁).symm
  rw [show i - 1 + 1 = i by omega, hci] at hprev
  have hnext := p.adj_getVert_succ hi₂
  rw [hci] at hnext
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro he
    have hh := hp.getVert_injOn (show i - 1 ∈ {j | j ≤ p.length} from hi₁.le)
      (show i + 1 ∈ {j | j ≤ p.length} from Nat.succ_le_of_lt hi₂) he
    omega
  have hh := degree_two_of_neighbors G hprev hnext hne
  omega

private lemma maximum_subgraph (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : ∃ B ≤ G, P B) :
    ∃ B ≤ G, P B ∧ ∀ C ≤ G, P C → C.edgeSet.ncard ≤ B.edgeSet.ncard := by
  let S : Set ℕ := {m | ∃ B ≤ G, P B ∧ B.edgeSet.ncard = m}
  have hS : S.Nonempty := by
    obtain ⟨B, hB, hBP⟩ := hP
    exact ⟨B.edgeSet.ncard, B, hB, hBP, rfl⟩
  have hbound : BddAbove S := by
    refine ⟨G.edgeSet.ncard, ?_⟩
    rintro m ⟨B, hB, hBP, rfl⟩
    exact Set.ncard_le_ncard (edgeSet_mono hB)
  obtain ⟨B, hB, hBP, hBc⟩ := Nat.sSup_mem hS hbound
  refine ⟨B, hB, hBP, fun C hC hCP => ?_⟩
  rw [hBc]
  exact le_csSup hbound ⟨C, hC, hCP, rfl⟩

private lemma hall_neighbors (G : SimpleGraph V) (hreg : ∀ v, degreeN G v = 3)
    (U : Set V) :
    ∃ f : U → V, Function.Injective f ∧ ∀ u : U, G.Adj u.val (f u) := by
  let t (u : U) := G.neighborFinset (u : V)
  have hHall (S : Finset U) : S.card ≤ (S.biUnion t).card := by
    let W := S.biUnion t
    have hs (u : U) (hu : u ∈ S) : t u ⊆ W :=
      fun w hw => Finset.mem_biUnion.mpr ⟨u, hu, hw⟩
    have hs₃ (u : U) : (t u).card = 3 := by
      simp only [t, card_neighbors G, hreg]
    have hsum :
        (∑ u ∈ S, (t u).card) = ∑ w ∈ W, (S.filter (fun u => w ∈ t u)).card := by
      calc
        _ = ∑ u ∈ S, ∑ w ∈ W, if w ∈ t u then 1 else 0 := by
          refine Finset.sum_congr rfl fun u hu => ?_
          have he : W.filter (fun w => w ∈ t u) = t u := by
            ext w
            exact ⟨fun h => (Finset.mem_filter.mp h).2,
              fun h => Finset.mem_filter.mpr ⟨hs u hu h, h⟩⟩
          rw [← Finset.card_filter, he]
        _ = _ := by rw [Finset.sum_comm]; simp only [Finset.card_filter]
    have hdeg (w : V) : (S.filter (fun u => w ∈ t u)).card ≤ 3 := by
      let S' := S.filter (fun u => w ∈ t u)
      have himage : S'.image Subtype.val ⊆ G.neighborFinset w := by
        intro y hy
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
        exact (G.mem_neighborFinset w u.val).mpr
          ((G.mem_neighborFinset u.val w).mp (Finset.mem_filter.mp hu).2).symm
      have hh := Finset.card_le_card himage
      rw [Finset.card_image_of_injective _ Subtype.val_injective,
        card_neighbors G, hreg] at hh
      exact hh
    have hupper : (∑ w ∈ W, (S.filter (fun u => w ∈ t u)).card) ≤ W.card * 3 := by
      simpa only [Finset.sum_const, Nat.nsmul_eq_mul] using
        (Finset.sum_le_sum fun w (_ : w ∈ W) => hdeg w)
    simp only [hs₃, Finset.sum_const, Nat.nsmul_eq_mul] at hsum
    change S.card ≤ W.card
    omega
  obtain ⟨f, hf, htf⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
  exact ⟨f, hf, fun u => (G.mem_neighborFinset u.val (f u)).mp (htf u)⟩

private lemma initial_forest (G : SimpleGraph V) (hreg : ∀ v, degreeN G v = 3) :
    ∃ B ≤ G, B.IsAcyclic ∧ (∀ v, degreeN B v ≤ 2) ∧ (∀ v, degreeN (G \ B) v ≤ 2) := by
  obtain ⟨M, hMG, hM, hMmax⟩ := maximum_subgraph G (fun M => ∀ v, degreeN M v ≤ 1)
    ⟨⊥, bot_le, fun v => by simp [degreeN]⟩
  let U : Set V := {v | degreeN M v = 0}
  have independent {a b : V} (ha : a ∈ U) (hb : b ∈ U) : ¬ G.Adj a b := by
    intro hab
    let M' := M ⊔ SimpleGraph.edge a b
    have hM'le : M' ≤ G := sup_le hMG ((edge_le_iff (G := G)).mpr (Or.inr hab))
    have hdeg (v : V) : degreeN M' v ≤ 1 := by
      by_cases hva : v = a
      · subst v
        exact (add_edge_degree_le M a b a).trans (by change degreeN M a + 1 ≤ 1; rw [show degreeN M a = 0 from ha])
      by_cases hvb : v = b
      · subst v
        exact (add_edge_degree_le M a b b).trans (by change degreeN M b + 1 ≤ 1; rw [show degreeN M b = 0 from hb])
      exact (add_edge_degree_unchanged M a b v hva hvb).le.trans (hM v)
    have hnot : ¬ M.Adj a b := by
      intro h
      exact (degreeN_pos_of_adj M h).ne' ha
    have hincr := Set.ncard_lt_ncard (edgeSet_strict_mono (lt_sup_edge M (s := a) (t := b) hab.ne hnot))
    exact (hMmax M' hM'le hdeg).not_gt hincr
  obtain ⟨f, hf, hfa⟩ := hall_neighbors G hreg U
  have hout (u : U) : f u ∉ U := fun h => independent u.property h (hfa u)
  let Rel (x y : V) : Prop := ∃ hx : x ∈ U, f ⟨x, hx⟩ = y
  let F := SimpleGraph.fromRel Rel
  have hFG : F ≤ G := by
    intro x y hxy
    rw [SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with ⟨hx, he⟩ | ⟨hy, he⟩
    · exact he ▸ hfa ⟨x, hx⟩
    · exact (he ▸ hfa ⟨y, hy⟩).symm
  have hFD (x : V) : degreeN F x ≤ 1 := by
    rw [← card_neighbors, Finset.card_le_one]
    intro y hy z hz
    have hy' := (F.mem_neighborFinset x y).mp hy
    have hz' := (F.mem_neighborFinset x z).mp hz
    rw [SimpleGraph.fromRel_adj] at hy' hz'
    rcases hy'.2 with ⟨hx, hxy⟩ | ⟨hy, hyx⟩ <;>
      rcases hz'.2 with ⟨hx', hxz⟩ | ⟨hz, hzx⟩
    · exact hxy.symm.trans hxz
    · exact (hout ⟨z, hz⟩ (hzx.symm ▸ hx)).elim
    · exact (hout ⟨y, hy⟩ (hyx.symm ▸ hx')).elim
    · exact congrArg Subtype.val (hf (hyx.trans hzx.symm))
  let B := M ⊔ F
  have hBG : B ≤ G := sup_le hMG hFG
  have hB₂ (x : V) : degreeN B x ≤ 2 := by
    have hh := degree_sup_le M F x
    change degreeN B x ≤ degreeN M x + degreeN F x at hh
    have hm := hM x
    have hf := hFD x
    omega
  have hB₁ (x : V) : 1 ≤ degreeN B x := by
    by_cases hx : x ∈ U
    · have hadj : F.Adj x (f ⟨x, hx⟩) := by
        exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨(hfa ⟨x, hx⟩).ne, Or.inl ⟨hx, rfl⟩⟩
      have hpos : 0 < degreeN F x := degreeN_pos_of_adj F hadj
      exact hpos.trans_le (degree_le_of_le le_sup_right x)
    · have hpos : 0 < degreeN M x := Nat.pos_of_ne_zero hx
      exact hpos.trans_le (degree_le_of_le le_sup_left x)
  have hacyc : B.IsAcyclic := by
    intro v p hp
    have hu (x : V) (hx : x ∈ p.support) : x ∉ U := by
      intro hxu
      have hcyc : (p.rotate x hx).IsCycle := (Walk.isCycle_rotate hx).mpr hp
      have hx2 := cycle_degree B hcyc
      have hx0 : degreeN M x = 0 := hxu
      have hh := degree_sup_le M F x
      change degreeN B x ≤ degreeN M x + degreeN F x at hh
      have hF := hFD x
      omega
    have hM_adj {a b : V} (ha : a ∉ U) (hb : b ∉ U) (hab : B.Adj a b) : M.Adj a b := by
      rcases hab with hM | hF
      · exact hM
      · rw [SimpleGraph.fromRel_adj] at hF
        rcases hF.2 with ⟨ha', _⟩ | ⟨hb', _⟩
        · exact (ha ha').elim
        · exact (hb hb').elim
    have hv := hu v p.start_mem_support
    have hsnd := hu p.snd (p.getVert_mem_support 1)
    have hpen := hu p.penultimate (p.getVert_mem_support (p.length - 1))
    have he := neighbors_eq M (hM v)
      (hM_adj hv hsnd (p.adj_snd hp.not_nil))
      (hM_adj hv hpen (p.adj_penultimate hp.not_nil).symm)
    exact hp.snd_ne_penultimate he
  refine ⟨B, hBG, hacyc, hB₂, fun x => ?_⟩
  rw [degree_sdiff G B hBG, hreg]
  have := hB₁ x
  omega

private lemma two_forests (G : SimpleGraph V) (hreg : ∀ v, degreeN G v = 3) :
    ∃ B ≤ G, IsLinearForest B ∧ IsLinearForest (G \ B) := by
  obtain ⟨B, hBG, ⟨hBacyc, hB₂, hR₂⟩, hmax⟩ := maximum_subgraph G
    (fun H => H.IsAcyclic ∧ (∀ v, degreeN H v ≤ 2) ∧ ∀ v, degreeN (G \ H) v ≤ 2)
    (initial_forest G hreg)
  refine ⟨B, hBG, ⟨hBacyc, hB₂⟩, ?_, hR₂⟩
  let R := G \ B
  by_contra hn
  have hcycles : ∃ (u : V) (p : R.Walk u u), p.IsCycle := by
    simpa only [SimpleGraph.IsAcyclic, not_forall, not_not] using hn
  obtain ⟨u, p, hp⟩ := hcycles
  have cycle_vertex (x : V) (hx : x ∈ p.support) : degreeN B x ≤ 1 := by
    have hi : (p.rotate x hx).IsCycle := (Walk.isCycle_rotate hx).mpr hp
    have hde := cycle_degree R hi
    change 2 ≤ degreeN (G \ B) x at hde
    rw [degree_sdiff G B hBG, hreg] at hde
    omega
  have hu := cycle_vertex u p.start_mem_support
  have hv := cycle_vertex p.snd (p.getVert_mem_support 1)
  have hw := cycle_vertex p.penultimate (p.getVert_mem_support (p.length - 1))
  have huv : R.Adj u p.snd := p.adj_snd hp.not_nil
  have huw : R.Adj u p.penultimate := (p.adj_penultimate hp.not_nil).symm
  have hedge : ∃ v, R.Adj u v ∧ degreeN B v ≤ 1 ∧ ¬ B.Reachable u v := by
    by_cases hr : B.Reachable u p.snd
    · refine ⟨p.penultimate, huw, hw, ?_⟩
      intro hr'
      exact hp.snd_ne_penultimate
        (reachable_low_degree_unique B hB₂ huv.ne huw.ne hu hv hw hr hr')
    · exact ⟨p.snd, huv, hv, hr⟩
  obtain ⟨v, huv, hv, hr⟩ := hedge
  have hab : G.Adj u v ∧ ¬ B.Adj u v := huv
  let B' := B ⊔ SimpleGraph.edge u v
  have hB'G : B' ≤ G := sup_le hBG ((edge_le_iff (G := G)).mpr (Or.inr hab.1))
  have hB'acyc : B'.IsAcyclic := hBacyc.sup_edge_of_not_reachable hr
  have hB'₂ (x : V) : degreeN B' x ≤ 2 := by
    by_cases hx : x = u
    · subst x
      exact (add_edge_degree_le B u v u).trans (by omega)
    by_cases hx' : x = v
    · subst x
      exact (add_edge_degree_le B u v v).trans (by omega)
    exact (add_edge_degree_unchanged B u v x hx hx').le.trans (hB₂ x)
  have hR'₂ (x : V) : degreeN (G \ B') x ≤ 2 := by
    have hle : G \ B' ≤ G \ B := fun _ _ e => ⟨e.1, fun hb => e.2 (Or.inl hb)⟩
    exact (degree_le_of_le hle x).trans (hR₂ x)
  have hincr := Set.ncard_lt_ncard (edgeSet_strict_mono (lt_sup_edge B (s := u) (t := v) hab.1.ne hab.2))
  exact (hmax B' hB'G ⟨hB'acyc, hB'₂, hR'₂⟩).not_gt hincr

private lemma two_decomposition (G : SimpleGraph V) (hreg : ∀ v, degreeN G v = 3) :
    HasLinearForestDecomposition G 2 := by
  obtain ⟨B, hBG, hB, hR⟩ := two_forests G hreg
  let D (i : Fin 2) : SimpleGraph V := if i = 0 then B else G \ B
  have hsub (i : Fin 2) : D i ≤ G := by
    unfold D
    split_ifs
    · exact hBG
    · exact fun _ _ e => e.1
  refine ⟨D, fun i => ⟨?_, hsub i⟩, ?_⟩
  · unfold D
    split_ifs
    · exact hB
    · exact hR
  intro u v
  constructor
  · intro hu
    by_cases h : B.Adj u v
    · refine ⟨0, by simpa only [D, if_pos rfl] using h, ?_⟩
      intro j hj
      by_contra hn
      have hr : (G \ B).Adj u v := by simpa only [D, if_neg hn] using hj
      exact hr.2 h
    · have hRuv : (G \ B).Adj u v := ⟨hu, h⟩
      refine ⟨1, by simpa only [D, if_neg (by decide : (1 : Fin 2) ≠ 0)] using hRuv, ?_⟩
      intro j hj
      have hj01 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
      rcases hj01 j with rfl | hj'
      · exact (h (by simpa only [D, if_pos rfl] using hj)).elim
      · exact hj'
  · rintro ⟨i, hi, _⟩
    exact hsub i hi

private lemma neither_zero_nor_one [Nonempty V] (G : SimpleGraph V)
    (hreg : ∀ v, degreeN G v = 3) {k : ℕ} (hk : HasLinearForestDecomposition G k) :
    2 ≤ k := by
  let v : V := Classical.choice ‹Nonempty V›
  by_contra h₂
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · obtain ⟨D, _, hD⟩ := hk
    have hpos : 0 < (G.neighborFinset v).card := by rw [card_neighbors, hreg]; decide
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    obtain ⟨i, _⟩ := (hD v w).mp ((G.mem_neighborFinset v w).mp hw)
    exact Fin.elim0 i
  · obtain ⟨D, hDf, hD⟩ := hk
    have he : G = D 0 := by
      ext x y
      constructor
      · intro h
        obtain ⟨i, hi, _⟩ := (hD x y).mp h
        have hi0 : i = 0 := Subsingleton.elim _ _
        exact hi0 ▸ hi
      · intro h
        exact (hDf 0).2 h
    have hd : degreeN (D 0) v ≤ 2 := (hDf 0).1.2 v
    rw [← he, hreg] at hd
    omega

private theorem cubic_arboricity [Nonempty V] (G : SimpleGraph V)
    (hreg : ∀ v, degreeN G v = 3) : linearArboricity G = 2 := by
  have h₂ := two_decomposition G hreg
  unfold linearArboricity
  apply le_antisymm (Nat.sInf_le h₂)
  have hmem := Nat.sInf_mem (s := {k : ℕ | HasLinearForestDecomposition G k}) ⟨2, h₂⟩
  exact neither_zero_nor_one G hreg hmem

end CubicArboricity

theorem OMA.solution : type_of% @LinearArboricityConjecture.linear_arboricity_conjecture.variants.cubic := by
  intro V instF instN G instAdj hreg
  exact CubicArboricity.cubic_arboricity G fun v =>
    (CubicArboricity.degreeN_eq_degree G v).trans (hreg v)