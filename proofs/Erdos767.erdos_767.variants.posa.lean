import FormalConjectures.ErdosProblems.«767»
import Mathlib.Tactic

-- Problem: Erdős Problem 767 — posa
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/767.lean:75 (declaration Erdos767.erdos_767.variants.posa)
-- Credit: @malikfassi (the owner of the agent is credited as the solver)
-- Upper bound: without a cycle with a chord every nonempty vertex set has a vertex with at most
-- two neighbours inside it (longest-path argument; that lemma and its helper are the ones from
-- the merged proof of the Czipszer variant in this repository). Peeling such vertices down to
-- four vertices, which span at most four edges, gives at most 2n - 4 edges.
-- Lower bound: the complete bipartite graph with sides {0, 1} and the rest has 2n - 4 edges,
-- and a vertex of the large side on a cycle uses both small vertices as cycle neighbours, so
-- no edge at it can be a chord.

open SimpleGraph Erdos767

namespace OMA.Posa

lemma edge_from_start_of_isPath {V : Type*} {G : SimpleGraph V} {u w y : V} (q : G.Walk u w)
    (hq : q.IsPath) (he : s(u, y) ∈ q.edges) : y = q.snd := by
  cases q with
  | nil => simp at he
  | cons h r =>
    rw [Walk.cons_isPath_iff] at hq
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · rw [Sym2.eq_iff] at he
      rcases he with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
      · simp
      · simp
    · exact absurd (r.fst_mem_support_of_mem_edges he) hq.2

lemma exists_low_degree {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (hG : ¬ HasCycleWithIncidentChords G k) (S : Finset V)
    (hS : S.Nonempty) : ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ k + 1 := by
  classical
  obtain ⟨s, hs⟩ := hS
  let P : ℕ → Prop := fun m => ∃ (u w : V) (p : G.Walk u w), p.IsPath ∧
    (∀ z ∈ p.support, z ∈ S) ∧ p.length = m
  have hP0 : P 0 := ⟨s, s, Walk.nil, by simp, by simp [hs], rfl⟩
  have hPb : ∀ m, P m → m ≤ Fintype.card V := by
    rintro m ⟨u, w, p, hp, -, rfl⟩
    exact hp.length_lt.le
  obtain ⟨u, w, p, hp, hpS, hpl⟩ : P (Nat.findGreatest P (Fintype.card V)) :=
    Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ m, P m → m ≤ Nat.findGreatest P (Fintype.card V) :=
    fun m hm => Nat.le_findGreatest (hPb m hm) hm
  refine ⟨u, hpS u p.start_mem_support, ?_⟩
  by_contra hlt
  push Not at hlt
  set N := S.filter (G.Adj u) with hNdef
  have hN : ∀ y ∈ N, y ∈ p.support := by
    intro y hy
    rw [Finset.mem_filter] at hy
    by_contra hyp
    have hP : P (Nat.findGreatest P (Fintype.card V) + 1) := by
      refine ⟨y, w, Walk.cons hy.2.symm p, hp.cons hyp, ?_, by simp [hpl]⟩
      intro z hz
      rw [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hy.1
      · exact hpS z hz
    have := hmax _ hP
    omega
  have hNne : N.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨x, hxN, hxmax⟩ := N.exists_max_image (fun y => p.support.idxOf y) hNne
  have hxp := hN x hxN
  have hux : G.Adj u x := (Finset.mem_filter.mp hxN).2
  have hxu : x ≠ u := hux.ne.symm
  set q := p.takeUntil x hxp with hqdef
  have hqpath : q.IsPath := hp.takeUntil hxp
  have hsuppq : q.support = p.support.take (p.support.idxOf x + 1) := by
    rw [hqdef, Walk.takeUntil_eq_take, Walk.support_copy, Walk.support_take]
  have hyq : ∀ y ∈ N, y ∈ q.support := by
    intro y hy
    rw [hsuppq, List.mem_take_iff_getElem]
    have hyl : p.support.idxOf y < p.support.length :=
      List.idxOf_lt_length_iff.mpr (hN y hy)
    refine ⟨p.support.idxOf y, ?_, List.getElem_idxOf hyl⟩
    have := hxmax y hy
    omega
  -- index facts
  have hidx_pos : ∀ y ∈ N, 1 ≤ p.support.idxOf y := by
    intro y hy
    have hyu : y ≠ u := ((Finset.mem_filter.mp hy).2).ne.symm
    rw [← Walk.cons_tail_support,List.idxOf_cons_ne _ hyu.symm]
    omega
  have hcard2 : 2 ≤ N.card := by omega
  obtain ⟨y0, hy0N, hy0x⟩ : ∃ y ∈ N, y ≠ x := by
    by_contra hcon
    push Not at hcon
    have : N ⊆ {x} := fun y hy => Finset.mem_singleton.mpr (hcon y hy)
    have := Finset.card_le_card this
    simp at this
    omega
  have hlt0 : p.support.idxOf y0 < p.support.idxOf x := by
    have h1 := hxmax y0 hy0N
    rcases h1.lt_or_eq with h | h
    · exact h
    · exact absurd ((List.idxOf_inj (hN y0 hy0N)).mp h) hy0x
  have hqlen : 2 ≤ q.length := by
    rw [hqdef, Walk.length_takeUntil]
    have := hidx_pos y0 hy0N
    omega
  have hsnd : q.snd ≠ x := by
    rw [hqdef, Walk.snd_takeUntil hxu]
    exact Walk.getVert_lt_length_takeUntil_ne hxp (by rw [← hqdef]; omega)
  -- the cycle
  let c : G.Walk u u := Walk.cons hux q.reverse
  have hc : c.IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨hqpath.reverse, ?_⟩
    rw [Walk.edges_reverse, List.mem_reverse]
    intro he
    exact hsnd (edge_from_start_of_isPath q hqpath he).symm
  set T := (N.erase x).erase q.snd with hT
  have hTcard : k ≤ T.card := by
    have h1 := Finset.pred_card_le_card_erase (s := N) (a := x)
    have h2 := Finset.pred_card_le_card_erase (s := N.erase x) (a := q.snd)
    rw [hT]
    omega
  obtain ⟨T', hT'T, hT'card⟩ := Finset.exists_subset_card_eq hTcard
  refine hG ⟨u, c, hc, fun i => (T'.equivFin.symm (Fin.cast hT'card.symm i)).1, ?_, ?_⟩
  · intro i j hij
    have := Subtype.val_injective hij
    simpa using this
  · intro i
    set y := (T'.equivFin.symm (Fin.cast hT'card.symm i)).1
    have hyT : y ∈ T := hT'T (T'.equivFin.symm (Fin.cast hT'card.symm i)).2
    rw [hT, Finset.mem_erase, Finset.mem_erase] at hyT
    obtain ⟨hysnd, hyx, hyN⟩ := hyT
    rw [Walk.isChord_sym2Mk]
    refine ⟨(Finset.mem_filter.mp hyN).2, ?_, ?_, ?_⟩
    · simp only [c, Walk.edges_cons, Walk.edges_reverse, List.mem_cons, List.mem_reverse]
      rintro (h | h)
      · rw [Sym2.eq_iff] at h
        rcases h with ⟨-, h⟩ | ⟨h, -⟩
        · exact hyx h
        · exact hxu h.symm
      · exact hysnd (edge_from_start_of_isPath q hqpath h)
    · simp [c]
    · simp only [c, Walk.support_cons, Walk.support_reverse, List.mem_cons, List.mem_reverse]
      exact Or.inr (hyq y hyN)
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Removing a vertex `v` loses at most as many edges inside `S` as `v` has neighbours in `S`. -/
lemma peel (S : Finset V) (v : V) (hv : v ∈ S) :
    (G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S)).card ≤
      (G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S.erase v)).card +
        (S.filter (G.Adj v)).card := by
  have hsub : G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S) ⊆
      G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S.erase v) ∪
        (S.filter (G.Adj v)).image (fun w => s(v, w)) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet] at he
      have ha := he.2 a (Sym2.mem_mk_left a b)
      have hb := he.2 b (Sym2.mem_mk_right a b)
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_image, mem_edgeFinset, mem_edgeSet]
      by_cases hav : a = v
      · subst hav
        exact Or.inr ⟨b, Finset.mem_filter.mpr ⟨hb, he.1⟩, rfl⟩
      by_cases hbv : b = v
      · subst hbv
        exact Or.inr ⟨a, Finset.mem_filter.mpr ⟨ha, he.1.symm⟩, Sym2.eq_swap⟩
      refine Or.inl ⟨he.1, ?_⟩
      intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_erase.mpr ⟨hav, ha⟩
      · exact Finset.mem_erase.mpr ⟨hbv, hb⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S.erase v))
    ((S.filter (G.Adj v)).image (fun w => s(v, w)))
  have h3 := Finset.card_image_le (s := S.filter (G.Adj v)) (f := fun w => s(v, w))
  omega

lemma nbr_sub (S : Finset V) (v : V) : S.filter (G.Adj v) ⊆ S.erase v := by
  intro w hw
  rw [Finset.mem_filter] at hw
  exact Finset.mem_erase.2 ⟨hw.2.ne.symm, hw.1⟩

lemma nbr_le (S : Finset V) (v : V) (hv : v ∈ S) : (S.filter (G.Adj v)).card + 1 ≤ S.card := by
  have h := Finset.card_le_card (nbr_sub (G := G) S v)
  rw [Finset.card_erase_of_mem hv] at h
  have hpos : 0 < S.card := Finset.card_pos.2 ⟨v, hv⟩
  omega

lemma E_empty : (G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ (∅ : Finset V))).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e _ h
  induction e using Sym2.ind with
  | h a b => simpa using h a (Sym2.mem_mk_left a b)

lemma E_le_one (S : Finset V) (hS : S.card ≤ 1) :
    (G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S)).card = 0 := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · exact E_empty
  · have h1 := peel (G := G) S v hv
    have h2 := nbr_le (G := G) S v hv
    have h3 : S.erase v = ∅ := by
      rw [← Finset.card_eq_zero, Finset.card_erase_of_mem hv]
      omega
    rw [h3, E_empty] at h1
    omega

lemma E_two (S : Finset V) (hS : S.card = 2) :
    (G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S)).card ≤ 1 := by
  obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  have h1 := peel (G := G) S v hv
  have h2 := nbr_le (G := G) S v hv
  have h3 := E_le_one (G := G) (S.erase v) (by rw [Finset.card_erase_of_mem hv]; omega)
  omega

lemma E_three (S : Finset V) (hS : S.card = 3) :
    (G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S)).card ≤ 3 := by
  obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  have h1 := peel (G := G) S v hv
  have h2 := nbr_le (G := G) S v hv
  have h3 := E_two (G := G) (S.erase v) (by rw [Finset.card_erase_of_mem hv]; omega)
  omega

/-- Three vertices spanning three edges form a triangle. -/
lemma tri_adj (T : Finset V) (hT : T.card = 3)
    (hE : 3 ≤ (G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ T)).card)
    (p q : V) (hp : p ∈ T) (hq : q ∈ T) (hne : q ≠ p) : G.Adj p q := by
  have h1 := peel (G := G) T p hp
  have h2 := E_two (G := G) (T.erase p) (by rw [Finset.card_erase_of_mem hp]; omega)
  have hcard : (T.erase p).card ≤ (T.filter (G.Adj p)).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  have heq := Finset.eq_of_subset_of_card_le (nbr_sub (G := G) T p) hcard
  have hmem : q ∈ T.filter (G.Adj p) := by
    rw [heq]
    exact Finset.mem_erase.2 ⟨hne, hq⟩
  exact (Finset.mem_filter.1 hmem).2

/-- Four vertices span at most four edges when no cycle has a chord. -/
lemma base (hG : ¬ HasCycleWithIncidentChords G 1) (S : Finset V) (hS : S.card = 4) :
    (G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S)).card ≤ 4 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨v, hvS, hv⟩ := exists_low_degree hG S (Finset.card_pos.1 (by omega))
  have h1 := peel (G := G) S v hvS
  have hTc : (S.erase v).card = 3 := by
    rw [Finset.card_erase_of_mem hvS]
    omega
  have h2 := E_three (G := G) (S.erase v) hTc
  have hN : 1 < (S.filter (G.Adj v)).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hN
  rw [Finset.mem_filter] at ha hb
  have haT : a ∈ S.erase v := Finset.mem_erase.2 ⟨ha.2.ne.symm, ha.1⟩
  have hbT : b ∈ S.erase v := Finset.mem_erase.2 ⟨hb.2.ne.symm, hb.1⟩
  have hc3 : 0 < (((S.erase v).erase a).erase b).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hab.symm, hbT⟩),
      Finset.card_erase_of_mem haT]
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.1 hc3
  rw [Finset.mem_erase, Finset.mem_erase] at hc
  obtain ⟨hcb, hca, hcT⟩ := hc
  have hET : 3 ≤ (G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S.erase v)).card := by omega
  have hac : G.Adj a c := tri_adj _ hTc hET a c haT hcT hca
  have hcb' : G.Adj c b := tri_adj _ hTc hET c b hcT hbT hcb.symm
  have hab' : G.Adj a b := tri_adj _ hTc hET a b haT hbT hab.symm
  have hcv : c ≠ v := (Finset.mem_erase.1 hcT).1
  have hca' : a ≠ c := hca.symm
  have hbc : b ≠ c := hcb.symm
  have hba : b ≠ a := hab.symm
  have hva : v ≠ a := ha.2.ne
  have hav : a ≠ v := hva.symm
  have hvb : v ≠ b := hb.2.ne
  have hbv : b ≠ v := hvb.symm
  have hvc : v ≠ c := hcv.symm
  refine hG ⟨a, Walk.cons hac (Walk.cons hcb' (Walk.cons hb.2.symm (Walk.cons ha.2 Walk.nil))),
    ?_, fun _ => b, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [Walk.cons_isPath_iff, hcb, hcv, hca, hbv, hba, hva]
    · simp [Sym2.eq_iff, hca', hcb, hca, hab, hba, hbc, hav, hva, hcv, hvc]
  · intro i j _
    exact Subsingleton.elim i j
  · intro _
    rw [Walk.isChord_sym2Mk]
    refine ⟨hab', ?_, by simp, by simp⟩
    simp [Sym2.eq_iff, hca', hcb, hca, hab, hba, hbc, hav, hva, hbv, hvb]

/-- Pósa's bound: without a cycle with a chord, `S` spans at most `2|S| - 4` edges. -/
lemma card_edges_le (hG : ¬ HasCycleWithIncidentChords G 1) :
    ∀ S : Finset V, 4 ≤ S.card →
      (G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S)).card + 4 ≤ 2 * S.card := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    by_cases h4 : S.card = 4
    · have := base hG S h4
      omega
    · obtain ⟨v, hvS, hv⟩ := exists_low_degree hG S (Finset.card_pos.1 (by omega))
      have h1 := peel (G := G) S v hvS
      have h5 := Finset.card_erase_of_mem hvS
      have h6 := ih (S.erase v) (Finset.erase_ssubset hvS) (by omega)
      omega

/-- The complete bipartite graph with sides `{0, 1}` and the rest. -/
def K (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun a b : Fin n => a.val < 2 ∧ 2 ≤ b.val)

lemma K_adj {n : ℕ} (a b : Fin n) :
    (K n).Adj a b ↔ (a.val < 2 ∧ 2 ≤ b.val) ∨ (b.val < 2 ∧ 2 ≤ a.val) := by
  rw [K, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    omega

/-- In `K n` a vertex of the large side on a cycle has both small vertices as cycle neighbours. -/
lemma K_key {n : ℕ} {v : Fin n} (c : (K n).Walk v v) (hc : c.IsCycle) (a b : Fin n)
    (ha : a.val < 2) (hb : 2 ≤ b.val) (hbs : b ∈ c.support) : s(a, b) ∈ c.edges := by
  have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hbs
  by_contra hne
  have hsub : c.toSubgraph.neighborSet b ⊆ ({x : Fin n | x.val < 2} \ {a}) := by
    intro x hx
    rw [Subgraph.mem_neighborSet] at hx
    have hadj := c.toSubgraph.adj_sub hx
    rw [K_adj] at hadj
    refine ⟨?_, ?_⟩
    · show x.val < 2
      omega
    · intro hxa
      rw [Set.mem_singleton_iff] at hxa
      subst hxa
      apply hne
      rw [Walk.adj_toSubgraph_iff_mem_edges] at hx
      rwa [Sym2.eq_swap]
  have hle : ({x : Fin n | x.val < 2} \ {a}).ncard ≤ 1 := by
    rw [Set.ncard_le_one_iff]
    intro x y hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    have hx1' : x.val < 2 := hx1
    have hy1' : y.val < 2 := hy1
    have hx2' : x.val ≠ a.val := fun h => hx2 (Set.mem_singleton_iff.2 (Fin.ext h))
    have hy2' : y.val ≠ a.val := fun h => hy2 (Set.mem_singleton_iff.2 (Fin.ext h))
    exact Fin.ext (by omega)
  have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

lemma K_free (n : ℕ) : ¬ HasCycleWithIncidentChords (K n) 1 := by
  rintro ⟨v, c, hc, f, -, hf⟩
  have hch := hf 0
  rw [Walk.isChord_sym2Mk] at hch
  obtain ⟨hadj, hnot, hv, hw⟩ := hch
  rw [K_adj] at hadj
  rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hnot (K_key c hc v (f 0) h1 h2 hw)
  · apply hnot
    rw [Sym2.eq_swap]
    exact K_key c hc (f 0) v h1 h2 hv

lemma K_edges (n : ℕ) (hn : 4 ≤ n) [Fintype (K n).edgeSet] :
    2 * n - 4 ≤ (K n).edgeFinset.card := by
  have hn0 : 0 < n := by omega
  have hcard : ((Finset.range 2) ×ˢ (Finset.Ico 2 n)).card = 2 * n - 4 := by
    rw [Finset.card_product, Finset.card_range, Nat.card_Ico]
    omega
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun p : ℕ × ℕ => s((⟨p.1 % n, Nat.mod_lt _ hn0⟩ : Fin n), (⟨p.2 % n, Nat.mod_lt _ hn0⟩ : Fin n)))
  · rintro ⟨i, j⟩ hp
    have hp' : (i, j) ∈ (Finset.range 2) ×ˢ (Finset.Ico 2 n) := hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_Ico] at hp'
    have e1 : i % n = i := Nat.mod_eq_of_lt (by omega)
    have e2 : j % n = j := Nat.mod_eq_of_lt (by omega)
    show s((⟨i % n, Nat.mod_lt _ hn0⟩ : Fin n), (⟨j % n, Nat.mod_lt _ hn0⟩ : Fin n)) ∈
      (K n).edgeFinset
    rw [mem_edgeFinset, mem_edgeSet, K_adj]
    left
    show i % n < 2 ∧ 2 ≤ j % n
    omega
  · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hq h
    have hp' : (i, j) ∈ (Finset.range 2) ×ˢ (Finset.Ico 2 n) := hp
    have hq' : (i', j') ∈ (Finset.range 2) ×ˢ (Finset.Ico 2 n) := hq
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_Ico] at hp' hq'
    have e1 : i % n = i := Nat.mod_eq_of_lt (by omega)
    have e2 : j % n = j := Nat.mod_eq_of_lt (by omega)
    have e3 : i' % n = i' := Nat.mod_eq_of_lt (by omega)
    have e4 : j' % n = j' := Nat.mod_eq_of_lt (by omega)
    have h' : s((⟨i % n, Nat.mod_lt _ hn0⟩ : Fin n), (⟨j % n, Nat.mod_lt _ hn0⟩ : Fin n)) =
        s((⟨i' % n, Nat.mod_lt _ hn0⟩ : Fin n), (⟨j' % n, Nat.mod_lt _ hn0⟩ : Fin n)) := h
    rw [Sym2.eq_iff] at h'
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have k1 : i % n = i' % n := congrArg Fin.val h1
      have k2 : j % n = j' % n := congrArg Fin.val h2
      exact Prod.ext (by show i = i'; omega) (by show j = j'; omega)
    · have k1 : i % n = j' % n := congrArg Fin.val h1
      exfalso
      omega

end OMA.Posa

open OMA.Posa in
theorem OMA.solution : type_of% @Erdos767.erdos_767.variants.posa := by
  classical
  intro n hn
  unfold Erdos767.g
  have hub : ∀ m ∈ {m | ∃ G : SimpleGraph (Fin n),
      ¬ HasCycleWithIncidentChords G 1 ∧ G.edgeFinset.card = m}, m ≤ 2 * n - 4 := by
    rintro m ⟨G, hG, rfl⟩
    have h := card_edges_le hG Finset.univ (by rw [Finset.card_univ, Fintype.card_fin]; exact hn)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have h' := Nat.le_sub_of_add_le h
    refine le_trans (le_of_eq ?_) h'
    congr 1
    ext e
    simp
  apply le_antisymm
  · exact csSup_le' hub
  · exact le_trans (K_edges n hn) (le_csSup ⟨_, hub⟩ ⟨K n, K_free n, rfl⟩)
