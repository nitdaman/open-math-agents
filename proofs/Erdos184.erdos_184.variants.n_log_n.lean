import FormalConjectures.ErdosProblems.«184»
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Order.Interval.Finset.Nat

/-!
The greedy longest-cycle argument for the Erdős–Gallai logarithmic decomposition bound.
-/

open Filter Finset SimpleGraph
open scoped Classical

universe u

private theorem degree_le_of_no_long_cycle {V : Type u} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k)
    (h : ∀ (v : V) (p : G.Walk v v), p.IsCycle → p.length ≤ k + 1) :
    ∃ v, G.degree v ≤ k := by
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨u, ?_⟩
  have hsubset : G.neighborFinset u ⊆ (Icc 1 k).image p.getVert := by
    intro x hx
    have hadj := (G.mem_neighborFinset u x).mp hx
    have hs : x ∈ p.support := by
      by_contra hn
      have hlong := hmax x v (Walk.cons hadj.symm p) (hp.cons hn)
      simp only [Walk.length_cons] at hlong
      omega
    obtain ⟨i, hix, hip⟩ := Walk.mem_support_iff_exists_getVert.mp hs
    have hi : 1 ≤ i := by
      by_contra hn
      have he : i = 0 := by omega
      subst i
      exact hadj.ne (by simpa using hix)
    have hik : i ≤ k := by
      by_contra hn
      have hiadj : G.Adj (p.getVert i) u := hix.symm ▸ hadj.symm
      let q := Walk.cons hiadj (p.take i)
      have hqLen : q.length = i + 1 := by
        simp [q, Walk.take_length, inf_eq_left.mpr hip]
      have hq : q.IsCycle := by
        apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
        refine ⟨?_, by rw [hqLen]; omega⟩
        simpa [q, Walk.tail_cons] using hp.take i
      have hn' := h (p.getVert i) q hq
      omega
    exact mem_image.mpr ⟨i, mem_Icc.mpr ⟨hi, hik⟩, hix⟩
  rw [← card_neighborFinset_eq_degree]
  exact (card_le_card hsubset).trans (card_image_le.trans_eq (by simp [Nat.card_Icc]))

private theorem edge_bound_of_no_long_cycle (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Fintype.card V = n →
      (∀ (v : V) (p : G.Walk v v), p.IsCycle → p.length ≤ k + 1) →
      G.edgeFinset.card ≤ k * n := by
  induction n with
  | zero =>
    intro V _ _ G hn _
    have h := G.card_edgeFinset_le_card_choose_two
    simpa [hn] using h
  | succ n ih =>
    intro V _ _ G hn h
    let _ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v, hv⟩ := degree_le_of_no_long_cycle G k hk h
    let S : Set V := ({v} : Set V)ᶜ
    let F := G.induce S
    let f : F →g G := ⟨Subtype.val, fun ha => ha⟩
    have hF (w : S) (p : F.Walk w w) (hp : p.IsCycle) : p.length ≤ k + 1 := by
      have hq : (p.map f).IsCycle := (Walk.isCycle_map_iff_of_injective Subtype.val_injective).mpr hp
      simpa only [Walk.length_map] using h (f w) (p.map f) hq
    have ht : Fintype.card S = n := by
      have hcard : Fintype.card ({v} : Set V) = 1 := Fintype.card_unique
      change Fintype.card ↥(({v} : Set V)ᶜ) = n
      rw [Fintype.card_compl_set, hcard, hn]
      omega
    have hsmall := ih F ht hF
    have hcount : F.edgeFinset.card = G.edgeFinset.card - G.degree v := by
      change (G.induce ({v} : Set V)ᶜ).edgeFinset.card = _
      rw [card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet]
    have hsplit : F.edgeFinset.card + G.degree v = G.edgeFinset.card := by
      rw [hcount, Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)]
    rw [Nat.mul_succ]
    exact hsplit.symm.le.trans (Nat.add_le_add hsmall hv)

private theorem dense_graph_has_long_cycle {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hm : Fintype.card V < G.edgeFinset.card) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ G.edgeFinset.card ≤ Fintype.card V * p.length := by
  let n := Fintype.card V
  let m := G.edgeFinset.card
  have hn : 0 < n := by
    by_contra! h
    have hn₀ : Fintype.card V = 0 := by omega
    have he : G.edgeFinset.card ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
    rw [hn₀] at he
    change G.edgeFinset.card ≤ 0 at he
    omega
  let k := (m - 1) / n
  have hk : 1 ≤ k := by
    apply (Nat.le_div_iff_mul_le hn).mpr
    omega
  have hkn : k * n ≤ m - 1 := Nat.div_mul_le_self _ _
  have hlong : ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ k + 2 ≤ p.length := by
    by_contra! h
    have hh := edge_bound_of_no_long_cycle k hk n G rfl (fun v p hp => by have := h v p hp; omega)
    omega
  obtain ⟨v, p, hp, hl⟩ := hlong
  have hmN : m ≤ n * (k + 1) := by
    have he := Nat.div_add_mod (m - 1) n
    have hr := Nat.mod_lt (m - 1) hn
    change n * k + (m - 1) % n = m - 1 at he
    rw [Nat.mul_succ]
    omega
  exact ⟨v, p, hp, hmN.trans (Nat.mul_le_mul_left _ (by omega))⟩

private theorem edge_card_eq_ncard {V : Type u} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] : G.edgeFinset.card = G.edgeSet.ncard := by
  exact (Set.ncard_eq_toFinset_card' G.edgeSet).symm

private theorem coe_edge_card {V : Type u} [Fintype V] (G : SimpleGraph V) (H : G.Subgraph) :
    H.coe.edgeFinset.card = H.edgeSet.ncard := by
  rw [edge_card_eq_ncard, ← H.image_coe_edgeSet_coe]
  exact (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)).symm

private theorem cycle_subgraph_good {V : Type u} [Fintype V] (G : SimpleGraph V)
    {v : V} (p : G.Walk v v) (hp : p.IsCycle) : Erdos184.IsCycleOrEdge p.toSubgraph.coe := by
  apply Or.inl
  refine ⟨p.toSubgraph_connected.coe, ?_⟩
  intro w
  rw [Subgraph.coe_degree]
  change Fintype.card (p.toSubgraph.neighborSet (w : V)) = 2
  rw [Set.fintypeCard_eq_ncard]
  exact hp.ncard_neighborSet_toSubgraph_eq_two ((Walk.mem_verts_toSubgraph p).mp w.property)

private theorem cycle_edge_count {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    {v : V} (p : G.Walk v v) (hp : p.IsCycle) : p.toSubgraph.edgeSet.ncard = p.length := by
  rw [Walk.edgeSet_toSubgraph, ← p.coe_edges_toFinset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hp.isTrail.edges_nodup, Walk.length_edges]

private theorem select_decomposition_piece {V : Type u} [Fintype V] [DecidableEq V]
    (G F : SimpleGraph V) (hle : F ≤ G) (hm : 0 < F.edgeFinset.card) :
    ∃ H : G.Subgraph, Erdos184.IsCycleOrEdge H.coe ∧ H.edgeSet ⊆ F.edgeSet ∧
      0 < H.edgeSet.ncard ∧
      (Fintype.card V < F.edgeFinset.card → F.edgeFinset.card ≤ Fintype.card V * H.edgeSet.ncard) := by
  by_cases hdense : Fintype.card V < F.edgeFinset.card
  · obtain ⟨u, p, hp, hsize⟩ := dense_graph_has_long_cycle F hdense
    let q := p.mapLe hle
    have hq : q.IsCycle := hp.mapLe hle
    have hcount : q.toSubgraph.edgeSet.ncard = p.length := by
      rw [cycle_edge_count G q hq]
      exact Walk.length_mapLe _ _
    have hsub : q.toSubgraph.edgeSet ⊆ F.edgeSet := by
      intro e he
      rw [Walk.edgeSet_toSubgraph, Walk.mem_edgeSet] at he
      change e ∈ (p.mapLe hle).edges at he
      rw [Walk.edges_mapLe_eq_edges] at he
      exact p.edges_subset_edgeSet he
    exact ⟨q.toSubgraph, cycle_subgraph_good G q hq, hsub,
      hcount ▸ (by have := hp.three_le_length; omega), fun _ => hcount ▸ hsize⟩
  · obtain ⟨e, he⟩ := card_pos.mp hm
    induction e using Sym2.ind with
    | h a b =>
      have hab : F.Adj a b := by simpa using he
      let H := G.subgraphOfAdj (hle hab)
      have hH : H.edgeSet = {s(a, b)} := by simp [H]
      have hcount : H.edgeSet.ncard = 1 := by rw [hH, Set.ncard_singleton]
      refine ⟨H, Or.inr ((coe_edge_card G H).trans hcount), ?_, by rw [hcount]; decide,
        fun h => (hdense h).elim⟩
      rw [hH, Set.singleton_subset_iff]
      exact hab

private theorem insert_piece_decomposition {V : Type u} (G F : SimpleGraph V) (H : G.Subgraph)
    (D : Finset G.Subgraph) (hH : H.edgeSet ⊆ F.edgeSet)
    (hdisj : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun J => J.edgeSet))
    (hcover : (⋃ J ∈ D, J.edgeSet) = (F.deleteEdges H.edgeSet).edgeSet) :
    Set.PairwiseDisjoint (↑(insert H D) : Set G.Subgraph) (fun J => J.edgeSet) ∧
      (⋃ J ∈ insert H D, J.edgeSet) = F.edgeSet := by
  classical
  have hsub (J : G.Subgraph) (hJ : J ∈ D) : J.edgeSet ⊆ (F.deleteEdges H.edgeSet).edgeSet := by
    intro e he
    rw [← hcover]
    exact Set.mem_iUnion.mpr ⟨J, Set.mem_iUnion.mpr ⟨hJ, he⟩⟩
  have hseparate (J : G.Subgraph) (hJ : J ∈ D) : Disjoint H.edgeSet J.edgeSet := by
    refine Set.disjoint_left.mpr fun e heH heJ => ?_
    have he := hsub J hJ heJ
    rw [edgeSet_deleteEdges] at he
    exact he.2 heH
  constructor
  · intro A hA B hB hab
    change A ∈ insert H D at hA
    change B ∈ insert H D at hB
    rcases mem_insert.mp hA with rfl | ha <;> rcases mem_insert.mp hB with rfl | hb
    · exact (hab rfl).elim
    · exact hseparate _ hb
    · exact (hseparate _ ha).symm
    · exact hdisj ha hb hab
  · ext e
    simp only [Set.mem_iUnion, exists_prop, mem_insert]
    constructor
    · rintro ⟨J, heJ, he⟩
      rcases heJ with rfl | hj
      · exact hH he
      · have hs := hsub J hj he
        rw [edgeSet_deleteEdges] at hs
        exact hs.1
    · intro he
      by_cases h : e ∈ H.edgeSet
      · exact ⟨H, Or.inl rfl, h⟩
      · have he' : e ∈ (F.deleteEdges H.edgeSet).edgeSet := by
          rw [edgeSet_deleteEdges]
          exact ⟨he, h⟩
        rw [← hcover] at he'
        obtain ⟨J, hJ, hj⟩ := Set.mem_iUnion.mp he'
          |>.imp fun _ h => Set.mem_iUnion.mp h
        exact ⟨J, Or.inr hJ, hj⟩

private noncomputable def cycleBudget (n m : ℕ) : ℝ :=
  n * (1 + Real.log ((max 1 m : ℕ) : ℝ))

private theorem le_cycleBudget (n m : ℕ) : (n : ℝ) ≤ cycleBudget n m := by
  have hh : 1 ≤ ((max 1 m : ℕ) : ℝ) := by exact_mod_cast (le_max_left 1 m)
  have hlog := Real.log_nonneg hh
  unfold cycleBudget
  nlinarith only [mul_nonneg (Nat.cast_nonneg n) hlog]

private theorem cycleBudget_step {n m r h : ℕ} (hr : 0 < r)
    (hsum : r + h = m) (hbig : m ≤ n * h) : cycleBudget n r + 1 ≤ cycleBudget n m := by
  have hm : 0 < m := by omega
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsumR : (r : ℝ) + h = m := by exact_mod_cast hsum
  have hbigR : (m : ℝ) ≤ (n : ℝ) * h := by exact_mod_cast hbig
  have hlog := Real.log_le_sub_one_of_pos (div_pos hrR hmR)
  rw [Real.log_div hrR.ne' hmR.ne'] at hlog
  have hdiv : (h : ℝ) / m = 1 - (r : ℝ) / m := by
    rw [← div_self hmR.ne', ← sub_div]
    congr 1
    linarith only [hsumR]
  have hlog' : (h : ℝ) / m ≤ Real.log m - Real.log r := by linarith only [hdiv, hlog]
  have hone : (1 : ℝ) ≤ (n : ℝ) * ((h : ℝ) / m) := by
    rw [← mul_div_assoc]
    exact (one_le_div hmR).mpr hbigR
  have hgap := hone.trans (mul_le_mul_of_nonneg_left hlog' (Nat.cast_nonneg n))
  simp only [cycleBudget, max_eq_right (show 1 ≤ r by omega),
    max_eq_right (show 1 ≤ m by omega)]
  nlinarith only [hgap]

private theorem edge_card_le_square {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    G.edgeFinset.card ≤ Fintype.card V ^ 2 :=
  G.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ _)

private theorem decompose_with_budget {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m : ℕ) :
    ∀ F : SimpleGraph V, F ≤ G → F.edgeFinset.card = m →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, Erdos184.IsCycleOrEdge H.coe) ∧
        Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) ∧
        (⋃ H ∈ D, H.edgeSet) = F.edgeSet ∧ D.card ≤ m ∧
        (D.card : ℝ) ≤ cycleBudget (Fintype.card V) m := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro F hle hFcard
    by_cases hzero : m = 0
    · have hfin : F.edgeFinset = ∅ := Finset.card_eq_zero.mp (hFcard.trans hzero)
      have hF : F.edgeSet = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro e he
        have hh : e ∈ F.edgeFinset := mem_edgeFinset.mpr he
        rw [hfin] at hh
        exact (Finset.notMem_empty e) hh
      refine ⟨∅, by simp, ?_, by simp [hF], by simp, ?_⟩
      · intro H hH
        simp at hH
      · simp only [Finset.card_empty, Nat.cast_zero]
        exact (Nat.cast_nonneg _).trans (le_cycleBudget _ _)
    have hm : 0 < F.edgeFinset.card := by omega
    obtain ⟨H, hH, hsub, hpos, hbig⟩ := select_decomposition_piece G F hle hm
    let R := F.deleteEdges H.edgeSet
    have hR : R ≤ G := (deleteEdges_le _).trans hle
    have hsplit : R.edgeFinset.card + H.edgeSet.ncard = m := by
      rw [edge_card_eq_ncard R]
      change (F.deleteEdges H.edgeSet).edgeSet.ncard + _ = _
      rw [edgeSet_deleteEdges, Set.ncard_sdiff_add_ncard_of_subset hsub,
        ← edge_card_eq_ncard F, hFcard]
    have hlt : R.edgeFinset.card < m := by omega
    obtain ⟨D, hpieces, hdisj, hcover, hDsize, hbudget⟩ :=
      ih R.edgeFinset.card hlt R hR (by simp only [edge_card_eq_ncard])
    have hi := insert_piece_decomposition G F H D hsub hdisj hcover
    have hInsert := Finset.card_insert_le H D
    have hSize : (insert H D).card ≤ m := by omega
    refine ⟨insert H D, ?_, hi.1, hi.2, hSize, ?_⟩
    · intro K hk
      rcases mem_insert.mp hk with rfl | hk
      · exact hH
      · exact hpieces _ hk
    let n := Fintype.card V
    by_cases hSmall : m ≤ n
    · have hcast : ((insert H D).card : ℝ) ≤ n := by exact_mod_cast hSize.trans hSmall
      exact hcast.trans (le_cycleBudget n m)
    · have hlarge : m ≤ n * H.edgeSet.ncard := by
        have h := hbig (by omega)
        simpa only [hFcard] using h
      by_cases hEmpty : R.edgeFinset.card = 0
      · have hOne : (insert H D).card ≤ 1 := by omega
        have hn : 1 ≤ n := by
          by_contra! h
          have he : n = 0 := by omega
          rw [he, zero_mul] at hlarge
          omega
        have hcast : ((insert H D).card : ℝ) ≤ n := by exact_mod_cast hOne.trans hn
        exact hcast.trans (le_cycleBudget n m)
      · have hRpos : 0 < R.edgeFinset.card := Nat.pos_of_ne_zero hEmpty
        calc
          ((insert H D).card : ℝ) ≤ (D.card : ℝ) + 1 := by exact_mod_cast hInsert
          _ ≤ cycleBudget n R.edgeFinset.card + 1 := by linarith only [hbudget]
          _ ≤ cycleBudget n m := cycleBudget_step hRpos hsplit hlarge

theorem OMA.solution : type_of% @Erdos184.erdos_184.variants.n_log_n := by
  let f : ℕ → ℝ := fun n => n * (1 + 2 * Real.log n)
  refine ⟨f, ?_, ?_⟩
  · apply Asymptotics.IsBigO.of_bound 3
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
    have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
    have hf : 0 ≤ f n := by dsimp [f]; positivity
    have hg : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by positivity
    rw [Real.norm_of_nonneg hf, Real.norm_of_nonneg hg]
    dsimp [f]
    nlinarith only [mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg n)]
  · intro V _ _ G
    obtain ⟨D, hpieces, hdisj, hcover, _, hbound⟩ :=
      decompose_with_budget G G.edgeFinset.card G le_rfl rfl
    refine ⟨D, hpieces, ⟨hdisj, hcover⟩, hbound.trans ?_⟩
    let n := Fintype.card V
    let m := G.edgeFinset.card
    change cycleBudget n m ≤ f n
    by_cases he : n = 0
    · simp [cycleBudget, f, he]
    have hn : 0 < n := Nat.pos_of_ne_zero he
    have hmax : max 1 m ≤ n ^ 2 :=
      max_le (Nat.pow_pos hn) (edge_card_le_square G)
    have hp : (0 : ℝ) < ((max 1 m : ℕ) : ℝ) := by
      exact_mod_cast (Nat.zero_lt_one.trans_le (le_max_left 1 m))
    have hcast : ((max 1 m : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hmax
    have hlog : Real.log ((max 1 m : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hp hcast
    have hsum : 1 + Real.log ((max 1 m : ℕ) : ℝ) ≤ 1 + 2 * Real.log (n : ℝ) := by
      linarith only [hlog]
    exact mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n)