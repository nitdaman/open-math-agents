import FormalConjectures.Arxiv.«2606.03696».BondyLongestCycles

-- Problem: Arxiv 2606.03696 bondy_conjecture variants one
-- Upstream: formal-conjectures FormalConjectures/Arxiv/2606.03696/BondyLongestCycles.lean (declaration Arxiv.«2606.03696».bondy_conjecture.variants.one)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)

/-!
Dirac's theorem. Take a longest path, written as a list of vertices. Every neighbour of an
end lies on the path, and the degree condition gives a crossing pair of chords, which closes
the path into a cycle on the same vertices. If some vertex were off this cycle, connectivity
would give an edge leaving the cycle, and the cycle opened at that edge would be a longer
path. So the cycle passes through all vertices, and a longest cycle missing a vertex is
impossible.
-/

namespace OMA.Dirac

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A cyclic list: consecutive entries are adjacent, and so are the last and the first. -/
def Cyc (G : SimpleGraph V) (c : List V) : Prop :=
  c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b

lemma rot {c : List V} (hc : Cyc G c) {q : V} (hq : q ∈ c) :
    ∃ c' : List V, c'.Perm c ∧ c'.IsChain G.Adj ∧ c'.head? = some q := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hq
  refine ⟨(q :: B) ++ A, List.perm_append_comm, ?_, by simp⟩
  obtain ⟨hch, hcl⟩ := hc
  rw [List.isChain_append] at hch
  refine List.isChain_append.2 ⟨hch.2.1, hch.1, ?_⟩
  intro x hx y hy
  apply hcl
  · rw [List.getLast?_append]
    have : (q :: B).getLast? = some x := hx
    simp [this]
  · rw [List.head?_append, hy]
    rfl

lemma edge_not_mem {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    s(u, v) ∉ p.edges := by
  cases p with
  | nil => simp at hlen
  | @cons _ w _ hadj p' =>
    intro hmem
    rw [Walk.edges_cons, List.mem_cons] at hmem
    have hnd := hp.support_nodup
    rw [Walk.support_cons, List.nodup_cons] at hnd
    rcases hmem with h | h
    · rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · subst h2
        have hp' : p'.IsPath := hp.of_cons
        have : p'.length = 0 := by
          rcases p' with _ | ⟨h'', p''⟩
          · rfl
          · exfalso
            have := hp'.support_nodup
            simp at this
        simp [this] at hlen
      · subst h1
        exact hadj.ne rfl
    · exact hnd.1 (Walk.fst_mem_support_of_mem_edges p' h)

lemma cycle_of_list (c : List V) (hnd : c.Nodup) (hc : Cyc G c) (h3 : 3 ≤ c.length) :
    c.length ∈ G.cycleLengths := by
  have hne : c ≠ [] := by
    rintro rfl
    simp at h3
  set W := Walk.ofSupport c hne hc.1
  have hW : W.support = c := Walk.support_ofSupport hne hc.1
  have hWl : W.length = c.length - 1 := Walk.length_ofSupport hne hc.1
  have hpath : W.IsPath := Walk.IsPath.mk' (by rw [hW]; exact hnd)
  have hadj : G.Adj (c.head hne) (c.getLast hne) := by
    refine (?_ : G.Adj (c.getLast hne) (c.head hne)).symm
    apply hc.2
    · exact List.getLast?_eq_getLast hne
    · exact List.head?_eq_some_head hne
  refine ⟨c.head hne, Walk.cons hadj W.reverse, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨hpath.reverse, ?_⟩
    rw [Walk.edges_reverse, List.mem_reverse]
    exact edge_not_mem W hpath (by omega)
  · rw [Walk.length_cons, Walk.length_reverse, hWl]
    omega

lemma cycle_length_le {a : V} (w : G.Walk a a) (hw : w.IsCycle) : w.length ≤ Fintype.card V := by
  have h1 := hw.support_nodup.length_le_card
  rw [List.length_tail, Walk.length_support] at h1
  omega

lemma getD_zero (l : List V) (hl : l ≠ []) (d : V) : l.getD 0 d = l.head hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

lemma getD_last (l : List V) (hl : l ≠ []) (d : V) : l.getD (l.length - 1) d = l.getLast hl := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem]

theorem dirac (h3 : 3 ≤ Fintype.card V) (hconn : ∀ a b : V, G.Reachable a b)
    [DecidableRel G.Adj] (hdeg : ∀ v, Fintype.card V ≤ 2 * G.degree v) :
    ∃ c : List V, c.Nodup ∧ Cyc G c ∧ c.length = Fintype.card V := by
  classical
  set n := Fintype.card V with hn
  obtain ⟨v0⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let PP : ℕ → Prop := fun k => ∃ l : List V, (l.Nodup ∧ l.IsChain G.Adj) ∧ l.length = k
  have h1 : PP 1 := ⟨[v0], ⟨by simp, List.isChain_singleton _⟩, rfl⟩
  set M := Nat.findGreatest PP n
  obtain ⟨l, ⟨hlnd, hlch⟩, hlM⟩ : PP M := Nat.findGreatest_spec (by omega) h1
  have hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ M :=
    fun l' h1 h2 => Nat.le_findGreatest h1.length_le_card ⟨l', ⟨h1, h2⟩, rfl⟩
  have hM1 : 1 ≤ M := Nat.le_findGreatest (by omega) h1
  have hl_ne : l ≠ [] := by
    rintro rfl
    simp at hlM
    omega
  set q0 := l.head hl_ne
  set z := l.getLast hl_ne
  have hmn : l.length ≤ n := hlnd.length_le_card
  have ext_head : ∀ y, G.Adj q0 y → y ∈ l := by
    intro y hy
    by_contra hyl
    have := hmax (y :: l) (List.nodup_cons.2 ⟨hyl, hlnd⟩)
      (List.IsChain.cons_of_ne_nil hl_ne hlch ((hy).symm))
    simp at this
    omega
  have ext_last : ∀ y, G.Adj z y → y ∈ l := by
    intro y hy
    by_contra hyl
    have hch : (l ++ [y]).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hlch, List.isChain_singleton _, ?_⟩
      intro x hx y' hy'
      rw [List.getLast?_eq_getLast hl_ne] at hx
      simp at hx hy'
      subst hx hy'
      exact hy
    have hnd : (l ++ [y]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hlnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp at hb
      subst hb
      rintro rfl
      exact hyl ha
    have := hmax _ hnd hch
    simp at this
    omega
  set m := l.length with hm
  have hq0 : l.getD 0 q0 = q0 := getD_zero l hl_ne q0
  have hz : l.getD (m - 1) q0 = z := getD_last l hl_ne q0
  -- the two index sets
  let S := (Finset.range (m - 1)).filter (fun j => G.Adj q0 (l.getD (j + 1) q0))
  let T := (Finset.range (m - 1)).filter (fun j => G.Adj (l.getD j q0) z)
  have hS : G.degree q0 ≤ S.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S)
      (f := fun j => l.getD (j + 1) q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_head y hy)
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hq0]
    rw [Finset.mem_image]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
      exact hy
    · rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
  have hT : G.degree z ≤ T.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := T)
      (f := fun j => l.getD j q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_last y hy)
    have hkm : k ≠ m - 1 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hz]
    rw [Finset.mem_image]
    refine ⟨k, ?_, List.getD_eq_getElem _ _ hk⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [List.getD_eq_getElem _ _ hk]
    exact (hy).symm
  have hdq := hdeg q0
  have hdz := hdeg z
  obtain ⟨j, hjS, hjT⟩ : ∃ j, j ∈ S ∧ j ∈ T := by
    by_contra hcon
    push Not at hcon
    have hdisj : Disjoint S T := Finset.disjoint_left.mpr hcon
    have hsub : S ∪ T ⊆ Finset.range (m - 1) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_range] at this
    omega
  rw [Finset.mem_filter, Finset.mem_range] at hjS hjT
  obtain ⟨hjm, hA⟩ := hjS
  obtain ⟨-, hB⟩ := hjT
  -- the cycle
  set c := l.take (j + 1) ++ (l.drop (j + 1)).reverse with hcdef
  have hperm : c.Perm l := by
    have := (List.Perm.append_left (l.take (j + 1)) (List.reverse_perm (l.drop (j + 1))))
    rw [List.take_append_drop] at this
    exact this
  have hcnd : c.Nodup := hperm.nodup_iff.mpr hlnd
  have hj1 : j < m := by omega
  have hj2 : j + 1 < m := by omega
  have e1 : (l.take (j + 1)).getLast? = some (l.getD j q0) := by
    rw [List.getLast?_take, List.getD_eq_getElem _ _ hj1]
    simp [List.getElem?_eq_getElem hj1]
  have e2 : (l.drop (j + 1)).reverse.head? = some z := by
    rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega), List.getLast?_eq_getLast hl_ne]
  have e3 : c.getLast? = some (l.getD (j + 1) q0) := by
    rw [hcdef, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
      List.getElem?_eq_getElem hj2, List.getD_eq_getElem _ _ hj2]
    rfl
  have e4 : c.head? = some q0 := by
    rw [hcdef, List.head?_append, List.head?_take]
    simp [List.head?_eq_some_head hl_ne, q0]
  have hcyc : Cyc G c := by
    refine ⟨List.isChain_append.2 ⟨hlch.take _, ?_, ?_⟩, ?_⟩
    · rw [List.isChain_reverse]
      exact (hlch.drop _).imp (fun a b h => h.symm)
    · intro x hx y hy
      rw [e1] at hx
      rw [e2] at hy
      simp at hx hy
      subst hx hy
      exact hB
    · intro a ha b hb
      rw [e3] at ha
      rw [e4] at hb
      simp at ha hb
      subst ha hb
      exact (hA).symm
  -- every vertex lies on the path
  have hall : ∀ w, w ∈ l := by
    intro w
    by_contra hw
    obtain ⟨p⟩ := hconn q0 w
    obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x ∈ l} (List.head_mem hl_ne) hw
    have hqc : d.fst ∈ c := hperm.mem_iff.mpr hd1
    obtain ⟨c', hc'p, hc'ch, hc'h⟩ := rot hcyc hqc
    have hnd' : (d.snd :: c').Nodup := by
      refine List.nodup_cons.2 ⟨?_, (hc'p.trans hperm).nodup_iff.mpr hlnd⟩
      intro hmem
      exact hd2 ((hc'p.trans hperm).mem_iff.mp hmem)
    have hch' : (d.snd :: c').IsChain G.Adj := by
      refine List.isChain_cons.2 ⟨?_, hc'ch⟩
      intro y hy
      rw [hc'h] at hy
      simp at hy
      subst hy
      exact (d.adj).symm
    have := hmax _ hnd' hch'
    rw [List.length_cons, (hc'p.trans hperm).length_eq] at this
    omega
  have hmn' : m = n := by
    have h1 : l.toFinset = Finset.univ := by
      ext w
      simp [hall w]
    have h2 := List.toFinset_card_of_nodup hlnd
    rw [h1, Finset.card_univ] at h2
    omega
  exact ⟨c, hcnd, hcyc, by rw [hperm.length_eq]; exact hmn'⟩

end OMA.Dirac

open SimpleGraph OMA.Dirac in
theorem OMA.solution : type_of% @Arxiv.«2606.03696».bondy_conjecture.variants.one := by
  intro V _ _ G _ hG hd a C hC hlong u v P hP
  exfalso
  classical
  set n := Fintype.card V
  have hu : u.1 ∉ C.support := u.2
  have hCle : C.length + 1 ≤ n := by
    have hnd := hC.support_nodup
    have hsub : C.support.tail.toFinset ⊆ Finset.univ.erase u.1 := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      exact hu (List.mem_of_mem_tail (List.mem_toFinset.mp hx))
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, List.length_tail, Walk.length_support] at this
    have h3 := hC.three_le_length
    omega
  have h3 := hC.three_le_length
  have hdeg : ∀ w, n ≤ 2 * G.degree w := by
    intro w
    have h1 : (G.minDegree : ℝ) ≤ G.degree w := by exact_mod_cast G.minDegree_le_degree w
    have h2 : (n : ℝ) ≤ 2 * G.degree w := by linarith
    exact_mod_cast h2
  have hconn : ∀ x y : V, G.Reachable x y := by
    intro x y
    have hc := hG.2 ∅ (by simp)
    have hr := hc.preconnected ⟨x, by simp⟩ ⟨y, by simp⟩
    exact hr.map (Embedding.induce _).toHom
  obtain ⟨c, hcnd, hcyc, hclen⟩ := dirac (by omega) hconn hdeg
  have hmem := cycle_of_list c hcnd hcyc (by omega)
  have hbdd : BddAbove G.cycleLengths := by
    refine ⟨n, ?_⟩
    rintro k ⟨b, w, hw, rfl⟩
    exact cycle_length_le w hw
  have := le_csSup hbdd hmem
  rw [hclen] at this
  have hcirc : G.circumference = C.length := hlong.symm
  unfold circumference at hcirc
  omega
