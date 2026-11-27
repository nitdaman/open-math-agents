import OMAReductions.R_Erdos1182_erdos_1182_variants_befrs_lower_R1_H1_R1
import Mathlib.Logic.Equiv.Fintype

/-! Contract two adjacent degree-two vertices and extend a blue copy of the contracted graph.
This formalizes the suspended-path argument in https://www.renyi.hu/~p_erdos/1980-04.pdf. -/

-- Step Erdos1182.erdos_1182.variants.befrs_lower.R1.H1.R1.H2: hypothesis H2 of reduction Erdos1182.erdos_1182.variants.befrs_lower.R1.H1.R1
-- Credit: @dk8827
-- H2 := ∀ {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m)),     4 ≤ l → 2 * l - 1 ≤ m → G.Connected → C.CliqueFree 3 →     (∃ x y, G.Adj x y ∧ (G.neighborSet x).ncard = 2 ∧ (G.neighborSet y).ncard = 2) →     ∃ H : SimpleGraph (Fin (l - 1)), H.Connected ∧       H.edgeSet.ncard + 1 ≤ G.edgeSet.ncard ∧ (H.IsContained Cᶜ → G.IsContained Cᶜ)

open SimpleGraph

lemma embed_anchored {V W : Type} [Fintype V] [Fintype W]
    (hcard : Fintype.card V ≤ Fintype.card W)
    {a b : V} {c d : W} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ f : V ↪ W, f a = c ∧ f b = d := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let before (k : Bool) := if k then e a else e b
  let after (k : Bool) := if k then c else d
  have hbefore : Function.Injective before := by
    intro i j h
    cases i <;> cases j <;> simp_all [before, e.injective.ne hab]
  have hafter : Function.Injective after := by
    intro i j h
    cases i <;> cases j <;> simp_all [after]
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair before after hbefore hafter
  exact ⟨e.trans p.toEmbedding, hp true, hp false⟩

lemma embed_in_blue_clique {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    (X : Finset (Fin m)) (hcard : l ≤ X.card)
    (hblue : ∀ a ∈ X, ∀ b ∈ X, ¬ C.Adj a b) : G.IsContained Cᶜ := by
  classical
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hcard
  refine isContained_iff_exists_le_comap.mpr ⟨(S.orderEmbOfFin hScard).toEmbedding, ?_⟩
  intro u w huw
  change Cᶜ.Adj (S.orderEmbOfFin hScard u) (S.orderEmbOfFin hScard w)
  rw [compl_adj]
  refine ⟨(S.orderEmbOfFin hScard).injective.ne (G.ne_of_adj huw), ?_⟩
  exact hblue _ (hS (S.orderEmbOfFin_mem hScard u)) _ (hS (S.orderEmbOfFin_mem hScard w))

lemma embed_in_near_blue_clique {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    (X : Finset (Fin m)) (hcard : l ≤ X.card)
    {x y : Fin l} (hxy : x ≠ y) (hnxy : ¬ G.Adj x y)
    {r s : Fin m} (hr : r ∈ X) (hs : s ∈ X) (hrs : r ≠ s)
    (hred : ∀ a ∈ X, ∀ b ∈ X, C.Adj a b → (a = r ∧ b = s) ∨ (a = s ∧ b = r)) :
    G.IsContained Cᶜ := by
  classical
  have hsz : Fintype.card (Fin l) ≤ Fintype.card ↥X := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hcard
  have hh : (⟨r, hr⟩ : ↥X) ≠ ⟨s, hs⟩ := fun he => hrs (congrArg Subtype.val he)
  obtain ⟨f, hfx, hfy⟩ := embed_anchored hsz hxy hh
  let e : Fin l ↪ Fin m := f.trans ⟨Subtype.val, Subtype.val_injective⟩
  have hex : e x = r := congrArg Subtype.val hfx
  have hey : e y = s := congrArg Subtype.val hfy
  refine isContained_iff_exists_le_comap.mpr ⟨e, ?_⟩
  intro a b hab
  change Cᶜ.Adj (e a) (e b)
  rw [compl_adj]
  refine ⟨e.injective.ne (G.ne_of_adj hab), ?_⟩
  intro h
  rcases hred (e a) (f a).property (e b) (f b).property h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have ha' := e.injective (ha.trans hex.symm)
    have hb' := e.injective (hb.trans hey.symm)
    exact hnxy (ha' ▸ hb' ▸ hab)
  · have ha' := e.injective (ha.trans hey.symm)
    have hb' := e.injective (hb.trans hex.symm)
    exact hnxy (hb' ▸ ha' ▸ hab.symm)

lemma embed_blue_clique_with_apex {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    (X : Finset (Fin m)) (hcard : l - 1 ≤ X.card)
    {x y z : Fin l} (hy : y ≠ x) (hz : z ≠ x) (hyz : y ≠ z)
    (hN : ∀ a, G.Adj x a → a = y ∨ a = z)
    {v r s : Fin m} (hv : v ∉ X) (hr : r ∈ X) (hs : s ∈ X) (hrs : r ≠ s)
    (hvr : Cᶜ.Adj v r) (hvs : Cᶜ.Adj v s)
    (hblue : ∀ a ∈ X, ∀ b ∈ X, ¬ C.Adj a b) : G.IsContained Cᶜ := by
  classical
  let U := (Finset.univ : Finset (Fin l)).erase x
  have hu (a : Fin l) (ha : a ≠ x) : a ∈ U := Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩
  have hsz : Fintype.card ↥U ≤ Fintype.card ↥X := by
    rw [Fintype.card_coe, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ, Fintype.card_fin]
    exact hcard
  have hh : (⟨y, hu y hy⟩ : ↥U) ≠ ⟨z, hu z hz⟩ := fun he => hyz (congrArg Subtype.val he)
  have hh' : (⟨r, hr⟩ : ↥X) ≠ ⟨s, hs⟩ := fun he => hrs (congrArg Subtype.val he)
  obtain ⟨f, hfY, hfZ⟩ := embed_anchored hsz hh hh'
  let g (a : Fin l) : Fin m := if ha : a ≠ x then (f ⟨a, hu a ha⟩).val else v
  have gx : g x = v := dif_neg (not_not.mpr rfl)
  have gg (a : Fin l) (ha : a ≠ x) : g a = (f ⟨a, hu a ha⟩).val := dif_pos ha
  have gin (a : Fin l) (ha : a ≠ x) : g a ∈ X := by rw [gg a ha]; exact (f _).property
  have gi : Function.Injective g := by
    intro a b hab
    by_contra hn
    by_cases ha : a = x
    · subst a
      exact hv (gx ▸ hab ▸ gin b (Ne.symm hn))
    · by_cases hb : b = x
      · subst b
        exact hv (gx ▸ hab.symm ▸ gin a hn)
      · rw [gg a ha, gg b hb] at hab
        exact hn (congrArg Subtype.val (f.injective (Subtype.ext hab)))
  have ghx (a : Fin l) (ha : G.Adj x a) : Cᶜ.Adj (g x) (g a) := by
    rw [gx]
    rcases hN a ha with h | h
    · subst a
      rw [gg y hy, hfY]
      exact hvr
    · subst a
      rw [gg z hz, hfZ]
      exact hvs
  refine isContained_iff_exists_le_comap.mpr ⟨⟨g, gi⟩, ?_⟩
  intro a b hab
  change Cᶜ.Adj (g a) (g b)
  by_cases ha : a = x
  · subst a
    exact ghx b hab
  · by_cases hb : b = x
    · subst b
      exact (ghx a hab.symm).symm
    · exact (compl_adj C _ _).mpr
        ⟨gi.ne (G.ne_of_adj hab), hblue _ (gin a ha) _ (gin b hb)⟩

lemma place_two_vertices {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    {x y : Fin l} (hxy : x ≠ y)
    (R : Set (Fin l)) (hR : ∀ z, z ∈ R ↔ z ≠ x ∧ z ≠ y)
    (f : R ↪ Fin m)
    (hf : ∀ a b : R, G.Adj a b → Cᶜ.Adj (f a) (f b))
    {p q : Fin m} (hpq : Cᶜ.Adj p q)
    (hp : ∀ a : R, p ≠ f a) (hq : ∀ a : R, q ≠ f a)
    (hx : ∀ a : R, G.Adj x a → Cᶜ.Adj p (f a))
    (hy : ∀ a : R, G.Adj y a → Cᶜ.Adj q (f a)) :
    G.IsContained Cᶜ := by
  classical
  let g (z : Fin l) : Fin m := if hz : z ∈ R then f ⟨z, hz⟩ else if z = x then p else q
  have gX : g x = p := by
    have h : x ∉ R := fun h => ((hR x).mp h).1 rfl
    simp [g, h]
  have gY : g y = q := by
    have h : y ∉ R := fun h => ((hR y).mp h).2 rfl
    simp [g, h, hxy.symm]
  have gR (a : R) : g a = f a := dif_pos a.property
  have casesR (a : Fin l) : a = x ∨ a = y ∨ a ∈ R := by
    by_cases ha : a = x
    · exact Or.inl ha
    by_cases hb : a = y
    · exact Or.inr (Or.inl hb)
    exact Or.inr (Or.inr ((hR a).mpr ⟨ha, hb⟩))
  have hginj : Function.Injective g := by
    intro a b hab
    rcases casesR a with ha | ha | ha
    · subst a
      rcases casesR b with hb | hb | hb
      · exact hb.symm
      · subst b
        exact ((compl_adj C _ _).mp hpq).1 (gX.symm.trans (hab.trans gY)) |>.elim
      · exact (hp ⟨b, hb⟩ (gX.symm.trans (hab.trans (gR ⟨b, hb⟩)))).elim
    · subst a
      rcases casesR b with hb | hb | hb
      · subst b
        exact ((compl_adj C _ _).mp hpq).1 (gX.symm.trans (hab.symm.trans gY)) |>.elim
      · exact hb.symm
      · exact (hq ⟨b, hb⟩ (gY.symm.trans (hab.trans (gR ⟨b, hb⟩)))).elim
    · rcases casesR b with hb | hb | hb
      · subst b
        exact (hp ⟨a, ha⟩ (gX.symm.trans (hab.symm.trans (gR ⟨a, ha⟩)))).elim
      · subst b
        exact (hq ⟨a, ha⟩ (gY.symm.trans (hab.symm.trans (gR ⟨a, ha⟩)))).elim
      · exact congrArg Subtype.val (f.injective
          ((gR ⟨a, ha⟩).symm.trans (hab.trans (gR ⟨b, hb⟩))))
  have gxAdj (z : Fin l) (h : G.Adj x z) : Cᶜ.Adj (g x) (g z) := by
    rw [gX]
    rcases casesR z with hz | hz | hz
    · exact (G.ne_of_adj h hz.symm).elim
    · subst z
      rw [gY]
      exact hpq
    · exact (gR ⟨z, hz⟩).symm ▸ hx ⟨z, hz⟩ h
  have gyAdj (z : Fin l) (h : G.Adj y z) : Cᶜ.Adj (g y) (g z) := by
    rw [gY]
    rcases casesR z with hz | hz | hz
    · subst z
      rw [gX]
      exact hpq.symm
    · exact (G.ne_of_adj h hz.symm).elim
    · exact (gR ⟨z, hz⟩).symm ▸ hy ⟨z, hz⟩ h
  refine isContained_iff_exists_le_comap.mpr ⟨⟨g, hginj⟩, ?_⟩
  intro a b hab
  change Cᶜ.Adj (g a) (g b)
  rcases casesR a with ha | ha | ha
  · subst a
    exact gxAdj b hab
  · subst a
    exact gyAdj b hab
  · rcases casesR b with hb | hb | hb
    · subst b
      exact (gxAdj a hab.symm).symm
    · subst b
      exact (gyAdj a hab.symm).symm
    · exact (gR ⟨a, ha⟩).symm ▸ (gR ⟨b, hb⟩).symm ▸ hf ⟨a, ha⟩ ⟨b, hb⟩ hab

theorem pathContractionGraph {l : ℕ} (G : SimpleGraph (Fin l)) (x y u : Fin l)
    (hconn : G.Connected) (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : y ≠ u)
    (hN : ∀ a, G.Adj x a → a = y ∨ a = u)
    (W : Finset (Fin l)) (hW : W = Finset.univ.erase x)
    (Y U : ↥W) (hY : (Y : Fin l) = y) (hU : (U : Fin l) = u)
    (H : SimpleGraph ↥W)
    (hH : H = G.induce (↑W : Set (Fin l)) ⊔ fromEdgeSet {s(Y, U)}) :
    H.Connected ∧ H.edgeSet.ncard + 1 ≤ G.edgeSet.ncard := by
  classical
  have hyu' : Y ≠ U := fun h => hyu (hY.symm.trans ((congrArg Subtype.val h).trans hU))
  have hju : H.Adj Y U := by
    rw [hH]
    exact Or.inr ((fromEdgeSet_adj _).mpr ⟨by simp, hyu'⟩)
  have he (a : Fin l) (ha : a ≠ x) : a ∈ W := by
    rw [hW]
    exact Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩
  have hmem (a : Fin l) (ha : a ∈ W) : a ≠ x := by
    rw [hW, Finset.mem_erase] at ha
    exact ha.1
  have hne (A : ↥W) : (A : Fin l) ≠ x := hmem A.val A.property
  let f (a : Fin l) : ↥W := if ha : a = x then Y else ⟨a, he a ha⟩
  have hfx : f x = Y := dif_pos rfl
  have hf (a : Fin l) (ha : a ≠ x) : f a = ⟨a, he a ha⟩ := dif_neg ha
  have hfy : f y = Y := by
    rw [hf y (G.ne_of_adj hxy.symm)]
    exact Subtype.ext hY.symm
  have hfu : f u = U := by
    rw [hf u (G.ne_of_adj hxu.symm)]
    exact Subtype.ext hU.symm
  have fromX (v : Fin l) (hxv : G.Adj x v) : H.Reachable (f x) (f v) := by
    rcases hN v hxv with hv | hv
    · rw [hv, hfx, hfy]
    · rw [hv, hfx, hfu]
      exact hju.reachable
  have hadj {a b : Fin l} (hab : G.Adj a b) : H.Reachable (f a) (f b) := by
    by_cases ha : a = x
    · subst a
      exact fromX b hab
    · by_cases hb : b = x
      · subst b
        exact (fromX a hab.symm).symm
      · rw [hf a ha, hf b hb]
        exact (show H.Adj ⟨a, he a ha⟩ ⟨b, he b hb⟩ by
          rw [hH]
          exact Or.inl hab).reachable
  have reach {a b : Fin l} (p : G.Walk a b) : H.Reachable (f a) (f b) := by
    induction p with
    | nil => exact Reachable.rfl
    | cons h _ ih => exact (hadj h).trans ih
  constructor
  · refine (connected_iff _).mpr ⟨?_, ⟨Y⟩⟩
    intro A B
    have hfa : f A = A := by
      rw [hf _ (hne A)]
    have hfb : f B = B := by
      rw [hf _ (hne B)]
    obtain ⟨p⟩ := hconn.preconnected A B
    simpa only [hfa, hfb] using reach p
  · let J := G.induce (↑W : Set (Fin l))
    let K : SimpleGraph ↥W := fromEdgeSet {s(Y, U)}
    have hpair : G.degree x = 2 := by
      classical
      rw [← card_neighborFinset_eq_degree]
      have hn : G.neighborFinset x = {y, u} := by
        ext v
        rw [mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨hN v, fun h => h.elim (fun hv => hv.symm ▸ hxy) (fun hv => hv.symm ▸ hxu)⟩
      rw [hn, Finset.card_pair hyu]
    have hdecrease : J.edgeFinset.card + 2 ≤ G.edgeFinset.card := by
      change (G.induce (↑W : Set (Fin l))).edgeFinset.card + 2 ≤ G.edgeFinset.card
      rw [← card_filter_edgeFinset_toFinset_subset]
      let E := G.edgeFinset.filter (fun e => e.toFinset ⊆ W)
      have hdis : Disjoint E (G.incidenceFinset x) := by
        apply Finset.disjoint_left.mpr
        intro e hE hinc
        rw [incidenceFinset_eq_filter, Finset.mem_filter] at hinc
        have hxW := (Finset.mem_filter.mp hE).2 (Sym2.mem_toFinset.mpr hinc.2)
        rw [hW, Finset.mem_erase] at hxW
        exact hxW.1 rfl
      have hle : (E ∪ G.incidenceFinset x).card ≤ G.edgeFinset.card :=
        Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (G.incidenceFinset_subset x))
      rw [Finset.card_union_of_disjoint hdis, card_incidenceFinset_eq_degree, hpair] at hle
      exact hle
    have hk : K.edgeSet.ncard ≤ 1 := by
      change (fromEdgeSet ({s(Y, U)} : Set (Sym2 ↥W))).edgeSet.ncard ≤ 1
      rw [edgeSet_fromEdgeSet]
      simpa using Set.ncard_le_ncard (Set.sdiff_subset :
        ({s(Y, U)} : Set (Sym2 ↥W)) \ Sym2.diagSet ⊆ {s(Y, U)})
    have hbound : H.edgeSet.ncard ≤ J.edgeSet.ncard + K.edgeSet.ncard := by
      have hh : H = J ⊔ K := hH
      rw [hh, edgeSet_sup]
      exact Set.ncard_union_le _ _
    have hj : J.edgeSet.ncard + 2 ≤ G.edgeSet.ncard := by
      rw [← coe_edgeFinset, ← coe_edgeFinset (G := G), Set.ncard_coe_finset,
        Set.ncard_coe_finset]
      exact hdecrease
    omega

lemma adjacent_degree_two_other {l : ℕ} (G : SimpleGraph (Fin l)) {x y : Fin l}
    (hxy : G.Adj x y) (hx : (G.neighborSet x).ncard = 2) :
    ∃ u, u ≠ y ∧ G.Adj x u ∧ ∀ t, G.Adj x t → t = y ∨ t = u := by
  obtain ⟨a, b, hab, h⟩ := Set.ncard_eq_two.mp hx
  have hm (t : Fin l) : G.Adj x t ↔ t = a ∨ t = b := by
    change t ∈ G.neighborSet x ↔ _
    rw [h, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases (hm y).mp hxy with rfl | rfl
  · exact ⟨b, hab.symm, (hm b).mpr (Or.inr rfl), fun t ht => (hm t).mp ht⟩
  · exact ⟨a, hab, (hm a).mpr (Or.inl rfl), fun t ht => ((hm t).mp ht).symm⟩

lemma shorten_keeps_blue_copy {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    (hl : 4 ≤ l) (hm : 2 * l - 1 ≤ m) (hC : C.CliqueFree 3)
    {x y u v : Fin l} (hxy : G.Adj x y) (hxu : G.Adj x u) (hyv : G.Adj y v)
    (huy : u ≠ y) (hvx : v ≠ x)
    (hx : ∀ t, G.Adj x t → t = y ∨ t = u)
    (hy : ∀ t, G.Adj y t → t = x ∨ t = v)
    (W : Finset (Fin l)) (hW : W = Finset.univ.erase x)
    (Y U V : ↥W) (hY : Y.val = y) (hU : U.val = u) (hV : V.val = v)
    (H : SimpleGraph ↥W) (hH : H = G.induce (↑W : Set (Fin l)) ⊔ fromEdgeSet {s(Y, U)})
    (hcopy : H.IsContained Cᶜ) : G.IsContained Cᶜ := by
  classical
  obtain ⟨f, hf⟩ := isContained_iff_exists_le_comap.mp hcopy
  let used := (Finset.univ : Finset ↥W).map f
  let X := usedᶜ
  have hUsed : used.card = l - 1 := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_coe, hW,
      Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]
  have hX : l ≤ X.card := by
    change l ≤ usedᶜ.card
    rw [Finset.card_compl, Fintype.card_fin, hUsed]
    omega
  have outside (a : Fin m) (ha : a ∈ X) (b : ↥W) : a ≠ f b := by
    intro e
    exact Finset.mem_compl.mp ha (e ▸ Finset.mem_map_of_mem f (Finset.mem_univ b))
  have blueOutside (a : Fin m) (ha : a ∈ X) (b : ↥W) (hn : ¬ C.Adj a (f b)) :
      Cᶜ.Adj a (f b) := (compl_adj C _ _).mpr ⟨outside a ha b, hn⟩
  have hYU : Cᶜ.Adj (f Y) (f U) := hf (show H.Adj Y U by
    rw [hH]
    apply Or.inr
    apply (fromEdgeSet_adj _).mpr
    exact ⟨by simp, fun e => huy (hU.symm.trans ((congrArg Subtype.val e).symm.trans hY))⟩)
  have hYV : Cᶜ.Adj (f Y) (f V) := hf (show H.Adj Y V by
    rw [hH]
    apply Or.inl
    change G.Adj Y.val V.val
    simpa only [hY, hV] using hyv)
  let R : Set (Fin l) := {t | t ≠ x ∧ t ≠ y}
  let incl : R ↪ ↥W := ⟨fun a => ⟨a.val, by
    rw [hW]
    exact Finset.mem_erase.mpr ⟨a.property.1, Finset.mem_univ _⟩⟩,
    fun a b e => Subtype.ext (congrArg (fun w : ↥W => w.val) e)⟩
  let e := incl.trans f
  have eAdj (a b : R) (h : G.Adj a b) : Cᶜ.Adj (e a) (e b) := hf (show H.Adj (incl a) (incl b) by
    rw [hH]
    exact Or.inl h)
  have eX (a : Fin m) (ha : a ∈ X) (b : R) : a ≠ e b := outside a ha (incl b)
  have eY (a : R) : f Y ≠ e a := by
    intro he
    have e' := congrArg Subtype.val (f.injective he)
    exact a.property.2 (e'.symm.trans hY)
  have place {p q : Fin m} (hpq : Cᶜ.Adj p q)
      (hp : ∀ a : R, p ≠ e a) (hq : ∀ a : R, q ≠ e a)
      (hpu : Cᶜ.Adj p (f U)) (hqv : Cᶜ.Adj q (f V)) : G.IsContained Cᶜ := by
    refine place_two_vertices G C (G.ne_of_adj hxy) R (fun _ => Iff.rfl) e eAdj hpq hp hq ?_ ?_
    · intro a ha
      have hau := (hx a ha).resolve_left a.property.2
      have he' : e a = f U := congrArg f (Subtype.ext (hau.trans hU.symm))
      simpa only [he'] using hpu
    · intro a ha
      have hav := (hy a ha).resolve_left a.property.1
      have he' : e a = f V := congrArg f (Subtype.ext (hav.trans hV.symm))
      simpa only [he'] using hqv
  by_contra hbad
  -- Partition the unused host vertices by their colour to the image of the retained vertex.
  let A := X.filter (fun t => C.Adj (f Y) t)
  let B := X.filter (fun t => Cᶜ.Adj (f Y) t)
  have Ared (a : Fin m) (ha : a ∈ A) : C.Adj (f Y) a := (Finset.mem_filter.mp ha).2
  have Bblue (b : Fin m) (hb : b ∈ B) : Cᶜ.Adj (f Y) b := (Finset.mem_filter.mp hb).2
  have AX (a : Fin m) (ha : a ∈ A) : a ∈ X := (Finset.mem_filter.mp ha).1
  have BX (b : Fin m) (hb : b ∈ B) : b ∈ X := (Finset.mem_filter.mp hb).1
  have partition (t : Fin m) (ht : t ∈ X) : t ∈ A ∨ t ∈ B := by
    by_cases h : C.Adj (f Y) t
    · exact Or.inl (Finset.mem_filter.mpr ⟨ht, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨ht, (compl_adj C _ _).mpr ⟨(outside t ht Y).symm, h⟩⟩)
  have BredU (b : Fin m) (hb : b ∈ B) : C.Adj b (f U) := by
    by_contra h
    exact hbad (place (Bblue b hb).symm (eX b (BX b hb)) eY
      (blueOutside b (BX b hb) U h) hYV)
  have BredV (b : Fin m) (hb : b ∈ B) : C.Adj b (f V) := by
    by_contra h
    exact hbad (place (Bblue b hb) eY (eX b (BX b hb)) hYU
      (blueOutside b (BX b hb) V h))
  have Aind (a : Fin m) (ha : a ∈ A) (b : Fin m) (hb : b ∈ A) : ¬ C.Adj a b :=
    fun h => hC _ (is3Clique_triple_iff.mpr ⟨Ared a ha, Ared b hb, h⟩)
  have Bind (a : Fin m) (ha : a ∈ B) (b : Fin m) (hb : b ∈ B) : ¬ C.Adj a b :=
    fun h => hC _ (is3Clique_triple_iff.mpr ⟨(BredU a ha).symm, (BredU b hb).symm, h⟩)
  -- Any vertex incident to a red edge across this partition can replace an endpoint.
  let P := A.filter (fun a => ∃ b ∈ B, C.Adj a b)
  have PA (a : Fin m) (ha : a ∈ P) : a ∈ A := (Finset.mem_filter.mp ha).1
  have Pblue (a : Fin m) (ha : a ∈ P) : Cᶜ.Adj a (f U) ∧ Cᶜ.Adj a (f V) := by
    obtain ⟨b, hb, hab⟩ := (Finset.mem_filter.mp ha).2
    refine ⟨blueOutside a (AX a (PA a ha)) U ?_, blueOutside a (AX a (PA a ha)) V ?_⟩
    · exact fun h => hC _ (is3Clique_triple_iff.mpr ⟨hab, h, BredU b hb⟩)
    · exact fun h => hC _ (is3Clique_triple_iff.mpr ⟨hab, h, BredV b hb⟩)
  have uniqueP (a : Fin m) (ha : a ∈ P) (b : Fin m) (hb : b ∈ P) : a = b := by
    by_contra hn
    have hpq : Cᶜ.Adj a b := (compl_adj C _ _).mpr ⟨hn, Aind a (PA a ha) b (PA b hb)⟩
    exact hbad (place hpq (eX a (AX a (PA a ha))) (eX b (AX b (PA b hb)))
      (Pblue a ha).1 (Pblue b hb).2)
  have redEdge (a : Fin m) (ha : a ∈ X) (b : Fin m) (hb : b ∈ X) (hab : C.Adj a b) :
      (a ∈ P ∧ b ∈ B) ∨ (b ∈ P ∧ a ∈ B) := by
    rcases partition a ha with ha' | ha'
    · rcases partition b hb with hb' | hb'
      · exact (Aind a ha' b hb' hab).elim
      · exact Or.inl ⟨Finset.mem_filter.mpr ⟨ha', b, hb', hab⟩, hb'⟩
    · rcases partition b hb with hb' | hb'
      · exact Or.inr ⟨Finset.mem_filter.mpr ⟨hb', a, ha', hab.symm⟩, ha'⟩
      · exact (Bind a ha' b hb' hab).elim
  by_cases hex : P.Nonempty
  swap
  · exact hbad (embed_in_blue_clique G C X hX (fun a ha b hb h =>
      (redEdge a ha b hb h).elim (fun hh => hex ⟨a, hh.1⟩) (fun hh => hex ⟨b, hh.1⟩)))
  obtain ⟨a, ha⟩ := hex
  have haX := AX a (PA a ha)
  by_cases hb : 1 < B.card
  · obtain ⟨b, hbB, c, hcB, hbc⟩ := Finset.one_lt_card.mp hb
    have inErase (t : Fin m) (ht : t ∈ B) : t ∈ X.erase a :=
      Finset.mem_erase.mpr ⟨fun eq => ((compl_adj C _ _).mp (Bblue t ht)).2
        (eq ▸ Ared a (PA a ha)), BX t ht⟩
    have hsz : l - 1 ≤ (X.erase a).card := by
      rw [Finset.card_erase_of_mem haX]
      omega
    refine hbad (embed_blue_clique_with_apex G C (X.erase a) hsz
      (G.ne_of_adj hxy.symm) (G.ne_of_adj hxu.symm) huy.symm hx ?_
      (inErase b hbB) (inErase c hcB) hbc (Bblue b hbB) (Bblue c hcB) ?_)
    · exact fun ht => outside (f Y) (Finset.mem_of_mem_erase ht) Y rfl
    · intro p hp q hq hpq
      rcases redEdge p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq) hpq with h | h
      · exact (Finset.mem_erase.mp hp).1 (uniqueP p h.1 a ha)
      · exact (Finset.mem_erase.mp hq).1 (uniqueP q h.1 a ha)
  obtain ⟨b, hbB, hab⟩ := (Finset.mem_filter.mp ha).2
  have uniqueB (t : Fin m) (ht : t ∈ B) : t = b :=
    Finset.card_le_one.mp (Nat.le_of_not_gt hb) t ht b hbB
  have hxdeg : (G.neighborSet x).ncard = 2 := by
    have he : G.neighborSet x = {y, u} := by
      ext t
      change G.Adj x t ↔ t ∈ ({y, u} : Set (Fin l))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨hx t, fun h => h.elim (fun e => e.symm ▸ hxy) (fun e => e.symm ▸ hxu)⟩
    exact Set.ncard_eq_two.mpr ⟨y, u, huy.symm, he⟩
  let S := insert x (G.neighborFinset x)
  have hS : S.card < (Finset.univ : Finset (Fin l)).card := by
    have hd : (G.neighborFinset x).card = 2 := by
      rw [← Set.ncard_coe_finset, coe_neighborFinset, hxdeg]
    have hh : S.card ≤ (G.neighborFinset x).card + 1 := Finset.card_insert_le _ _
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hS
  have htx : x ≠ t := fun e => ht (e ▸ Finset.mem_insert_self _ _)
  have htn : ¬ G.Adj x t := fun h => ht (Finset.mem_insert_of_mem ((mem_neighborFinset G x t).mpr h))
  refine hbad (embed_in_near_blue_clique G C X hX htx htn haX (BX b hbB)
    (C.ne_of_adj hab) ?_)
  intro p hp q hq hpq
  rcases redEdge p hp q hq hpq with h | h
  · exact Or.inl ⟨uniqueP p h.1 a ha, uniqueB q h.2⟩
  · exact Or.inr ⟨uniqueB p h.2, uniqueP q h.1 a ha⟩

theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_befrs_lower_R1_H1_R1.H2 := by
  intro l m G C hl hm hconn hC hex
  classical
  obtain ⟨x, y, hxy, hx, hy⟩ := hex
  obtain ⟨u, huy, hxu, hxN⟩ := adjacent_degree_two_other G hxy hx
  obtain ⟨v, hvx, hyv, hyN⟩ := adjacent_degree_two_other G hxy.symm hy
  let W := (Finset.univ : Finset (Fin l)).erase x
  have hmem (a : Fin l) (ha : a ≠ x) : a ∈ W := Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩
  let Y : ↥W := ⟨y, hmem y (G.ne_of_adj hxy.symm)⟩
  let U : ↥W := ⟨u, hmem u (G.ne_of_adj hxu.symm)⟩
  let V : ↥W := ⟨v, hmem v hvx⟩
  let J := G.induce (↑W : Set (Fin l)) ⊔ fromEdgeSet {s(Y, U)}
  obtain ⟨hJ, hJedge⟩ := pathContractionGraph G x y u hconn hxy hxu huy.symm hxN
    W rfl Y U rfl rfl J rfl
  have hcard : Fintype.card ↥W = l - 1 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let H := J.comap e
  let i : H ≃g J := { toEquiv := e, map_rel_iff' := Iff.rfl }
  refine ⟨H, i.connected_iff.mpr hJ, ?_, ?_⟩
  · have he : H.edgeSet.ncard = J.edgeSet.ncard := by
      rw [← coe_edgeFinset, ← coe_edgeFinset (G := J), Set.ncard_coe_finset, Set.ncard_coe_finset]
      exact i.card_edgeFinset_eq
    omega
  · intro hcopy
    exact shorten_keeps_blue_copy G C hl hm hC hxy hxu hyv huy hvx hxN hyN
      W rfl Y U V rfl rfl rfl J rfl (IsContained.trans ⟨i.symm.toCopy⟩ hcopy)
