import OMAReductions.R_Erdos751_erdos_751_parts_i_R1

-- Step Erdos751.erdos_751.parts.i.R1.H1: hypothesis H1 of reduction Erdos751.erdos_751.parts.i.R1
-- Credit: @LordMike
-- H1 := every finite graph G that is not 3-colourable has a subgraph G' with more than two vertices,
-- such that deleting any vertex leaves G' connected, and every vertex of G' has at least 3 neighbours in G'.
-- Proof idea: take a vertex-minimal non-3-colourable induced subgraph S (a 4-critical one). Minimum
-- degree at least 3 and 2-connectivity follow from minimality by colour extension and colour gluing.

open SimpleGraph

open scoped Classical

namespace OMA

variable {V : Type}

/-- A finset `T` of vertices is properly 3-colourable: some colouring of `V` is proper on `T`. -/
abbrev Col3 (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∃ c : V → Fin 3, ∀ a ∈ T, ∀ b ∈ T, G.Adj a b → c a ≠ c b

lemma col3_empty (G : SimpleGraph V) : Col3 G ∅ :=
  ⟨fun _ => 0, by simp⟩

lemma colorable_of_col3 [Fintype V] (G : SimpleGraph V) (h : Col3 G Finset.univ) :
    G.Colorable 3 := by
  obtain ⟨c, hc⟩ := h
  exact Nonempty.intro (Coloring.mk c (fun {a b} hab => hc a (Finset.mem_univ _) b (Finset.mem_univ _) hab))

lemma col3_of_colorable [Fintype V] (G : SimpleGraph V) (h : G.Colorable 3) :
    Col3 G Finset.univ := by
  obtain ⟨C⟩ := h
  exact ⟨fun v => C v, fun a _ b _ hab => C.valid hab⟩

lemma deg_ge_three (G : SimpleGraph V) (S : Finset V) (hS : ¬ Col3 G S)
    (hmin : ∀ T : Finset V, T.card < S.card → Col3 G T)
    (x : V) (hx : x ∈ S) : 3 ≤ (S.filter (G.Adj x)).card := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc⟩ := hmin (S.erase x) (Finset.card_erase_lt_of_mem hx)
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, k ∉ (S.filter (G.Adj x)).image c := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (Fin 3)) ⊆ (S.filter (G.Adj x)).image c :=
      fun k _ => hcon k
    have h3 := Finset.card_le_card hsub
    have h4 := Finset.card_image_le (f := c) (s := S.filter (G.Adj x))
    rw [Finset.card_univ, Fintype.card_fin] at h3
    omega
  apply hS
  refine ⟨Function.update c x k, fun a ha b hb hab => ?_⟩
  have key : ∀ b ∈ S, G.Adj x b → c b ≠ k := by
    intro b hb hxb hcb
    exact hk (Finset.mem_image.2 ⟨b, Finset.mem_filter.2 ⟨hb, hxb⟩, hcb⟩)
  by_cases hax : a = x
  · have hxb : G.Adj x b := by rw [← hax]; exact hab
    have hbx : b ≠ x := by
      rintro rfl
      exact G.irrefl hxb
    rw [hax, Function.update_self, Function.update_of_ne hbx]
    exact (key b hb hxb).symm
  · by_cases hbx : b = x
    · have hxa : G.Adj x a := by rw [← hbx]; exact hab.symm
      rw [hbx, Function.update_self, Function.update_of_ne hax]
      exact key a ha hxa
    · rw [Function.update_of_ne hax, Function.update_of_ne hbx]
      exact hc a (Finset.mem_erase.2 ⟨hax, ha⟩) b (Finset.mem_erase.2 ⟨hbx, hb⟩) hab

lemma sep_false (G : SimpleGraph V) (S : Finset V) (hS : ¬ Col3 G S)
    (hmin : ∀ T : Finset V, T.card < S.card → Col3 G T)
    (x : V) (hx : x ∈ S) (A : Set V)
    (hA1 : ∀ a ∈ A, a ∈ S ∧ a ≠ x)
    (hA2 : ∀ a ∈ A, ∀ b ∈ S, b ≠ x → G.Adj a b → b ∈ A)
    (u : V) (hu : u ∈ A) (v : V) (hv : v ∈ S) (hvx : v ≠ x) (hvA : v ∉ A) : False := by
  obtain ⟨TA, hTA⟩ : ∃ T : Finset V, ∀ w, w ∈ T ↔ (w = x ∨ (w ∈ S ∧ w ∈ A)) :=
    ⟨insert x (S.filter (fun w => w ∈ A)), fun w => by simp⟩
  obtain ⟨TB, hTB⟩ : ∃ T : Finset V, ∀ w, w ∈ T ↔ (w = x ∨ (w ∈ S ∧ w ∉ A)) :=
    ⟨insert x (S.filter (fun w => w ∉ A)), fun w => by simp⟩
  have hxTA : x ∈ TA := (hTA x).2 (Or.inl rfl)
  have hxTB : x ∈ TB := (hTB x).2 (Or.inl rfl)
  have hTA_sub : TA ⊆ S := fun w hw => by
    rcases (hTA w).1 hw with h | h
    · rw [h]; exact hx
    · exact h.1
  have hTB_sub : TB ⊆ S := fun w hw => by
    rcases (hTB w).1 hw with h | h
    · rw [h]; exact hx
    · exact h.1
  have hvTA : v ∉ TA := fun h => by
    rcases (hTA v).1 h with h' | h'
    · exact hvx h'
    · exact hvA h'.2
  have huTB : u ∉ TB := fun h => by
    rcases (hTB u).1 h with h' | h'
    · exact (hA1 u hu).2 h'
    · exact h'.2 hu
  have hTA_lt : TA.card < S.card :=
    Finset.card_lt_card ((Finset.ssubset_iff_of_subset hTA_sub).2 ⟨v, hv, hvTA⟩)
  have hTB_lt : TB.card < S.card :=
    Finset.card_lt_card ((Finset.ssubset_iff_of_subset hTB_sub).2 ⟨u, (hA1 u hu).1, huTB⟩)
  obtain ⟨cA, hcA⟩ := hmin TA hTA_lt
  obtain ⟨cB, hcB⟩ := hmin TB hTB_lt
  have hBcover : ∀ w ∈ S, w ∉ TA → w ∈ TB := by
    intro w hw hwA
    by_cases hwx : w = x
    · exact (hTB w).2 (Or.inl hwx)
    · exact (hTB w).2 (Or.inr ⟨hw, fun hwA' => hwA ((hTA w).2 (Or.inr ⟨hw, hwA'⟩))⟩)
  apply hS
  refine ⟨fun w => if w ∈ TA then cA w else Equiv.swap (cB x) (cA x) (cB w), fun a ha b hb hab => ?_⟩
  dsimp only
  by_cases h1 : a ∈ TA <;> by_cases h2 : b ∈ TA
  · rw [if_pos h1, if_pos h2]
    exact hcA a h1 b h2 hab
  · have hbx : b ≠ x := fun h => h2 (by rw [h]; exact hxTA)
    have hax : a = x := by
      by_contra hax
      rcases (hTA a).1 h1 with h | ⟨_, haA⟩
      · exact hax h
      · exact h2 ((hTA b).2 (Or.inr ⟨hb, hA2 a haA b hb hbx hab⟩))
    have hxb : G.Adj x b := by rw [← hax]; exact hab
    have hbTB : b ∈ TB := hBcover b hb h2
    rw [if_pos h1, if_neg h2, hax]
    intro heq
    apply hcB x hxTB b hbTB hxb
    exact (Equiv.swap (cB x) (cA x)).injective ((Equiv.swap_apply_left _ _).trans heq)
  · have hax : a ≠ x := fun h => h1 (by rw [h]; exact hxTA)
    have hbx : b = x := by
      by_contra hbx
      rcases (hTA b).1 h2 with h | ⟨_, hbA⟩
      · exact hbx h
      · exact h1 ((hTA a).2 (Or.inr ⟨ha, hA2 b hbA a ha hax hab.symm⟩))
    have hxa : G.Adj x a := by rw [← hbx]; exact hab.symm
    have haTB : a ∈ TB := hBcover a ha h1
    rw [if_neg h1, if_pos h2, hbx]
    intro heq
    apply hcB x hxTB a haTB hxa
    exact (Equiv.swap (cB x) (cA x)).injective ((Equiv.swap_apply_left _ _).trans heq.symm)
  · rw [if_neg h1, if_neg h2]
    intro heq
    exact hcB a (hBcover a ha h1) b (hBcover b hb h2) hab (Equiv.injective _ heq)

/-- The subgraph of `G` on the finset `S`: all edges of `G` between vertices of `S`. -/
def subS (G : SimpleGraph V) (S : Finset V) : G.Subgraph where
  verts := (S : Set V)
  Adj a b := G.Adj a b ∧ a ∈ S ∧ b ∈ S
  adj_sub h := h.1
  edge_vert h := Finset.mem_coe.2 h.2.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩

lemma subS_adj (G : SimpleGraph V) (S : Finset V) (a b : (subS G S).verts) :
    (subS G S).coe.Adj a b ↔ G.Adj a.1 b.1 ∧ a.1 ∈ S ∧ b.1 ∈ S := Iff.rfl

lemma nbr_card (G : SimpleGraph V) (S : Finset V) (x : (subS G S).verts) :
    Nat.card ((subS G S).coe.neighborSet x) = (S.filter (G.Adj x.1)).card := by
  have h1 : Subtype.val '' ((subS G S).coe.neighborSet x) =
      ((S.filter (G.Adj x.1) : Finset V) : Set V) := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hadj, _, hyS⟩ := (subS_adj G S x y).1 ((SimpleGraph.mem_neighborSet _ _ _).1 hy)
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hyS, hadj⟩)
    · intro hw
      obtain ⟨hwS, hwadj⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hw)
      refine ⟨⟨w, Finset.mem_coe.2 hwS⟩, ?_, rfl⟩
      exact (SimpleGraph.mem_neighborSet _ _ _).2
        ((subS_adj G S x _).2 ⟨hwadj, Finset.mem_coe.1 x.2, hwS⟩)
  rw [Nat.card_coe_set_eq, ← Set.ncard_image_of_injective _ Subtype.val_injective, h1,
    Set.ncard_coe_finset]

lemma conn_induce (G : SimpleGraph V) (S : Finset V) (hS : ¬ Col3 G S)
    (hmin : ∀ T : Finset V, T.card < S.card → Col3 G T) (x : (subS G S).verts) :
    ((subS G S).coe.induce {x}ᶜ).Connected := by
  have hxS : x.1 ∈ S := Finset.mem_coe.1 x.2
  have hdeg := deg_ge_three G S hS hmin x.1 hxS
  obtain ⟨y, hy⟩ : (S.filter (G.Adj x.1)).Nonempty := Finset.card_pos.1 (by omega)
  have hyS : y ∈ S := (Finset.mem_filter.1 hy).1
  have hxy : G.Adj x.1 y := (Finset.mem_filter.1 hy).2
  have hyx : (⟨y, Finset.mem_coe.2 hyS⟩ : (subS G S).verts) ≠ x := by
    intro h
    subst h
    exact G.irrefl hxy
  haveI : Nonempty ↥({x}ᶜ : Set (subS G S).verts) := ⟨⟨⟨y, Finset.mem_coe.2 hyS⟩, hyx⟩⟩
  rw [SimpleGraph.connected_iff]
  refine ⟨fun p q => ?_, inferInstance⟩
  by_contra hne
  obtain ⟨A, hA⟩ : ∃ A : Set V, ∀ w, w ∈ A ↔ ∃ r : ↥({x}ᶜ : Set (subS G S).verts),
      r.1.1 = w ∧ ((subS G S).coe.induce {x}ᶜ).Reachable p r :=
    ⟨{w | ∃ r : ↥({x}ᶜ : Set (subS G S).verts), r.1.1 = w ∧
      ((subS G S).coe.induce {x}ᶜ).Reachable p r}, fun w => Iff.rfl⟩
  refine sep_false G S hS hmin x.1 hxS A ?_ ?_ p.1.1 ((hA p.1.1).2 ⟨p, rfl, SimpleGraph.Reachable.refl p⟩)
    q.1.1 (Finset.mem_coe.1 q.1.2) ?_ ?_
  · intro a ha
    obtain ⟨r, rfl, _⟩ := (hA _).1 ha
    exact ⟨Finset.mem_coe.1 r.1.2, fun h => r.2 (Set.mem_singleton_iff.2 (Subtype.ext h))⟩
  · intro a ha b hb hbx hab
    obtain ⟨r, hr, hreach⟩ := (hA a).1 ha
    let s : ↥({x}ᶜ : Set (subS G S).verts) :=
      ⟨⟨b, Finset.mem_coe.2 hb⟩, fun h => hbx (congrArg Subtype.val (Set.mem_singleton_iff.1 h))⟩
    have hadj : ((subS G S).coe.induce {x}ᶜ).Adj r s := by
      show (subS G S).coe.Adj r.1 s.1
      rw [subS_adj]
      exact ⟨by rw [hr]; exact hab, Finset.mem_coe.1 r.1.2, hb⟩
    have hpq : ((subS G S).coe.induce {x}ᶜ).Reachable p s := hreach.trans hadj.reachable
    exact (hA b).2 ⟨s, rfl, hpq⟩
  · exact fun h => q.2 (Set.mem_singleton_iff.2 (Subtype.ext h))
  · intro h
    obtain ⟨r, hr, hreach⟩ := (hA _).1 h
    have hrq : r = q := Subtype.ext (Subtype.ext hr)
    rw [hrq] at hreach
    exact hne hreach

end OMA

open OMA

theorem OMA.solution : OMA.R_Erdos751_erdos_751_parts_i_R1.H1 := by
  unfold OMA.R_Erdos751_erdos_751_parts_i_R1.H1
  intro W hfin G hG
  haveI : Fintype W := Fintype.ofFinite W
  have hex : ∃ n : ℕ, ∃ S : Finset W, S.card = n ∧ ¬ Col3 G S :=
    ⟨Finset.univ.card, Finset.univ, rfl, fun h => hG (colorable_of_col3 G h)⟩
  obtain ⟨S, hSn, hS⟩ := Nat.find_spec hex
  have hmin : ∀ T : Finset W, T.card < S.card → Col3 G T := by
    intro T hT
    by_contra hC
    exact Nat.find_min hex (by rw [← hSn]; exact hT) ⟨T, rfl, hC⟩
  have hne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · exact (hS (by rw [h]; exact col3_empty G)).elim
    · exact h
  obtain ⟨x0, hx0⟩ := hne
  have hS2 : 2 < S.card := by
    have h3 := deg_ge_three G S hS hmin x0 hx0
    have hsub : S.filter (G.Adj x0) ⊂ S :=
      (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2
        ⟨x0, hx0, fun h => G.irrefl (Finset.mem_filter.1 h).2⟩
    have := Finset.card_lt_card hsub
    omega
  refine ⟨subS G S, ?_, fun x => conn_induce G S hS hmin x, fun x => ?_⟩
  · show 2 < Nat.card (↑S : Set W)
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact hS2
  · rw [nbr_card]
    exact deg_ge_three G S hS hmin x.1 (Finset.mem_coe.1 x.2)
