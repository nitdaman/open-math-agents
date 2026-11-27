import FormalConjectures.ErdosProblems.«761»

-- Problem: Erdős Problem 761 — parts ii imp i
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/761.lean:96 (declaration Erdos761.erdos_761.variants.parts_ii_imp_i)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Write `χ`, `ζ`, `δ` for the chromatic, cochromatic and dichromatic numbers. Assume that every
finite graph with `ζ ≥ m` has a subgraph with `δ ≥ k`. We show that every finite graph `G` with
`χ(G) ≥ m ^ 3` has `δ(G) ≥ k`. The cubic bound replaces the sharper bound of problem 760, which
is not needed for the implication.

* `δ` is monotone: if `G'` embeds in `G` by an injective homomorphism then `δ(G') ≤ δ(G)`. Extend
  an orientation of `G'` to one of `G`, orienting the remaining edges along a well-order; a good
  colouring of `G` restricts to a good colouring of `G'`.
* If `ζ(G) ≥ m`, apply the hypothesis to `G` and use monotonicity.
* Otherwise `G` has a cocolouring with `n < m` colours. If `G` had no clique on `m * m` vertices,
  each clique class would have fewer than `m * m` vertices, so giving the vertices of every clique
  class distinct colours would colour `G` properly with `n * (m * m) < m ^ 3` colours.
* Hence `G` contains a clique on `m * m` vertices. Inside it take `m` disjoint cliques of size
  `m`. A colour class of a cocolouring of this graph meets at most `m` of its `m * m` vertices
  (one per block, or all in one block), so `ζ ≥ m`. Apply the hypothesis and monotonicity.
-/

/-- Dicolourability passes from a graph to any graph embedded in it by an injective
homomorphism. -/
theorem OMA.e761_dicolorable_of_injective {V W : Type*} (G : SimpleGraph V) (G' : SimpleGraph W)
    (f : W → V) (hf : Function.Injective f) (hadj : ∀ u v, G'.Adj u v → G.Adj (f u) (f v))
    (k : ℕ) (h : Erdos761.Dicolorable G k) : Erdos761.Dicolorable G' k := by
  intro D' hD'
  have hD : (Digraph.mk fun a b : V => (∃ u v, f u = a ∧ f v = b ∧ D'.Adj u v) ∨
      (G.Adj a b ∧ (¬ ∃ u v, f u = a ∧ f v = b ∧ G'.Adj u v) ∧
        WellOrderingRel a b)).IsOrientation G := by
    unfold Digraph.IsOrientation
    refine ⟨?_, ?_⟩
    · rintro a b (⟨u, v, rfl, rfl, huv⟩ | ⟨hab, -, -⟩)
      · exact hadj u v (hD'.1 u v huv)
      · exact hab
    · intro a b hab
      by_cases himg : ∃ u v, f u = a ∧ f v = b ∧ G'.Adj u v
      · obtain ⟨u, v, rfl, rfl, huv⟩ := himg
        constructor
        · rintro (⟨u', v', hu', hv', h⟩ | ⟨-, hn, -⟩)
          · have eu : u' = u := hf hu'
            have ev : v' = v := hf hv'
            rw [eu, ev] at h
            rintro (⟨u'', v'', hu'', hv'', h'⟩ | ⟨-, hn', -⟩)
            · have eu' : u'' = v := hf hu''
              have ev' : v'' = u := hf hv''
              rw [eu', ev'] at h'
              exact ((hD'.2 u v huv).mp h) h'
            · exact hn' ⟨v, u, rfl, rfl, huv.symm⟩
          · exact absurd ⟨u, v, rfl, rfl, huv⟩ hn
        · intro hn
          by_contra hcon
          have h1 : ¬ D'.Adj u v := fun h => hcon (Or.inl ⟨u, v, rfl, rfl, h⟩)
          have h2 : D'.Adj v u := by
            by_contra h3
            exact h1 ((hD'.2 u v huv).mpr h3)
          exact hn (Or.inl ⟨v, u, rfl, rfl, h2⟩)
      · have himg' : ¬ ∃ u v, f u = b ∧ f v = a ∧ G'.Adj u v :=
          fun ⟨u, v, hu, hv, h⟩ => himg ⟨v, u, hv, hu, h.symm⟩
        have hne : a ≠ b := G.ne_of_adj hab
        constructor
        · rintro (⟨u, v, hu, hv, h⟩ | ⟨-, -, hr⟩)
          · exact absurd ⟨u, v, hu, hv, hD'.1 u v h⟩ himg
          · rintro (⟨u, v, hu, hv, h⟩ | ⟨-, -, hr'⟩)
            · exact himg' ⟨u, v, hu, hv, hD'.1 u v h⟩
            · exact asymm_of WellOrderingRel hr hr'
        · intro hn
          rcases trichotomous_of WellOrderingRel a b with hr | hr | hr
          · exact Or.inr ⟨hab, himg, hr⟩
          · exact absurd hr hne
          · exact absurd (Or.inr ⟨hab.symm, himg', hr⟩) hn
  obtain ⟨c, hc⟩ := h _ hD
  refine ⟨fun w => c (f w), ?_⟩
  intro i v hcyc
  refine hc i (f v) (Relation.TransGen.lift f ?_ v v hcyc)
  intro a b hab
  exact ⟨hab.1, hab.2.1, Or.inl ⟨a, b, rfl, rfl, hab.2.2⟩⟩

/-- A cocolouring with `n` colours of a graph with no clique on `N` vertices yields a proper
colouring with `n * N` colours. -/
theorem OMA.e761_colorable_of_cocolorable {V : Type*} (G : SimpleGraph V) (n N : ℕ) (hN : 0 < N)
    (hco : G.Cocolorable n) (hfree : G.CliqueFree N) : G.Colorable (n * N) := by
  classical
  obtain ⟨c, hc⟩ := hco
  have hex : ∀ i : Fin n, ∃ e : V → Fin N, ∀ v w, G.induce {x | c x = i} = ⊤ →
      c v = i → c w = i → e v = e w → v = w := by
    intro i
    by_cases htop : G.induce {x | c x = i} = ⊤
    · rcases Function.Embedding.total (↥{x | c x = i}) (Fin N) with ⟨⟨emb⟩⟩ | ⟨⟨emb⟩⟩
      · refine ⟨fun v => if hv : c v = i then emb ⟨v, Set.mem_ofPred.mpr hv⟩ else ⟨0, hN⟩,
          fun v w _ hv hw h => ?_⟩
        simp only [dif_pos hv, dif_pos hw] at h
        exact congrArg Subtype.val (emb.injective h)
      · exfalso
        refine (SimpleGraph.cliqueFree_iff.mp hfree).false ⟨⟨fun a => (emb a).1, ?_⟩, ?_⟩
        · intro a b hab
          have hne : emb a ≠ emb b :=
            fun h => (SimpleGraph.top_adj a b).mp hab (emb.injective h)
          have h3 : (G.induce {x | c x = i}).Adj (emb a) (emb b) := by
            rw [htop]
            exact (SimpleGraph.top_adj _ _).mpr hne
          exact h3
        · intro a b hab
          exact emb.injective (Subtype.ext hab)
    · exact ⟨fun _ => ⟨0, hN⟩, fun _ _ h => absurd h htop⟩
  choose e he using hex
  have hcol : G.Colorable (Fintype.card (Fin n × Fin N)) := by
    refine (SimpleGraph.Coloring.mk (fun v => (c v, e (c v) v)) ?_).colorable
    intro v w hadj heq
    have h1 : c v = c w := congrArg Prod.fst heq
    have h2 : e (c v) v = e (c w) w := congrArg Prod.snd heq
    rw [← h1] at h2
    have htop : G.induce {x | c x = c v} = ⊤ := by
      rcases hc (c v) with hbot | htop
      · exfalso
        have h3 : (G.induce {x | c x = c v}).Adj ⟨v, Set.mem_ofPred.mpr rfl⟩
            ⟨w, Set.mem_ofPred.mpr h1.symm⟩ := hadj
        rw [hbot] at h3
        exact h3
      · exact htop
    exact G.ne_of_adj hadj (he (c v) v w htop rfl h1.symm h2)
  simpa using hcol

/-- The graph made of `m` disjoint cliques of size `m` has cochromatic number at least `m`. -/
theorem OMA.e761_block_graph {V : Type*} (m : ℕ) (hm : 0 < m) (φ : Fin (m * m) → V)
    (hφ : Function.Injective φ) (G₁ : SimpleGraph V)
    (hG₁ : ∀ x y, G₁.Adj x y ↔
      ∃ a b : Fin (m * m), φ a = x ∧ φ b = y ∧ a ≠ b ∧ a.val / m = b.val / m)
    (n : ℕ) (hco : G₁.Cocolorable n) : m ≤ n := by
  classical
  obtain ⟨c, hc⟩ := hco
  have hdiv : ∀ a : Fin (m * m), a.val / m < m := fun a => Nat.div_lt_of_lt_mul a.isLt
  have hmod : ∀ a : Fin (m * m), a.val % m < m := fun a => Nat.mod_lt _ hm
  have hinj : Function.Injective (fun a : Fin (m * m) =>
      ((c (φ a), if G₁.induce {v | c v = c (φ a)} = ⊥ then (⟨a.val / m, hdiv a⟩ : Fin m)
        else ⟨a.val % m, hmod a⟩) : Fin n × Fin m)) := by
    intro a b hab
    have h1 : c (φ a) = c (φ b) := congrArg Prod.fst hab
    have h2 := congrArg Prod.snd hab
    simp only at h2
    rw [← h1] at h2
    by_contra hne
    by_cases hbot : G₁.induce {v | c v = c (φ a)} = ⊥
    · rw [if_pos hbot, if_pos hbot] at h2
      have hd : a.val / m = b.val / m := congrArg Fin.val h2
      have hadj : G₁.Adj (φ a) (φ b) := (hG₁ _ _).mpr ⟨a, b, rfl, rfl, hne, hd⟩
      have h3 : (G₁.induce {v | c v = c (φ a)}).Adj ⟨φ a, Set.mem_ofPred.mpr rfl⟩
          ⟨φ b, Set.mem_ofPred.mpr h1.symm⟩ := hadj
      rw [hbot] at h3
      exact h3
    · rw [if_neg hbot, if_neg hbot] at h2
      have hmd : a.val % m = b.val % m := congrArg Fin.val h2
      have htop : G₁.induce {v | c v = c (φ a)} = ⊤ := (hc _).resolve_left hbot
      have h3 : (G₁.induce {v | c v = c (φ a)}).Adj ⟨φ a, Set.mem_ofPred.mpr rfl⟩
          ⟨φ b, Set.mem_ofPred.mpr h1.symm⟩ := by
        rw [htop]
        exact (SimpleGraph.top_adj _ _).mpr (fun h => hne (hφ (congrArg Subtype.val h)))
      have h4 : G₁.Adj (φ a) (φ b) := h3
      obtain ⟨a', b', ha', hb', -, hd⟩ := (hG₁ _ _).mp h4
      have ea : a' = a := hφ ha'
      have eb : b' = b := hφ hb'
      rw [ea, eb] at hd
      have hval : a.val = b.val := by
        rw [← Nat.div_add_mod a.val m, ← Nat.div_add_mod b.val m, hd, hmd]
      exact hne (Fin.ext hval)
  have hcard := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, Fintype.card_prod] at hcard
  exact Nat.le_of_mul_le_mul_right hcard hm

theorem OMA.solution : type_of% @Erdos761.erdos_761.variants.parts_ii_imp_i := by
  intro hii k
  obtain ⟨m, hm⟩ := hii k
  refine ⟨m * (m * m), ?_⟩
  intro V _ G hχ
  classical
  have mono : ∀ (G₁ : SimpleGraph V), (∀ x y, G₁.Adj x y → G.Adj x y) → ∀ H : G₁.Subgraph,
      Erdos761.dichromaticNumber H.coe ≤ Erdos761.dichromaticNumber G := by
    intro G₁ hle H
    unfold Erdos761.dichromaticNumber
    refine le_iInf₂ fun j hj => iInf₂_le j ?_
    exact OMA.e761_dicolorable_of_injective G H.coe Subtype.val Subtype.val_injective
      (fun u v huv => hle _ _ (H.coe_adj_sub u v huv)) j hj
  by_cases hζ : (m : ℕ∞) ≤ G.cochromaticNumber
  · obtain ⟨H, hH⟩ := hm V G hζ
    exact le_trans hH (mono G (fun _ _ h => h) H)
  · have hex : ∃ n : ℕ, G.Cocolorable n ∧ n < m := by
      by_contra hcon
      apply hζ
      unfold SimpleGraph.cochromaticNumber
      refine le_iInf₂ fun n hn => ?_
      have hnm : m ≤ n := not_lt.mp fun h => hcon ⟨n, hn, h⟩
      exact_mod_cast hnm
    obtain ⟨n, hn, hnm⟩ := hex
    have hmpos : 0 < m := by omega
    have hmm : 0 < m * m := Nat.mul_pos hmpos hmpos
    have hnotfree : ¬ G.CliqueFree (m * m) := by
      intro hfree
      have hcol := OMA.e761_colorable_of_cocolorable G n (m * m) hmm hn hfree
      have h1 : G.chromaticNumber ≤ ((n * (m * m) : ℕ) : ℕ∞) := hcol.chromaticNumber_le
      have h2 : ((m * (m * m) : ℕ) : ℕ∞) ≤ ((n * (m * m) : ℕ) : ℕ∞) := le_trans hχ h1
      have h3 : m * (m * m) ≤ n * (m * m) := by exact_mod_cast h2
      have h4 : n * (m * m) < m * (m * m) := Nat.mul_lt_mul_of_pos_right hnm hmm
      omega
    obtain ⟨φ⟩ := (SimpleGraph.not_cliqueFree_iff_top_isContained (m * m)).mp hnotfree
    obtain ⟨G₁, hG₁⟩ : ∃ G₁ : SimpleGraph V, ∀ x y, G₁.Adj x y ↔
        ∃ a b : Fin (m * m), φ a = x ∧ φ b = y ∧ a ≠ b ∧ a.val / m = b.val / m := by
      refine ⟨SimpleGraph.fromRel fun x y : V =>
        ∃ a b : Fin (m * m), φ a = x ∧ φ b = y ∧ a.val / m = b.val / m, fun x y => ?_⟩
      rw [SimpleGraph.fromRel_adj]
      constructor
      · rintro ⟨hxy, ⟨a, b, rfl, rfl, hd⟩ | ⟨a, b, rfl, rfl, hd⟩⟩
        · exact ⟨a, b, rfl, rfl, fun h => hxy (by rw [h]), hd⟩
        · exact ⟨b, a, rfl, rfl, fun h => hxy (by rw [h]), hd.symm⟩
      · rintro ⟨a, b, rfl, rfl, hab, hd⟩
        exact ⟨fun h => hab (φ.injective h), Or.inl ⟨a, b, rfl, rfl, hd⟩⟩
    have hle : ∀ x y, G₁.Adj x y → G.Adj x y := by
      intro x y h
      obtain ⟨a, b, rfl, rfl, hab, -⟩ := (hG₁ x y).mp h
      exact φ.toHom.map_adj ((SimpleGraph.top_adj a b).mpr hab)
    have hζ₁ : (m : ℕ∞) ≤ G₁.cochromaticNumber := by
      unfold SimpleGraph.cochromaticNumber
      refine le_iInf₂ fun n' hn' => ?_
      have hmn' : m ≤ n' :=
        OMA.e761_block_graph m hmpos (fun a => φ a) φ.injective G₁ hG₁ n' hn'
      exact_mod_cast hmn'
    obtain ⟨H, hH⟩ := hm V G₁ hζ₁
    exact le_trans hH (mono G₁ hle H)
