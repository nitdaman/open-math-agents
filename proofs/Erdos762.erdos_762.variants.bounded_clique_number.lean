import FormalConjectures.ErdosProblems.«762»

/-! A bounded collection of clique classes suffices in any minimum cocoloring. -/

open SimpleGraph

namespace Erdos762Aux

private def threshold (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => k * threshold k m + 1

/-- Select successively from a largest remaining color class. -/
private lemma stableSequence {A C : Type*} [Fintype C] (label : A → A → C)
    (m : ℕ) (S : Finset A) (hS : threshold (Fintype.card C) m < S.card) :
    ∃ a : Fin m ↪ A, (∀ i, a i ∈ S) ∧ ∃ c : Fin m → C,
      ∀ i j, i < j → label (a i) (a j) = c i := by
  classical
  induction m generalizing S with
  | zero =>
    exact ⟨⟨Fin.elim0, fun i => i.elim0⟩, fun i => i.elim0, Fin.elim0, fun i => i.elim0⟩
  | succ m ih =>
    have hpos : 0 < S.card := Nat.zero_le _ |>.trans_lt hS
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    have hc : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hx
    rw [threshold] at hS
    obtain ⟨d, _, hd⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := S.erase x) (t := Finset.univ) (f := label x)
      (n := threshold (Fintype.card C) m) (fun _ _ => Finset.mem_univ _)
      (by rw [Finset.card_univ, hc]; omega)
    obtain ⟨a, ha, c, hlabel⟩ := ih _ hd
    have hmem (i : Fin m) := Finset.mem_filter.mp (ha i)
    have hnew : x ∉ Set.range a := by
      rintro ⟨i, hi⟩
      exact (Finset.mem_erase.mp (hmem i).1).1 hi
    refine ⟨⟨Fin.cons x a, Fin.cons_injective_iff.mpr ⟨hnew, a.injective⟩⟩, ?_,
      Fin.cons d c, ?_⟩
    · intro i
      refine Fin.cases hx (fun j => ?_) i
      exact Finset.mem_of_mem_erase (hmem j).1
    · intro i j hij
      refine Fin.cases ?_ (fun i => ?_) i hij
      · refine Fin.cases (by simp) (fun j _ => ?_) j
        exact (hmem j).2
      · refine Fin.cases (by simp) (fun j hij => ?_) j
        exact hlabel i j (Fin.succ_lt_succ_iff.mp hij)

private lemma homogeneous {A C : Type*} [Fintype A] [Fintype C] (label : A → A → C)
    (n : ℕ) (hA : threshold (Fintype.card C) (Fintype.card C * n + 1) < Fintype.card A) :
    ∃ a : Fin n ↪ A, ∃ d : C, ∀ i j, i < j → label (a i) (a j) = d := by
  classical
  let m := Fintype.card C * n + 1
  obtain ⟨a, _, c, hc⟩ := stableSequence label m Finset.univ (by simpa [m] using hA)
  obtain ⟨d, _, hd⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := c) (n := n)
    (fun _ _ => Finset.mem_univ _) (by simp [m])
  obtain ⟨J, hJ, hcard⟩ := Finset.exists_subset_card_eq hd.le
  let e := J.orderEmbOfFin hcard
  refine ⟨e.toEmbedding.trans a, d, fun i j hij => ?_⟩
  have hi := Finset.mem_filter.mp (hJ (J.orderEmbOfFin_mem hcard i))
  exact (hc (e i) (e j) (e.strictMono hij)).trans hi.2

private def IndependentClass {V C : Type*} (G : SimpleGraph V) (color : V → C) (i : C) :=
  ∀ x y, color x = i → color y = i → ¬ G.Adj x y

private def CompleteClass {V C : Type*} (G : SimpleGraph V) (color : V → C) (i : C) :=
  ∀ x y, color x = i → color y = i → x ≠ y → G.Adj x y

private lemma cocolorable_iff_classes {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    G.Cocolorable k ↔ ∃ color : V → Fin k,
      ∀ i, IndependentClass G color i ∨ CompleteClass G color i := by
  unfold SimpleGraph.Cocolorable
  apply exists_congr
  intro color
  apply forall_congr'
  intro i
  apply or_congr
  · rw [SimpleGraph.eq_bot_iff_forall_not_adj]
    constructor
    · intro h x y hx hy
      exact h ⟨x, hx⟩ ⟨y, hy⟩
    · rintro h ⟨x, hx⟩ ⟨y, hy⟩
      exact h x y hx hy
  · constructor
    · intro h x y hx hy hxy
      have ht : (⊤ : SimpleGraph {v | color v = i}).Adj ⟨x, hx⟩ ⟨y, hy⟩ :=
        fun h => hxy (congrArg Subtype.val h)
      rw [← h] at ht
      exact ht
    · intro h
      apply top_unique
      rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      exact h x y hx hy (fun e => hxy (Subtype.ext e))

private lemma cocolorable_of_classes {V C : Type*} [Fintype C] {G : SimpleGraph V}
    (color : V → C) (h : ∀ i, IndependentClass G color i ∨ CompleteClass G color i) :
    G.Cocolorable (Fintype.card C) := by
  let e := Fintype.equivFin C
  refine (cocolorable_iff_classes G _).mpr ⟨e ∘ color, fun i => ?_⟩
  rcases h (e.symm i) with hi | hi
  · exact Or.inl fun x y hx hy =>
      hi x y (e.injective (hx.trans (e.apply_symm_apply i).symm))
        (e.injective (hy.trans (e.apply_symm_apply i).symm))
  · exact Or.inr fun x y hx hy =>
      hi x y (e.injective (hx.trans (e.apply_symm_apply i).symm))
        (e.injective (hy.trans (e.apply_symm_apply i).symm))

private lemma no_clique_embedding {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (hf : G.CliqueFree n) (e : Fin n ↪ V) (he : ∀ i j, i ≠ j → G.Adj (e i) (e j)) :
    False := by
  classical
  apply hf (Finset.univ.map e)
  rw [isNClique_iff]
  refine ⟨?_, by simp⟩
  intro x hx y hy hxy
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hy
  exact he i j (fun h => hxy (congrArg e h))

private lemma completeClass_small {V C : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (hf : G.CliqueFree n) {color : V → C} {i : C}
    [Fintype {v // color v = i}] (hi : CompleteClass G color i) :
    Fintype.card {v // color v = i} ≤ n - 1 := by
  by_contra! h
  have hcard : Fintype.card (Fin n) ≤ Fintype.card {v // color v = i} := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact no_clique_embedding hf (e.trans ⟨Subtype.val, Subtype.val_injective⟩)
    (fun a b hab => hi _ _ (e a).property (e b).property
      (fun eq => hab (e.injective (Subtype.ext eq))))

end Erdos762Aux

namespace Erdos762Aux

private lemma optimal_coloring {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ k : ℕ, G.Cocolorable k ∧ G.cochromaticNumber = k ∧
      ∀ t : ℕ, G.Cocolorable t → k ≤ t := by
  classical
  have hex : ∃ k, G.Cocolorable k := by
    obtain ⟨c, hc⟩ := (colorable_iff_induce_eq_bot G _).mp G.colorable_of_fintype
    exact ⟨_, c, fun i => Or.inl (hc i)⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, fun t ht => Nat.find_min' hex ht⟩
  apply le_antisymm
  · exact iInf₂_le (Nat.find hex) (Nat.find_spec hex)
  · apply le_iInf₂
    intro t ht
    exact_mod_cast (Nat.find_min' hex ht)

private lemma chromatic_le_card_of_coloring {V C : Type*} [Fintype C] {G : SimpleGraph V}
    (c : V → C) (hc : ∀ a b, G.Adj a b → c a ≠ c b) :
    G.chromaticNumber ≤ Fintype.card C := by
  let e := Fintype.equivFin C
  exact chromaticNumber_le_iff_colorable.mpr
    ⟨⟨e ∘ c, fun h he => hc _ _ h (e.injective he)⟩⟩

end Erdos762Aux

open Erdos762Aux

theorem OMA.solution : type_of% @Erdos762.erdos_762.variants.bounded_clique_number := by
  classical
  intro n hn
  let R := threshold (Fintype.card (Option (Fin (n - 1))))
    (Fintype.card (Option (Fin (n - 1))) * n + 1)
  refine ⟨R * (n - 1), ?_⟩
  intro V _ G hf
  obtain ⟨k, hk, hnum, hmin⟩ := optimal_coloring G
  obtain ⟨c, hc⟩ := (cocolorable_iff_classes G k).mp hk
  let Bad := {i : Fin k // ¬IndependentClass G c i}
  let _ : Fintype Bad := inferInstanceAs (Fintype {i : Fin k // ¬IndependentClass G c i})
  have hComplete (i : Bad) : CompleteClass G c i.val := (hc i.val).resolve_left i.property
  have hEmb (i : Bad) : Nonempty ({v // c v = i.val} ↪ Fin (n - 1)) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin]
    exact completeClass_small hf (hComplete i)
  let index (i : Bad) : {v // c v = i.val} ↪ Fin (n - 1) := Classical.choice (hEmb i)
  let slot (v : V) : Fin (n - 1) :=
    if h : ¬IndependentClass G c (c v) then index ⟨c v, h⟩ ⟨v, rfl⟩ else ⟨0, by omega⟩
  have slot_injective {x y : V} (h : c x = c y) (hb : ¬IndependentClass G c (c x))
      (hs : slot x = slot y) : x = y := by
    have hslot (v : V) (i : Bad) (hv : c v = i.val) : slot v = index i ⟨v, hv⟩ := by
      rcases i with ⟨i, hi⟩
      dsimp at hv
      subst i
      simp [slot, hi]
    let i : Bad := ⟨c x, hb⟩
    have he : index i ⟨x, rfl⟩ = index i ⟨y, h.symm⟩ :=
      (hslot x i rfl).symm.trans (hs.trans (hslot y i h.symm))
    exact congrArg Subtype.val ((index i).injective he)
  -- A conflict is an edge whose endpoints have the same index in their respective classes.
  let Conflict (i j : Bad) (d : Fin (n - 1)) :=
    ∃ x y, c x = i.val ∧ c y = j.val ∧ slot x = d ∧ slot y = d ∧ G.Adj x y
  let label (i j : Bad) : Option (Fin (n - 1)) :=
    if h : ∃ d, Conflict i j d then some (Classical.choose h) else none
  have conflict_of_some {i j : Bad} {d : Fin (n - 1)}
      (h : label i j = some d) : Conflict i j d := by
    unfold label at h
    split at h
    · rename_i hex
      exact (Option.some.inj h) ▸ Classical.choose_spec hex
    · contradiction
  have no_conflict_of_none {i j : Bad} (h : label i j = none) (d : Fin (n - 1)) :
      ¬Conflict i j d := by
    intro hd
    simp [label, show ∃ d, Conflict i j d from ⟨d, hd⟩] at h
  have hBad : Fintype.card Bad ≤ R := by
    by_contra! hlarge
    obtain ⟨sel, d, hsel⟩ := homogeneous label n hlarge
    cases d with
    | some d =>
      -- A shared conflict index gives one vertex per class and a clique on them.
      have hTarget (a : Fin n) : ∃ x, c x = (sel a).val ∧ slot x = d := by
        have hzero : 0 < n := by omega
        let o : Fin n := ⟨0, hzero⟩
        let p : Fin n := ⟨1, by omega⟩
        by_cases ha : a = o
        · obtain ⟨x, y, hx, _, hxd, _, _⟩ := conflict_of_some (hsel a p (by subst a; change 0 < 1; omega))
          exact ⟨x, hx, hxd⟩
        · obtain ⟨x, y, _, hy, _, hyd, _⟩ := conflict_of_some (hsel o a (by
            change 0 < a.val
            have hz : a.val ≠ 0 := fun hv => ha (Fin.ext hv)
            omega))
          exact ⟨y, hy, hyd⟩
      choose f hfColor hfSlot using hTarget
      have hsel_inj : Function.Injective (fun i => (sel i).val) :=
        Subtype.val_injective.comp sel.injective
      have hfinj : Function.Injective f := fun a b hab =>
        hsel_inj ((hfColor a).symm.trans ((congrArg c hab).trans (hfColor b)))
      have hadj (a b : Fin n) (hab : a < b) : G.Adj (f a) (f b) := by
        obtain ⟨x, y, hx, hy, hxd, hyd, hxy⟩ := conflict_of_some (hsel a b hab)
        have hxb : ¬IndependentClass G c (c x) := hx.symm ▸ (sel a).property
        have hyb : ¬IndependentClass G c (c y) := hy.symm ▸ (sel b).property
        have heq₁ := slot_injective (hx.trans (hfColor a).symm) hxb (hxd.trans (hfSlot a).symm)
        have heq₂ := slot_injective (hy.trans (hfColor b).symm) hyb (hyd.trans (hfSlot b).symm)
        simpa only [heq₁, heq₂] using hxy
      apply no_clique_embedding hf ⟨f, hfinj⟩
      intro a b hab
      rcases lt_or_gt_of_ne hab with hab | hab
      · exact hadj a b hab
      · exact (hadj b a hab).symm
    | none =>
      -- Regroup the selected classes by index, using fewer colors.
      let e : Fin n ↪ Fin k := sel.trans ⟨Subtype.val, Subtype.val_injective⟩
      let Rest := {i : Fin k // i ∉ Set.range e}
      let _ : Fintype Rest := inferInstanceAs (Fintype {i : Fin k // i ∉ Set.range e})
      let recolor (v : V) : Rest ⊕ Fin (n - 1) :=
        if h : c v ∈ Set.range e then Sum.inr (slot v) else Sum.inl ⟨c v, h⟩
      have hrest : Fintype.card Rest = k - n := by
        rw [show Fintype.card Rest = Fintype.card (Fin k) -
            Fintype.card {i : Fin k // i ∈ Set.range e} from Fintype.card_subtype_compl _]
        rw [Fintype.card_fin, ← Fintype.card_congr (Equiv.ofInjective e e.injective), Fintype.card_fin]
      have h_recolor : G.Cocolorable (Fintype.card (Rest ⊕ Fin (n - 1))) := by
        apply cocolorable_of_classes recolor
        intro i
        cases i with
        | inl i =>
          have heq (v : V) (h : recolor v = Sum.inl i) : c v = i.val := by
            unfold recolor at h
            split at h
            · contradiction
            · exact congrArg Subtype.val (Sum.inl.inj h)
          rcases hc i.val with hi | hi
          · exact Or.inl fun x y hx hy => hi x y (heq x hx) (heq y hy)
          · exact Or.inr fun x y hx hy => hi x y (heq x hx) (heq y hy)
        | inr j =>
          have heq (v : V) (h : recolor v = Sum.inr j) :
              c v ∈ Set.range e ∧ slot v = j := by
            unfold recolor at h
            split at h
            · rename_i hv
              exact ⟨hv, Sum.inr.inj h⟩
            · contradiction
          refine Or.inl fun x y hx hy hxy => ?_
          obtain ⟨⟨a, ha⟩, hxa⟩ := heq x hx
          obtain ⟨⟨b, hb⟩, hyb⟩ := heq y hy
          change (sel a).val = c x at ha
          change (sel b).val = c y at hb
          rcases lt_trichotomy a b with hab | hab | hab
          · exact no_conflict_of_none (hsel a b hab) j ⟨x, y, ha.symm, hb.symm, hxa, hyb, hxy⟩
          · subst b
            exact hxy.ne (slot_injective (ha.symm.trans hb) (ha ▸ (sel a).property)
              (hxa.trans hyb.symm))
          · exact no_conflict_of_none (hsel b a hab) j ⟨y, x, hb.symm, ha.symm, hyb, hxa, hxy.symm⟩
      have hn_le : n ≤ k := by simpa using Fintype.card_le_of_embedding e
      have hle := hmin _ h_recolor
      rw [Fintype.card_sum, hrest, Fintype.card_fin] at hle
      omega
  let Vert := {v : V // ¬IndependentClass G c (c v)}
  let _ : Fintype Vert := inferInstanceAs (Fintype {v : V // ¬IndependentClass G c (c v)})
  let pack (v : Vert) : Bad × Fin (n - 1) := (⟨c v.val, v.property⟩, slot v.val)
  have hpack : Function.Injective pack := by
    intro x y h
    apply Subtype.ext
    exact slot_injective (congrArg (fun p => p.1.val) h) x.property (congrArg Prod.snd h)
  have hVert : Fintype.card Vert ≤ R * (n - 1) := by
    have h := Fintype.card_le_of_injective pack hpack
    rw [Fintype.card_prod, Fintype.card_fin] at h
    exact h.trans (Nat.mul_le_mul_right _ hBad)
  let recolor (v : V) : Fin k ⊕ Vert :=
    if h : ¬IndependentClass G c (c v) then Sum.inr ⟨v, h⟩ else Sum.inl (c v)
  have hProper (x y : V) (hxy : G.Adj x y) (h : recolor x = recolor y) : False := by
    unfold recolor at h
    split at h <;> split at h
    · exact hxy.ne (congrArg Subtype.val (Sum.inr.inj h))
    · contradiction
    · contradiction
    · rename_i hx hy
      exact (not_not.mp hx) x y rfl (Sum.inl.inj h).symm hxy
  have hχ := chromatic_le_card_of_coloring recolor hProper
  rw [hnum]
  rw [Fintype.card_sum, Fintype.card_fin] at hχ
  exact hχ.trans (by exact_mod_cast Nat.add_le_add_left hVert k)