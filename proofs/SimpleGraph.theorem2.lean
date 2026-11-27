import FormalConjectures.Paper.DegreeSequencesTriangleFree

/-!
# Embedding Any Triangle-Free Graph into One with Degree Multiplicity `3`

We prove that every finite connected triangle-free graph `G` on `α` (`n = |α| ≥ 1`) is an induced
subgraph of a finite triangle-free graph `H` with `degreeSequenceMultiplicity H = 3`.

1. Identify `α` with `Fin n` via `e : Fin n ≃ α`. For each `k < n`, set
   `m k = n + k - G.degree (e k) ≥ 1`, so adding `m k` edges to `e k` produces pairwise distinct
   degrees `n, n + 1, ..., 2n - 1`.
2. Let `P = ∑_{k < n} m k`, `a = 2n`, `b = 2n + P`, and `M = b + 1`. Construct `H` on
   `ULift (Fin n ⊕ (Fin M ⊕ Fin M))` by placing a copy of `G` on `Fin n`, a staircase bipartite
   graph `j ≤ i` between `L = Fin M` and `R = Fin M`, and connecting each `k : Fin n` to a
   pairwise-disjoint block of `m k` vertices of `L` partitioning `[a, b)`.
3. Since `L` and `R` are independent, there are no edges between `Fin n` and `R`, and the
   neighborhoods of `k : Fin n` in `L` are pairwise disjoint, `H` is triangle-free and contains
   `G` as an induced subgraph.
4. Counting degrees across `Fin n`, `L`, and `R` gives exact multiplicity `3` at degree `M` (and
   at degrees `n, ..., 2n - 1`) and at most `3` at every degree, so
   `degreeSequenceMultiplicity H = 3`.
-/

-- Problem: Theorem 2.
-- Upstream: formal-conjectures FormalConjectures/Paper/DegreeSequencesTriangleFree.lean:287 (declaration SimpleGraph.theorem2)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Theorem2EFSProof

open SimpleGraph Finset

/- ### Section 1: Prefix-sum interval partition helpers -/

private lemma sum_range_mono (m : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    ∑ t ∈ Finset.range i, m t ≤ ∑ t ∈ Finset.range j, m t :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hij)

private lemma exists_interval_of_lt_sum (m : ℕ → ℕ) :
    ∀ (n t : ℕ), t < ∑ j ∈ Finset.range n, m j →
      ∃ k < n, (∑ j ∈ Finset.range k, m j) ≤ t ∧ t < (∑ j ∈ Finset.range (k + 1), m j) := by
  intro n
  induction n with
  | zero =>
    intro t ht
    simp at ht
  | succ n ih =>
    intro t ht
    rw [Finset.sum_range_succ] at ht
    by_cases hlt : t < ∑ j ∈ Finset.range n, m j
    · obtain ⟨k, hk, h1, h2⟩ := ih t hlt
      exact ⟨k, by omega, h1, h2⟩
    · exact ⟨n, by omega, by omega, by rw [Finset.sum_range_succ]; exact ht⟩

private lemma interval_unique (m : ℕ → ℕ) {k₁ k₂ t : ℕ}
    (h1a : ∑ j ∈ Finset.range k₁, m j ≤ t)
    (h1b : t < ∑ j ∈ Finset.range (k₁ + 1), m j)
    (h2a : ∑ j ∈ Finset.range k₂, m j ≤ t)
    (h2b : t < ∑ j ∈ Finset.range (k₂ + 1), m j) : k₁ = k₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmono : ∑ j ∈ Finset.range (k₁ + 1), m j ≤ ∑ j ∈ Finset.range k₂, m j :=
      sum_range_mono m (by omega)
    omega
  · have hmono : ∑ j ∈ Finset.range (k₂ + 1), m j ≤ ∑ j ∈ Finset.range k₁, m j :=
      sum_range_mono m (by omega)
    omega

/- ### Section 2: Degree multiplicity characterization -/

private lemma count_degreeSequence {β : Type*} [Fintype β] [DecidableEq β]
    (H : SimpleGraph β) [DecidableRel H.Adj] (d : ℕ) :
    (degreeSequence H).count d = (Finset.univ.filter (fun v : β => H.degree v = d)).card := by
  have h1 : (degreeSequence H).count d = ((degreeSequence H : Multiset ℕ)).count d := by
    rw [Multiset.coe_count]
  rw [h1]
  unfold degreeSequence
  rw [Multiset.sort_eq]
  have hgen : ∀ s : Finset β,
      (s.val.map (fun v => H.degree v)).count d =
        (s.filter (fun v => H.degree v = d)).card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih =>
      rw [Finset.insert_val_of_notMem hx, Multiset.map_cons, Multiset.count_cons,
        Finset.filter_insert]
      by_cases h : H.degree x = d
      · rw [if_pos h.symm, if_pos h, Finset.card_insert_of_notMem (by simp [hx]), ih]
      · rw [if_neg (Ne.symm h), if_neg h, ih, add_zero]
  exact hgen Finset.univ

private lemma degreeSequenceMultiplicity_eq_of_bounds {β : Type*} [Fintype β] [DecidableEq β]
    (H : SimpleGraph β) [DecidableRel H.Adj] (M_val : ℕ)
    (hle : ∀ d : ℕ, (Finset.univ.filter (fun v : β => H.degree v = d)).card ≤ 3)
    (heq : (Finset.univ.filter (fun v : β => H.degree v = M_val)).card = 3) :
    degreeSequenceMultiplicity H = 3 := by
  let ds : List ℕ := degreeSequence H
  have hcnt_le : ∀ d : ℕ, ds.count d ≤ 3 := fun d => by
    dsimp only [ds]; rw [count_degreeSequence]; exact hle d
  have hcnt_M : ds.count M_val = 3 := by
    dsimp only [ds]; rw [count_degreeSequence]; exact heq
  have hM_mem : M_val ∈ ds := List.count_pos_iff.mp (by omega)
  have h3_mem : 3 ∈ ds.map (fun d => ds.count d) :=
    List.mem_map.mpr ⟨M_val, hM_mem, hcnt_M⟩
  have hne : ds.map (fun d => ds.count d) ≠ [] := List.ne_nil_of_mem h3_mem
  obtain ⟨m, hmax⟩ := Option.ne_none_iff_exists'.mp (List.max?_eq_none_iff.not.mpr hne)
  have hm_spec := List.max?_eq_some_iff.mp hmax
  have h3_le : 3 ≤ m := hm_spec.2 3 h3_mem
  have hm_le : m ≤ 3 := by
    obtain ⟨d, _, hd⟩ := List.mem_map.mp hm_spec.1
    rw [← hd]
    exact hcnt_le d
  have hm3 : m = 3 := by omega
  unfold degreeSequenceMultiplicity
  change (List.max? (ds.map (fun d => ds.count d))).getD 0 = 3
  rw [hmax, hm3]
  rfl

/- ### Section 3: Explicit triangle-free supergraph construction -/

private def extAdj {n : ℕ} (M : ℕ) (G0 : SimpleGraph (Fin n)) (a : ℕ) (S : ℕ → ℕ)
    (x y : Fin n ⊕ (Fin M ⊕ Fin M)) : Prop :=
  match x, y with
  | Sum.inl u, Sum.inl v => G0.Adj u v
  | Sum.inl u, Sum.inr (Sum.inl ℓ) => a + S u.1 ≤ ℓ.1 ∧ ℓ.1 < a + S (u.1 + 1)
  | Sum.inr (Sum.inl ℓ), Sum.inl u => a + S u.1 ≤ ℓ.1 ∧ ℓ.1 < a + S (u.1 + 1)
  | Sum.inr (Sum.inl ℓ), Sum.inr (Sum.inr r) => r.1 ≤ ℓ.1
  | Sum.inr (Sum.inr r), Sum.inr (Sum.inl ℓ) => r.1 ≤ ℓ.1
  | _, _ => False

private instance instDecidableRelExtAdj {n : ℕ} (M : ℕ) (G0 : SimpleGraph (Fin n))
    [DecidableRel G0.Adj] (a : ℕ) (S : ℕ → ℕ) : DecidableRel (extAdj M G0 a S) := fun x y => by
  cases x with
  | inl u =>
    cases y with
    | inl v => exact inferInstanceAs (Decidable (G0.Adj u v))
    | inr yr =>
      cases yr with
      | inl ℓ => exact inferInstanceAs (Decidable (a + S u.1 ≤ ℓ.1 ∧ ℓ.1 < a + S (u.1 + 1)))
      | inr _ => exact isFalse id
  | inr xr =>
    cases xr with
    | inl ℓ =>
      cases y with
      | inl u => exact inferInstanceAs (Decidable (a + S u.1 ≤ ℓ.1 ∧ ℓ.1 < a + S (u.1 + 1)))
      | inr yr =>
        cases yr with
        | inl _ => exact isFalse id
        | inr r => exact inferInstanceAs (Decidable (r.1 ≤ ℓ.1))
    | inr r =>
      cases y with
      | inl _ => exact isFalse id
      | inr yr =>
        cases yr with
        | inl ℓ => exact inferInstanceAs (Decidable (r.1 ≤ ℓ.1))
        | inr _ => exact isFalse id

private def extGraph {n : ℕ} (M : ℕ) (G0 : SimpleGraph (Fin n)) (a : ℕ) (S : ℕ → ℕ) :
    SimpleGraph (Fin n ⊕ (Fin M ⊕ Fin M)) where
  Adj := extAdj M G0 a S
  symm := ⟨fun x y h => by
    cases x with
    | inl u =>
      cases y with
      | inl v => exact h.symm
      | inr yr =>
        cases yr with
        | inl ℓ => exact h
        | inr r => exact False.elim h
    | inr xr =>
      cases xr with
      | inl ℓ =>
        cases y with
        | inl u => exact h
        | inr yr =>
          cases yr with
          | inl ℓ' => exact False.elim h
          | inr r => exact h
      | inr r =>
        cases y with
        | inl u => exact False.elim h
        | inr yr =>
          cases yr with
          | inl ℓ => exact h
          | inr r' => exact False.elim h⟩
  loopless := ⟨fun x h => by
    cases x with
    | inl u => exact G0.loopless.irrefl u h
    | inr xr =>
      cases xr with
      | inl ℓ => exact False.elim h
      | inr r => exact False.elim h⟩

private instance instDecidableRelExtGraph {n : ℕ} (M : ℕ) (G0 : SimpleGraph (Fin n))
    [DecidableRel G0.Adj] (a : ℕ) (S : ℕ → ℕ) : DecidableRel (extGraph M G0 a S).Adj :=
  instDecidableRelExtAdj M G0 a S

private lemma extGraph_cliqueFree {n : ℕ} (M : ℕ) (G0 : SimpleGraph (Fin n)) (h0 : G0.CliqueFree 3)
    (a : ℕ) (m : ℕ → ℕ) :
    (extGraph M G0 a (fun k => ∑ j ∈ Finset.range k, m j)).CliqueFree 3 := by
  let S : ℕ → ℕ := fun k => ∑ j ∈ Finset.range k, m j
  intro c hc
  obtain ⟨x, y, z, hxy, hxz, hyz, hceq⟩ := Finset.card_eq_three.mp hc.2
  have hx : x ∈ (c : Set _) := by rw [hceq]; simp
  have hy : y ∈ (c : Set _) := by rw [hceq]; simp
  have hz : z ∈ (c : Set _) := by rw [hceq]; simp
  have hadj_xy : extAdj M G0 a S x y := hc.1 hx hy hxy
  have hadj_xz : extAdj M G0 a S x z := hc.1 hx hz hxz
  have hadj_yz : extAdj M G0 a S y z := hc.1 hy hz hyz
  have hno_uul : ∀ (u v : Fin n) (ℓ : Fin M),
      u ≠ v → extAdj M G0 a S (Sum.inl u) (Sum.inr (Sum.inl ℓ)) →
      extAdj M G0 a S (Sum.inl v) (Sum.inr (Sum.inl ℓ)) → False := by
    intro u v ℓ huv hu hv
    dsimp only [extAdj, S] at hu hv
    have heq := interval_unique m (k₁ := u.1) (k₂ := v.1) (t := ℓ.1 - a)
      (by omega) (by omega) (by omega) (by omega)
    exact huv (Fin.ext heq)
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      cases z with
      | inl w =>
        have hclq : G0.IsNClique 3 {u, v, w} := by
          refine ⟨?_, ?_⟩
          · intro p hp q hq hpq
            simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
              Set.mem_singleton_iff] at hp hq
            rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
            · exact absurd rfl hpq
            · exact hadj_xy
            · exact hadj_xz
            · exact (G0.adj_comm _ _).mp hadj_xy
            · exact absurd rfl hpq
            · exact hadj_yz
            · exact (G0.adj_comm _ _).mp hadj_xz
            · exact (G0.adj_comm _ _).mp hadj_yz
            · exact absurd rfl hpq
          · have h1 : u ≠ v := fun h => hxy (congrArg Sum.inl h)
            have h2 : u ≠ w := fun h => hxz (congrArg Sum.inl h)
            have h3 : v ≠ w := fun h => hyz (congrArg Sum.inl h)
            rw [Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair h3]
        exact h0 {u, v, w} hclq
      | inr zr =>
        cases zr with
        | inl ℓ => exact hno_uul u v ℓ (fun h => hxy (congrArg Sum.inl h)) hadj_xz hadj_yz
        | inr r => exact False.elim hadj_xz
    | inr yr =>
      cases yr with
      | inl ℓ =>
        cases z with
        | inl w => exact hno_uul u w ℓ (fun h => hxz (congrArg Sum.inl h)) hadj_xy hadj_yz
        | inr zr =>
          cases zr with
          | inl ℓ' => exact False.elim hadj_yz
          | inr r => exact False.elim hadj_xz
      | inr r => exact False.elim hadj_xy
  | inr xr =>
    cases xr with
    | inl ℓ =>
      cases y with
      | inl v =>
        cases z with
        | inl w => exact hno_uul v w ℓ (fun h => hyz (congrArg Sum.inl h)) hadj_xy hadj_xz
        | inr zr =>
          cases zr with
          | inl ℓ' => exact False.elim hadj_xz
          | inr r => exact False.elim hadj_yz
      | inr yr =>
        cases yr with
        | inl ℓ' => exact False.elim hadj_xy
        | inr r =>
          cases z with
          | inl w => exact False.elim hadj_yz
          | inr zr =>
            cases zr with
            | inl ℓ' => exact False.elim hadj_xz
            | inr r' => exact False.elim hadj_yz
    | inr r =>
      cases y with
      | inl v => exact False.elim hadj_xy
      | inr yr =>
        cases yr with
        | inl ℓ =>
          cases z with
          | inl w => exact False.elim hadj_xz
          | inr zr =>
            cases zr with
            | inl ℓ' => exact False.elim hadj_yz
            | inr r' => exact False.elim hadj_xz
        | inr r' => exact False.elim hadj_xy

private lemma exists_fin_extension {n : ℕ} (hn : 1 ≤ n)
    (G0 : SimpleGraph (Fin n)) [DecidableRel G0.Adj] (h0 : G0.CliqueFree 3) :
    ∃ (M : ℕ) (H0 : SimpleGraph (Fin n ⊕ (Fin M ⊕ Fin M))) (_ : DecidableRel H0.Adj),
      (∀ u v : Fin n, H0.Adj (Sum.inl u) (Sum.inl v) ↔ G0.Adj u v) ∧
      H0.CliqueFree 3 ∧
      degreeSequenceMultiplicity H0 = 3 := by
  let m : ℕ → ℕ := fun k => if hk : k < n then n + k - G0.degree ⟨k, hk⟩ else 0
  let S : ℕ → ℕ := fun k => ∑ j ∈ Finset.range k, m j
  let P : ℕ := S n
  let a : ℕ := 2 * n
  let b : ℕ := a + P
  let M : ℕ := b + 1
  have hm_ge1 : ∀ k < n, 1 ≤ m k := by
    intro k hk
    have hlt : G0.degree ⟨k, hk⟩ < n := by
      simpa [Fintype.card_fin] using G0.degree_lt_card_verts ⟨k, hk⟩
    simp only [m, dif_pos hk]
    omega
  have hP_ge : n ≤ P := by
    calc n = ∑ _j ∈ Finset.range n, 1 := by simp
      _ ≤ ∑ j ∈ Finset.range n, m j :=
          Finset.sum_le_sum fun j hj => hm_ge1 j (Finset.mem_range.mp hj)
  have hS_succ : ∀ k : ℕ, S (k + 1) = S k + m k := fun k => Finset.sum_range_succ m k
  have hS_le_P : ∀ k ≤ n, S k ≤ P := fun k hk => sum_range_mono m hk
  let H0 : SimpleGraph (Fin n ⊕ (Fin M ⊕ Fin M)) := extGraph M G0 a S
  have hH0_cf : H0.CliqueFree 3 := extGraph_cliqueFree M G0 h0 a m
  -- Compute degrees of all three vertex classes in H0
  have hdeg_inl : ∀ u : Fin n, H0.degree (Sum.inl u) = n + u.1 := by
    intro u
    rw [SimpleGraph.degree]
    have hnb : H0.neighborFinset (Sum.inl u) =
        (G0.neighborFinset u).image Sum.inl ∪
        ((Finset.univ : Finset (Fin M)).filter
          (fun ℓ => a + S u.1 ≤ ℓ.1 ∧ ℓ.1 < a + S (u.1 + 1))).image (fun ℓ => Sum.inr (Sum.inl ℓ)) := by
      ext x
      simp only [mem_neighborFinset, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      cases x with
      | inl v =>
        simp only [Sum.inl.injEq, reduceCtorEq, and_false, exists_false, or_false, exists_eq_right]
        rfl
      | inr xr =>
        cases xr with
        | inl ℓ =>
          simp only [reduceCtorEq, and_false, exists_false, false_or, Sum.inr.injEq, Sum.inl.injEq,
            exists_eq_right]
          rfl
        | inr r =>
          simp only [Sum.inr.injEq, reduceCtorEq, and_false, exists_false, or_self]
          rfl
    have hdisj : Disjoint ((G0.neighborFinset u).image (Sum.inl : Fin n → Fin n ⊕ (Fin M ⊕ Fin M)))
        (((Finset.univ : Finset (Fin M)).filter
          (fun ℓ => a + S u.1 ≤ ℓ.1 ∧ ℓ.1 < a + S (u.1 + 1))).image
            (fun ℓ => (Sum.inr (Sum.inl ℓ) : Fin n ⊕ (Fin M ⊕ Fin M)))) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨_, _, h⟩ := Finset.mem_image.mp h2
      exact absurd h (by simp)
    have hL_card : ((Finset.univ : Finset (Fin M)).filter
        (fun ℓ => a + S u.1 ≤ ℓ.1 ∧ ℓ.1 < a + S (u.1 + 1))).card = m u.1 := by
      have hle_M : a + S (u.1 + 1) ≤ M := by
        have := hS_le_P (u.1 + 1) u.2
        omega
      have hbij : ((Finset.univ : Finset (Fin M)).filter
          (fun ℓ => a + S u.1 ≤ ℓ.1 ∧ ℓ.1 < a + S (u.1 + 1))).card =
          (Finset.range (m u.1)).card := by
        refine Finset.card_bij (fun ℓ _ => ℓ.1 - (a + S u.1))
          (fun ℓ hℓ => Finset.mem_range.mpr (by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
            have := hS_succ u.1; omega))
          (fun ℓ₁ hℓ₁ ℓ₂ hℓ₂ heq => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hℓ₁ hℓ₂
            exact Fin.ext (by omega))
          (fun t ht => by
            have ht' := Finset.mem_range.mp ht
            have := hS_succ u.1
            refine ⟨⟨a + S u.1 + t, by omega⟩, ?_, by dsimp; omega⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            omega)
      rw [hbij, Finset.card_range]
    rw [hnb, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj (Sum.inr.inj h)),
      hL_card, ← SimpleGraph.degree]
    have hlt : G0.degree u < n := by
      simpa [Fintype.card_fin] using G0.degree_lt_card_verts u
    have hm_eq : m u.1 = n + u.1 - G0.degree u := by
      simp only [m, dif_pos u.2, Fin.eta]
    omega
  have hdeg_L : ∀ ℓ : Fin M,
      H0.degree (Sum.inr (Sum.inl ℓ)) = if a ≤ ℓ.1 ∧ ℓ.1 < b then ℓ.1 + 2 else ℓ.1 + 1 := by
    intro ℓ
    rw [SimpleGraph.degree]
    let A_nb : Finset (Fin n) := Finset.univ.filter (fun u : Fin n =>
      a + S u.1 ≤ ℓ.1 ∧ ℓ.1 < a + S (u.1 + 1))
    let R_nb : Finset (Fin M) := Finset.univ.filter (fun r : Fin M => r.1 ≤ ℓ.1)
    have hnb : H0.neighborFinset (Sum.inr (Sum.inl ℓ)) =
        A_nb.image Sum.inl ∪ R_nb.image (fun r => Sum.inr (Sum.inr r)) := by
      ext x
      simp only [mem_neighborFinset, Finset.mem_union, Finset.mem_image, A_nb, R_nb,
        Finset.mem_filter, Finset.mem_univ, true_and]
      cases x with
      | inl u =>
        simp only [Sum.inl.injEq, reduceCtorEq, and_false, exists_false, or_false, exists_eq_right]
        rfl
      | inr xr =>
        cases xr with
        | inl ℓ' =>
          simp only [Sum.inr.injEq, reduceCtorEq, and_false, exists_false, or_self]
          rfl
        | inr r =>
          simp only [reduceCtorEq, and_false, exists_false, false_or, Sum.inr.injEq, exists_eq_right]
          rfl
    have hdisj : Disjoint (A_nb.image (Sum.inl : Fin n → Fin n ⊕ (Fin M ⊕ Fin M)))
        (R_nb.image (fun r => (Sum.inr (Sum.inr r) : Fin n ⊕ (Fin M ⊕ Fin M)))) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨_, _, h⟩ := Finset.mem_image.mp h2
      exact absurd h (by simp)
    have hR_card : R_nb.card = ℓ.1 + 1 := by
      have hbij : R_nb.card = (Finset.range (ℓ.1 + 1)).card := by
        refine Finset.card_bij (fun r _ => r.1)
          (fun r hr => Finset.mem_range.mpr (by
            simp only [R_nb, Finset.mem_filter, Finset.mem_univ, true_and] at hr; omega))
          (fun _ _ _ _ h => Fin.ext h)
          (fun t ht => by
            have ht' := Finset.mem_range.mp ht
            refine ⟨⟨t, by have := ℓ.2; omega⟩, ?_, rfl⟩
            simp only [R_nb, Finset.mem_filter, Finset.mem_univ, true_and]
            omega)
      rw [hbij, Finset.card_range]
    have hA_card : A_nb.card = if a ≤ ℓ.1 ∧ ℓ.1 < b then 1 else 0 := by
      split_ifs with hab
      · obtain ⟨k, hk, h1, h2⟩ :=
          exists_interval_of_lt_sum m n (ℓ.1 - a) (show ℓ.1 - a < S n by omega)
        have h1' : S k ≤ ℓ.1 - a := h1
        have h2' : ℓ.1 - a < S (k + 1) := h2
        have hsing : A_nb = {⟨k, hk⟩} := by
          ext u
          simp only [A_nb, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hu
            have heq := interval_unique m (k₁ := u.1) (k₂ := k) (t := ℓ.1 - a)
              (show S u.1 ≤ ℓ.1 - a by omega) (show ℓ.1 - a < S (u.1 + 1) by omega) h1 h2
            exact Fin.ext heq
          · rintro rfl
            dsimp
            omega
        rw [hsing, Finset.card_singleton]
      · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro u hu
        simp only [A_nb, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        have hle := hS_le_P (u.1 + 1) u.2
        omega
    rw [hnb, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ (fun _ _ h => Sum.inr.inj (Sum.inr.inj h)),
      hA_card, hR_card]
    split_ifs <;> omega
  have hdeg_R : ∀ r : Fin M, H0.degree (Sum.inr (Sum.inr r)) = M - r.1 := by
    intro r
    rw [SimpleGraph.degree]
    let L_nb : Finset (Fin M) := Finset.univ.filter (fun ℓ : Fin M => r.1 ≤ ℓ.1)
    have hnb : H0.neighborFinset (Sum.inr (Sum.inr r)) =
        L_nb.image (fun ℓ => Sum.inr (Sum.inl ℓ)) := by
      ext x
      simp only [mem_neighborFinset, Finset.mem_image, L_nb, Finset.mem_filter, Finset.mem_univ,
        true_and]
      cases x with
      | inl u =>
        simp only [reduceCtorEq, and_false, exists_false]
        rfl
      | inr xr =>
        cases xr with
        | inl ℓ =>
          simp only [Sum.inr.injEq, Sum.inl.injEq, exists_eq_right]
          rfl
        | inr r' =>
          simp only [Sum.inr.injEq, reduceCtorEq, and_false, exists_false]
          rfl
    have hL_card : L_nb.card = M - r.1 := by
      have hbij : L_nb.card = (Finset.range (M - r.1)).card := by
        refine Finset.card_bij (fun ℓ _ => ℓ.1 - r.1)
          (fun ℓ hℓ => Finset.mem_range.mpr (by
            simp only [L_nb, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
            have := ℓ.2; omega))
          (fun ℓ₁ hℓ₁ ℓ₂ hℓ₂ h => by
            simp only [L_nb, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ₁ hℓ₂
            exact Fin.ext (by omega))
          (fun t ht => by
            have ht' := Finset.mem_range.mp ht
            refine ⟨⟨r.1 + t, by omega⟩, ?_, by dsimp; omega⟩
            simp only [L_nb, Finset.mem_filter, Finset.mem_univ, true_and]
            omega)
      rw [hbij, Finset.card_range]
    rw [hnb, Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj (Sum.inr.inj h)), hL_card]
  -- Count vertices of degree d across the three disjoint parts Fin n, L, R
  have hcount_split : ∀ d : ℕ,
      (Finset.univ.filter (fun x : Fin n ⊕ (Fin M ⊕ Fin M) => H0.degree x = d)).card =
        (Finset.univ.filter (fun u : Fin n => H0.degree (Sum.inl u) = d)).card +
        (Finset.univ.filter (fun ℓ : Fin M => H0.degree (Sum.inr (Sum.inl ℓ)) = d)).card +
        (Finset.univ.filter (fun r : Fin M => H0.degree (Sum.inr (Sum.inr r)) = d)).card := by
    intro d
    let C1 : Finset (Fin n ⊕ (Fin M ⊕ Fin M)) :=
      (Finset.univ.filter (fun u : Fin n => H0.degree (Sum.inl u) = d)).image Sum.inl
    let C2 : Finset (Fin n ⊕ (Fin M ⊕ Fin M)) :=
      (Finset.univ.filter (fun ℓ : Fin M => H0.degree (Sum.inr (Sum.inl ℓ)) = d)).image
        (fun ℓ => Sum.inr (Sum.inl ℓ))
    let C3 : Finset (Fin n ⊕ (Fin M ⊕ Fin M)) :=
      (Finset.univ.filter (fun r : Fin M => H0.degree (Sum.inr (Sum.inr r)) = d)).image
        (fun r => Sum.inr (Sum.inr r))
    have hunion : Finset.univ.filter (fun x : Fin n ⊕ (Fin M ⊕ Fin M) => H0.degree x = d) =
        (C1 ∪ C2) ∪ C3 := by
      ext x
      simp only [C1, C2, C3, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and]
      cases x with
      | inl u => simp
      | inr xr =>
        cases xr with
        | inl ℓ => simp
        | inr r => simp
    have hd12 : Disjoint C1 C2 := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨_, _, h⟩ := Finset.mem_image.mp h2
      exact absurd h (by simp)
    have hd123 : Disjoint (C1 ∪ C2) C3 := by
      rw [Finset.disjoint_left]
      intro x h12 h3
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h3
      rcases Finset.mem_union.mp h12 with h1 | h2
      · obtain ⟨_, _, h⟩ := Finset.mem_image.mp h1; exact absurd h (by simp)
      · obtain ⟨_, _, h⟩ := Finset.mem_image.mp h2; exact absurd h (by simp)
    rw [hunion, Finset.card_union_of_disjoint hd123, Finset.card_union_of_disjoint hd12,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj (Sum.inr.inj h)),
      Finset.card_image_of_injective _ (fun _ _ h => Sum.inr.inj (Sum.inr.inj h))]
  -- Bound each of the three counts explicitly
  have hC1_le : ∀ d : ℕ,
      (Finset.univ.filter (fun u : Fin n => H0.degree (Sum.inl u) = d)).card ≤
        if d < 2 * n then 1 else 0 := by
    intro d
    split_ifs with hd
    · refine Finset.card_le_one.mpr fun u₁ hu₁ u₂ hu₂ => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdeg_inl] at hu₁ hu₂
      exact Fin.ext (by omega)
    · rw [Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdeg_inl] at hu
      have := u.2; omega
  have hC2_le : ∀ d : ℕ,
      (Finset.univ.filter (fun ℓ : Fin M => H0.degree (Sum.inr (Sum.inl ℓ)) = d)).card ≤
        if d = M then 2 else 1 := by
    intro d
    split_ifs with hd
    · have hsub : Finset.univ.filter (fun ℓ : Fin M => H0.degree (Sum.inr (Sum.inl ℓ)) = d) ⊆
          ({⟨b - 1, by omega⟩, ⟨b, by omega⟩} : Finset (Fin M)) := by
        intro ℓ hℓ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdeg_L] at hℓ
        simp only [Finset.mem_insert, Finset.mem_singleton]
        split_ifs at hℓ with hab
        · left; exact Fin.ext (by dsimp; omega)
        · right; exact Fin.ext (by dsimp; omega)
      calc _ ≤ ({⟨b - 1, by omega⟩, ⟨b, by omega⟩} : Finset (Fin M)).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    · refine Finset.card_le_one.mpr fun ℓ₁ hℓ₁ ℓ₂ hℓ₂ => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdeg_L] at hℓ₁ hℓ₂
      split_ifs at hℓ₁ hℓ₂ with h1 h2 h2
      · exact Fin.ext (by omega)
      · have h1M := ℓ₁.2; have h2M := ℓ₂.2; omega
      · have h1M := ℓ₁.2; have h2M := ℓ₂.2; omega
      · exact Fin.ext (by omega)
  have hC3_le : ∀ d : ℕ,
      (Finset.univ.filter (fun r : Fin M => H0.degree (Sum.inr (Sum.inr r)) = d)).card ≤ 1 := by
    intro d
    refine Finset.card_le_one.mpr fun r₁ hr₁ r₂ hr₂ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdeg_R] at hr₁ hr₂
    have h1 := r₁.2; have h2 := r₂.2
    exact Fin.ext (by omega)
  have hle3 : ∀ d : ℕ,
      (Finset.univ.filter (fun x : Fin n ⊕ (Fin M ⊕ Fin M) => H0.degree x = d)).card ≤ 3 := by
    intro d
    rw [hcount_split d]
    have h1 := hC1_le d
    have h2 := hC2_le d
    have h3 := hC3_le d
    split_ifs at h1 h2 <;> omega
  have heq3 :
      (Finset.univ.filter (fun x : Fin n ⊕ (Fin M ⊕ Fin M) => H0.degree x = M)).card = 3 := by
    rw [hcount_split M]
    have h1 : (Finset.univ.filter (fun u : Fin n => H0.degree (Sum.inl u) = M)).card = 0 := by
      have := hC1_le M
      split_ifs at this <;> omega
    have h2 : (Finset.univ.filter (fun ℓ : Fin M => H0.degree (Sum.inr (Sum.inl ℓ)) = M)).card = 2 := by
      have hset : Finset.univ.filter (fun ℓ : Fin M => H0.degree (Sum.inr (Sum.inl ℓ)) = M) =
          ({⟨b - 1, by omega⟩, ⟨b, by omega⟩} : Finset (Fin M)) := by
        ext ℓ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdeg_L, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro hℓ
          split_ifs at hℓ with hab
          · left; exact Fin.ext (by dsimp; omega)
          · right; exact Fin.ext (by dsimp; omega)
        · rintro (rfl | rfl)
          · dsimp; split_ifs <;> omega
          · dsimp; split_ifs <;> omega
      rw [hset, Finset.card_pair]
      intro h
      have := congrArg Fin.val h
      dsimp at this
      omega
    have h3 : (Finset.univ.filter (fun r : Fin M => H0.degree (Sum.inr (Sum.inr r)) = M)).card = 1 := by
      have hset : Finset.univ.filter (fun r : Fin M => H0.degree (Sum.inr (Sum.inr r)) = M) =
          {⟨0, by omega⟩} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdeg_R, Finset.mem_singleton]
        constructor
        · intro hr; exact Fin.ext (by dsimp; omega)
        · rintro rfl; simp
      rw [hset, Finset.card_singleton]
    omega
  refine ⟨M, H0, instDecidableRelExtGraph M G0 a S, fun u v => Iff.rfl, hH0_cf, ?_⟩
  exact degreeSequenceMultiplicity_eq_of_bounds H0 M hle3 heq3

/- ### Section 4: Universe-lifting wrapper -/

private lemma transfer_to_ulift.{u} {γ : Type} [Fintype γ] [DecidableEq γ]
    (H0 : SimpleGraph γ) [DecidableRel H0.Adj]
    [DecidableRel (H0.comap (ULift.down : ULift.{u} γ → γ)).Adj]
    (hcf : H0.CliqueFree 3) (hmult : degreeSequenceMultiplicity H0 = 3) :
    (H0.comap (ULift.down : ULift.{u} γ → γ)).CliqueFree 3 ∧
      degreeSequenceMultiplicity (H0.comap (ULift.down : ULift.{u} γ → γ)) = 3 := by
  let H : SimpleGraph (ULift.{u} γ) := H0.comap ULift.down
  have hcf' : H.CliqueFree 3 := by
    intro c hc
    refine hcf (c.image ULift.down) ⟨?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_image, Set.mem_image] at hx hy
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      exact hc.1 hu hv (fun huv => hxy (congrArg ULift.down huv))
    · rw [Finset.card_image_of_injective _ ULift.down_injective, hc.2]
  refine ⟨hcf', ?_⟩
  have hdeg : ∀ v : ULift.{u} γ, H.degree v = H0.degree v.down := by
    intro v
    rw [SimpleGraph.degree, SimpleGraph.degree]
    refine Finset.card_bij (fun w _ => w.down)
      (fun w hw => (mem_neighborFinset H0 v.down w.down).mpr ((mem_neighborFinset H v w).mp hw))
      (fun _ _ _ _ h => ULift.ext _ _ h)
      (fun w hw => ⟨ULift.up w, (mem_neighborFinset H v (ULift.up w)).mpr
        ((mem_neighborFinset H0 v.down w).mp hw), rfl⟩)
  have hds : degreeSequence H = degreeSequence H0 := by
    unfold degreeSequence
    congr 1
    have hmap : Finset.univ.val.map (fun v : ULift.{u} γ => H.degree v) =
        Finset.univ.val.map (fun w : γ => H0.degree w) := by
      have heq : (Finset.univ : Finset (ULift.{u} γ)).val =
          (Finset.univ : Finset γ).val.map ULift.up := by
        rw [← Finset.image_val_of_injOn (fun _ _ _ _ h => ULift.up.inj h)]
        congr 1
        ext v
        simp
      rw [heq, Multiset.map_map]
      exact Multiset.map_congr rfl fun w _ => hdeg (ULift.up w)
    exact hmap
  unfold degreeSequenceMultiplicity at hmult ⊢
  rw [hds]
  exact hmult

end Theorem2EFSProof

theorem OMA.solution : type_of% @SimpleGraph.theorem2 := by
  intro α _ _ G _ h_conn h
  let n : ℕ := Fintype.card α
  have hn : 1 ≤ n := Fintype.card_pos_iff.mpr h_conn.nonempty
  let e : Fin n ≃ α := (Fintype.equivFin α).symm
  let G0 : SimpleGraph (Fin n) := G.comap e
  have hG0_cf : G0.CliqueFree 3 := by
    intro c hc
    refine h (c.image e) ⟨?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_image, Set.mem_image] at hx hy
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      exact hc.1 hu hv (fun huv => hxy (congrArg e huv))
    · rw [Finset.card_image_of_injective _ e.injective, hc.2]
  obtain ⟨M, H0, hdec0, h_emb0, hH0_cf, hH0_mult⟩ :=
    Theorem2EFSProof.exists_fin_extension hn G0 hG0_cf
  let H : SimpleGraph (ULift (Fin n ⊕ (Fin M ⊕ Fin M))) := H0.comap ULift.down
  let : DecidableRel H.Adj := fun x y => hdec0 x.down y.down
  have htrans := Theorem2EFSProof.transfer_to_ulift H0 hH0_cf hH0_mult
  let emb : G ↪g H :=
    { toFun := fun u => ULift.up (Sum.inl (e.symm u))
      inj' := fun u v huv => e.symm.injective (Sum.inl.inj (ULift.up.inj huv))
      map_rel_iff' := fun {u v} => by
        change H0.Adj (Sum.inl (e.symm u)) (Sum.inl (e.symm v)) ↔ G.Adj u v
        rw [h_emb0]
        change G.Adj (e (e.symm u)) (e (e.symm v)) ↔ G.Adj u v
        simp }
  exact ⟨ULift (Fin n ⊕ (Fin M ⊕ Fin M)), inferInstance, H, inferInstance, emb, htrans.1, htrans.2⟩
