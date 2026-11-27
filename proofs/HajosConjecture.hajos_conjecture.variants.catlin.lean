import FormalConjectures.Wikipedia.HajosConjecture

/-!
# Catlin's Counterexamples to Hajós' Conjecture for All `k ≥ 7`

For every `k ≥ 7`, write `k = 7 + m` (`m = k - 7`) and let `H_m = G_13 ∨ K_m` be the join of the
13-vertex `C_5`-blowup `G_13 = C_5(3, 3, 2, 3, 2)` with the complete graph `K_m` on `Fin m`:

1. Every independent set in `G_13` has size at most `2` (since `α(C_5) = 2` and each cluster is
   a clique). In any `(6 + m)`-coloring of `H_m`, the `m` universal vertices of `K_m` consume `m`
   distinct colors unavailable to `G_13`, leaving at most `6` colors for `13 > 6 * 2` vertices,
   contradiction. Thus `k ≤ H_m.chromaticNumber`.
2. Suppose `H_m` contains a subdivision of `K_{7 + m}` on branch set `B` (`|R| = |V \ B| = 6`).
   Let `n i` be the number of branch vertices in cluster `i : Fin 5` of `G_13` (`n i ≤ c i`) and
   `t = |Fin m \ B|` (`∑ n i = 7 + t`). Disjointness of internal vertices of the non-adjacent
   branch pairs `B_i × B_{i+2}` gives:
   - Weighted internal-vertex bound:
     `∑ i, (2 * n i * n (i + 2) - min (n i * n (i + 2)) (c (i + 1) - n (i + 1))) ≤ 6 + t`.
   - Vertex-cut bound: whenever `n (i + 1) = c (i + 1)`, every `B_i`-to-`B_{i+2}` path avoiding
     `Fin m \ B` exits through both cluster `i + 4` and cluster `i + 3`, giving
     `n i * n (i + 2) ≤ t + (c (i + 4) - n (i + 4))` and
     `n i * n (i + 2) ≤ t + (c (i + 3) - n (i + 3))`.
   A finite check over the 576 tuples `n ≤ (3, 3, 2, 3, 2)` rules out all possibilities.
-/

-- Problem: Catlin (1979): counterexamples for every $k \ge 7$.
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/HajosConjecture.lean:108 (declaration HajosConjecture.hajos_conjecture.variants.catlin)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace HajosCatlinProof

open SimpleGraph Finset

/- ### Section 1: Graph definition `G_13 ∨ K_m` and finite checks -/

private def c13 : Fin 5 → ℕ
  | 0 => 3
  | 1 => 3
  | 2 => 2
  | 3 => 3
  | 4 => 2

private abbrev V13 := { p : Fin 5 × Fin 3 // p.2.1 < c13 p.1 }

private def g13Adj (u v : V13) : Prop :=
  (u.1.1 = v.1.1 ∧ u.1.2 ≠ v.1.2) ∨ u.1.1 - v.1.1 = 1 ∨ v.1.1 - u.1.1 = 1

private instance : DecidableRel g13Adj := fun u v =>
  inferInstanceAs
    (Decidable ((u.1.1 = v.1.1 ∧ u.1.2 ≠ v.1.2) ∨ u.1.1 - v.1.1 = 1 ∨ v.1.1 - u.1.1 = 1))

private def joinAdj (m : ℕ) (x y : V13 ⊕ Fin m) : Prop :=
  match x, y with
  | Sum.inl u, Sum.inl v => g13Adj u v
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True
  | Sum.inr j₁, Sum.inr j₂ => j₁ ≠ j₂

private instance (m : ℕ) : DecidableRel (joinAdj m) := fun x y => by
  cases x with
  | inl u =>
    cases y with
    | inl v => exact inferInstanceAs (Decidable (g13Adj u v))
    | inr _ => exact isTrue trivial
  | inr j₁ =>
    cases y with
    | inl _ => exact isTrue trivial
    | inr j₂ => exact inferInstanceAs (Decidable (j₁ ≠ j₂))

private def Hm (m : ℕ) : SimpleGraph (V13 ⊕ Fin m) where
  Adj := joinAdj m
  symm := ⟨fun x y h => by
    cases x with
    | inl u =>
      cases y with
      | inl v =>
        rcases h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
      | inr _ => exact trivial
    | inr j₁ =>
      cases y with
      | inl _ => exact trivial
      | inr j₂ => exact Ne.symm h⟩
  loopless := ⟨fun x h => by
    cases x with
    | inl u =>
      rcases h with ⟨_, h2⟩ | h | h
      · exact h2 rfl
      · rw [sub_self] at h; exact absurd h (by decide)
      · rw [sub_self] at h; exact absurd h (by decide)
    | inr j => exact h rfl⟩

private instance (m : ℕ) : DecidableRel (Hm m).Adj := fun x y =>
  inferInstanceAs (Decidable (joinAdj m x y))

private lemma card_V13 : Fintype.card V13 = 13 := by decide

private lemma cluster_card_V13 :
    ∀ i : Fin 5, (Finset.univ.filter (fun v : V13 => v.1.1 = i)).card = c13 i := by
  decide

private lemma c5_no_three_indep_aux :
    ∀ a b c : Fin 5,
      ¬ (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
         a - b ≠ 1 ∧ b - a ≠ 1 ∧
         a - c ≠ 1 ∧ c - a ≠ 1 ∧
         b - c ≠ 1 ∧ c - b ≠ 1) := by
  decide

private lemma c5_dist2_not_adj :
    ∀ i : Fin 5, i ≠ i + 2 ∧ i - (i + 2) ≠ 1 ∧ (i + 2) - i ≠ 1 := by
  decide

private lemma c5_common_nb_cluster_aux :
    ∀ i x : Fin 5,
      ¬ ((i = x ∨ i - x = 1 ∨ x - i = 1) ∧
         (x = i + 2 ∨ x - (i + 2) = 1 ∨ (i + 2) - x = 1) ∧
         x ≠ i + 1) := by
  decide

private lemma c5_common_nb_cluster (i x : Fin 5)
    (h1 : i = x ∨ i - x = 1 ∨ x - i = 1)
    (h2 : x = i + 2 ∨ x - (i + 2) = 1 ∨ (i + 2) - x = 1) : x = i + 1 := by
  by_contra hne
  exact c5_common_nb_cluster_aux i x ⟨h1, h2, hne⟩

private lemma c5_pair_unique_aux :
    ∀ i j : Fin 5, ¬ (i = j + 2 ∧ i + 2 = j) := by
  decide

private lemma c5_exit_i_aux :
    ∀ i y : Fin 5,
      ¬ ((i = y ∨ i - y = 1 ∨ y - i = 1) ∧ y ≠ i ∧ y ≠ i + 1 ∧ y ≠ i + 4) := by
  decide

private lemma c5_exit_i_i4_aux :
    ∀ i x y : Fin 5,
      ¬ ((x = i ∨ x = i + 4) ∧
         (x = y ∨ x - y = 1 ∨ y - x = 1) ∧
         y ≠ i ∧ y ≠ i + 4 ∧ y ≠ i + 1 ∧ y ≠ i + 3) := by
  decide

private lemma c5_i4_not_adj_i2 :
    ∀ i : Fin 5, i + 4 ≠ i + 2 ∧ (i + 4) - (i + 2) ≠ 1 ∧ (i + 2) - (i + 4) ≠ 1 := by
  decide

private lemma c5_i3_ne_i2 : ∀ i : Fin 5, i + 3 ≠ i + 2 ∧ i + 4 ≠ i + 2 := by
  decide

private lemma catlin_tuple_impossible :
    ∀ (n0 : Fin 4) (n1 : Fin 4) (n2 : Fin 3) (n3 : Fin 4) (n4 : Fin 3),
      ¬ (7 ≤ n0.1 + n1.1 + n2.1 + n3.1 + n4.1 ∧
         (2 * (n0.1 * n2.1) - min (n0.1 * n2.1) (3 - n1.1)) +
         (2 * (n1.1 * n3.1) - min (n1.1 * n3.1) (2 - n2.1)) +
         (2 * (n2.1 * n4.1) - min (n2.1 * n4.1) (3 - n3.1)) +
         (2 * (n3.1 * n0.1) - min (n3.1 * n0.1) (2 - n4.1)) +
         (2 * (n4.1 * n1.1) - min (n4.1 * n1.1) (3 - n0.1)) ≤
           6 + (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) ∧
         (n1.1 = 3 → n0.1 * n2.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (2 - n4.1) ∧
                      n0.1 * n2.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (3 - n3.1)) ∧
         (n2.1 = 2 → n1.1 * n3.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (3 - n0.1) ∧
                      n1.1 * n3.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (2 - n4.1)) ∧
         (n3.1 = 3 → n2.1 * n4.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (3 - n1.1) ∧
                      n2.1 * n4.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (3 - n0.1)) ∧
         (n4.1 = 2 → n3.1 * n0.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (2 - n2.1) ∧
                      n3.1 * n0.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (3 - n1.1)) ∧
         (n0.1 = 3 → n4.1 * n1.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (3 - n3.1) ∧
                      n4.1 * n1.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (2 - n2.1))) := by
  decide

/- ### Section 2: `7 + m ≤ (Hm m).chromaticNumber` -/

private lemma indep_card_le_two (S : Finset V13)
    (hind : ∀ u ∈ S, ∀ v ∈ S, ¬ g13Adj u v) : S.card ≤ 2 := by
  by_contra hgt
  have h3 : 3 ≤ S.card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hS1 : (S.erase u).card = S.card - 1 := Finset.card_erase_of_mem hu
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (S.erase u).card)
  have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
  have hvS : v ∈ S := (Finset.mem_erase.mp hv).2
  have hS2 : ((S.erase u).erase v).card = (S.erase u).card - 1 := Finset.card_erase_of_mem hv
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < ((S.erase u).erase v).card)
  have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
  have hwu : w ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
  have hwS : w ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).2
  have extract : ∀ x y : V13, x ≠ y → ¬ g13Adj x y →
      x.1.1 ≠ y.1.1 ∧ x.1.1 - y.1.1 ≠ 1 ∧ y.1.1 - x.1.1 ≠ 1 := by
    intro x y hne hna
    refine ⟨fun h1 => hna (Or.inl ⟨h1, fun h2 => hne (Subtype.ext (Prod.ext h1 h2))⟩),
      fun h => hna (Or.inr (Or.inl h)), fun h => hna (Or.inr (Or.inr h))⟩
  obtain ⟨huv1, huv2, huv3⟩ := extract u v hvu.symm (hind u hu v hvS)
  obtain ⟨huw1, huw2, huw3⟩ := extract u w hwu.symm (hind u hu w hwS)
  obtain ⟨hvw1, hvw2, hvw3⟩ := extract v w hwv.symm (hind v hvS w hwS)
  exact c5_no_three_indep_aux u.1.1 v.1.1 w.1.1
    ⟨huv1, huw1, hvw1, huv2, huv3, huw2, huw3, hvw2, hvw3⟩

private lemma chromaticNumber_Hm_ge (m : ℕ) : ((7 + m : ℕ) : ℕ∞) ≤ (Hm m).chromaticNumber := by
  by_contra hlt
  have hle : (Hm m).chromaticNumber ≤ ((6 + m : ℕ) : ℕ∞) := by
    cases hcn : (Hm m).chromaticNumber with
    | top =>
      rw [hcn] at hlt
      exact absurd le_top hlt
    | coe r =>
      rw [hcn] at hlt
      have hr : r < 7 + m := by
        by_contra hge
        exact hlt (Nat.cast_le.mpr (by omega : 7 + m ≤ r))
      exact Nat.cast_le.mpr (by omega : r ≤ 6 + m)
  obtain ⟨col⟩ := SimpleGraph.chromaticNumber_le_iff_colorable.mp hle
  let colK : Finset (Fin (6 + m)) := Finset.univ.image (fun j : Fin m => col (Sum.inr j))
  let colG : Finset (Fin (6 + m)) := Finset.univ \ colK
  have hcolK_inj : Function.Injective (fun j : Fin m => col (Sum.inr j)) := by
    intro j₁ j₂ heq
    by_contra hne
    exact col.valid (show (Hm m).Adj (Sum.inr j₁) (Sum.inr j₂) from hne) heq
  have hcolK_card : colK.card = m := by
    rw [Finset.card_image_of_injective _ hcolK_inj, Finset.card_univ, Fintype.card_fin]
  have hcolG_card : colG.card = 6 := by
    have hu := Finset.card_union_of_disjoint (Finset.disjoint_sdiff : Disjoint colK (Finset.univ \ colK))
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ colK), Finset.card_univ, Fintype.card_fin,
      hcolK_card] at hu
    change (Finset.univ \ colK).card = 6
    omega
  have hG_in_colG : ∀ v : V13, col (Sum.inl v) ∈ colG := by
    intro v
    simp only [colG, colK, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image]
    rintro ⟨j, hj⟩
    exact col.valid (show (Hm m).Adj (Sum.inr j) (Sum.inl v) from trivial) hj
  have hpart : (Finset.univ : Finset V13) =
      colG.biUnion (fun t => Finset.univ.filter (fun v : V13 => col (Sum.inl v) = t)) := by
    ext v
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, true_iff]
    exact ⟨col (Sum.inl v), hG_in_colG v, rfl⟩
  have hdisj : Set.PairwiseDisjoint (colG : Set (Fin (6 + m)))
      (fun t => Finset.univ.filter (fun v : V13 => col (Sum.inl v) = t)) := by
    intro t₁ _ t₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hne (h1.symm.trans h2)
  have hsum : 13 = ∑ t ∈ colG, (Finset.univ.filter (fun v : V13 => col (Sum.inl v) = t)).card := by
    calc 13 = (Finset.univ : Finset V13).card := by rw [Finset.card_univ, card_V13]
      _ = (colG.biUnion (fun t => Finset.univ.filter (fun v : V13 => col (Sum.inl v) = t))).card := by
          rw [← hpart]
      _ = _ := Finset.card_biUnion hdisj
  have hle12 : ∑ t ∈ colG, (Finset.univ.filter (fun v : V13 => col (Sum.inl v) = t)).card ≤ 12 := by
    calc ∑ t ∈ colG, (Finset.univ.filter (fun v : V13 => col (Sum.inl v) = t)).card
        ≤ ∑ _t ∈ colG, 2 := by
          refine Finset.sum_le_sum fun t _ => indep_card_le_two _ fun u hu v hv huv => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
          exact col.valid (show (Hm m).Adj (Sum.inl u) (Sum.inl v) from huv) (hu.trans hv.symm)
      _ = colG.card * 2 := by rw [Finset.sum_const, smul_eq_mul]
      _ = 12 := by rw [hcolG_card]
  omega

/- ### Section 3: Walk exit and internal-vertex helpers -/

private lemma walk_support_getLast? {V : Type*} {G : SimpleGraph V} :
    ∀ {a b : V} (w : G.Walk a b), w.support.getLast? = some b := by
  intro a b w
  induction w with
  | nil => simp
  | cons _ w' ih =>
    rw [SimpleGraph.Walk.support_cons, List.getLast?_cons_of_ne_nil (SimpleGraph.Walk.support_ne_nil w')]
    exact ih

private lemma mem_dropLast_of_ne_getLast {α : Type*} :
    ∀ (l : List α) (y b : α), l.getLast? = some b → y ∈ l → y ≠ b → y ∈ l.dropLast := by
  intro l
  induction l with
  | nil => intro _ _ _ h; simp at h
  | cons a tl ih =>
    intro y b hlast hy hne
    cases tl with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      simp only [List.mem_singleton] at hy
      exact absurd (hy.trans hlast) hne
    | cons a' tl' =>
      rw [List.dropLast_cons_of_ne_nil (by simp)]
      rw [List.mem_cons] at hy ⊢
      rcases hy with rfl | htl
      · exact Or.inl rfl
      · right
        apply ih y b _ htl hne
        simpa using hlast

private lemma walk_first_exit {V : Type*} {G : SimpleGraph V} (Q : V → Prop) :
    ∀ {a b : V} (w : G.Walk a b), Q a → ¬ Q b →
      ∃ x y : V, G.Adj x y ∧ Q x ∧ ¬ Q y ∧ y ∈ w.support.tail := by
  intro a b w
  induction w with
  | nil => intro ha hna; exact absurd ha hna
  | @cons u v z huv w' ih =>
    intro hu hnz
    by_cases hv : Q v
    · obtain ⟨x, y, hxy, hQx, hQy, hy⟩ := ih hv hnz
      refine ⟨x, y, hxy, hQx, hQy, ?_⟩
      simp only [SimpleGraph.Walk.support_cons, List.tail_cons]
      exact List.mem_of_mem_tail hy
    · refine ⟨u, v, huv, hu, hv, ?_⟩
      simp only [SimpleGraph.Walk.support_cons, List.tail_cons]
      exact SimpleGraph.Walk.start_mem_support w'

private lemma walk_tail_getLast?_of_ne {V : Type*} {G : SimpleGraph V} {a b : V}
    (w : G.Walk a b) (hne : a ≠ b) : w.support.tail.getLast? = some b := by
  cases w with
  | nil => exact absurd rfl hne
  | cons _ w' =>
    simp only [SimpleGraph.Walk.support_cons, List.tail_cons]
    exact walk_support_getLast? w'

private lemma internal_card_ge_one {m : ℕ} {u v : V13 ⊕ Fin m} (hne : u ≠ v)
    (hna : ¬ (Hm m).Adj u v) (w : (Hm m).Walk u v) (hw : w.IsPath) :
    1 ≤ (w.support.tail.dropLast).toFinset.card := by
  have hnodup : (w.support.tail.dropLast).Nodup :=
    hw.support_nodup.sublist ((List.dropLast_sublist _).trans (List.tail_sublist _))
  rw [List.toFinset_card_of_nodup hnodup, List.length_dropLast, List.length_tail,
    SimpleGraph.Walk.length_support]
  cases w with
  | nil => exact absurd rfl hne
  | cons hadj w' =>
    cases w' with
    | nil => exact absurd hadj hna
    | cons _ _ => simp

private lemma internal_card_ge_two_of_no_mid {m : ℕ} {u v : V13 ⊕ Fin m} (hne : u ≠ v)
    (hna : ¬ (Hm m).Adj u v) (w : (Hm m).Walk u v) (hw : w.IsPath)
    (hno_mid : ∀ z, z ∈ w.support.tail.dropLast → ¬ ((Hm m).Adj u z ∧ (Hm m).Adj z v)) :
    2 ≤ (w.support.tail.dropLast).toFinset.card := by
  have hnodup : (w.support.tail.dropLast).Nodup :=
    hw.support_nodup.sublist ((List.dropLast_sublist _).trans (List.tail_sublist _))
  rw [List.toFinset_card_of_nodup hnodup, List.length_dropLast, List.length_tail,
    SimpleGraph.Walk.length_support]
  cases w with
  | nil => exact absurd rfl hne
  | @cons _ x _ hux w' =>
    cases w' with
    | nil => exact absurd hux hna
    | @cons _ y _ hxy w'' =>
      cases w'' with
      | nil =>
        exfalso
        refine hno_mid x ?_ ⟨hux, hxy⟩
        simp
      | cons _ _ => simp

/- ### Section 4: No `K_{7 + m}` subdivision in `Hm m` -/

private lemma no_subdivision_aux (m : ℕ)
    (f : Fin (7 + m) → V13 ⊕ Fin m)
    (P : ∀ w w', (completeGraph (Fin (7 + m))).Adj w w' → (Hm m).Walk (f w) (f w'))
    (hM : HajosConjecture.IsSubdivisionModel (completeGraph (Fin (7 + m))) (Hm m) f P)
    (B R : Finset (V13 ⊕ Fin m)) (hB : B = Finset.univ.image f) (hR : R = Finset.univ \ B)
    (BG RG : Finset V13)
    (hBG : BG = Finset.univ.filter (fun v : V13 => Sum.inl v ∈ B))
    (hRG : RG = Finset.univ \ BG)
    (BK RK : Finset (Fin m))
    (hBK : BK = Finset.univ.filter (fun j : Fin m => Sum.inr j ∈ B))
    (hRK : RK = Finset.univ \ BK)
    (Bi : Fin 5 → Finset V13) (hBi : ∀ i, Bi i = BG.filter (fun v => v.1.1 = i))
    (preFun : V13 → Fin (7 + m)) (hf_pre : ∀ v ∈ BG, f (preFun v) = Sum.inl v) :
    False := by
  classical
  have hB_card : B.card = 7 + m := by
    rw [hB, Finset.card_image_of_injective _ hM.injective, Finset.card_univ, Fintype.card_fin]
  have hV_card : (Finset.univ : Finset (V13 ⊕ Fin m)).card = 13 + m := by
    rw [Finset.card_univ, Fintype.card_sum, card_V13, Fintype.card_fin]
  have hR_card : R.card = 6 := by
    have hu := Finset.card_union_of_disjoint (Finset.disjoint_sdiff : Disjoint B (Finset.univ \ B))
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ B), hV_card, hB_card, ← hR] at hu
    omega
  have hB_split : B.card = BG.card + BK.card := by
    let B1 : Finset (V13 ⊕ Fin m) := BG.image Sum.inl
    let B2 : Finset (V13 ⊕ Fin m) := BK.image Sum.inr
    have hu : B = B1 ∪ B2 := by
      ext x
      simp only [B1, B2, Finset.mem_union, Finset.mem_image, hBG, hBK, Finset.mem_filter,
        Finset.mem_univ, true_and]
      cases x with
      | inl v => simp
      | inr j => simp
    have hd : Disjoint B1 B2 := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨_, _, h⟩ := Finset.mem_image.mp h2
      exact absurd h (by simp)
    rw [hu, Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective]
  have hK_split : BK.card + RK.card = m := by
    have hu := Finset.card_union_of_disjoint (Finset.disjoint_sdiff : Disjoint BK (Finset.univ \ BK))
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ BK), Finset.card_univ, Fintype.card_fin,
      ← hRK] at hu
    exact hu.symm
  have hBG_ge7 : 7 ≤ BG.card := by omega
  have ht_eq : RK.card = BG.card - 7 := by omega
  have hRG_mem : ∀ v : V13, v ∈ RG ↔ Sum.inl v ∈ R := by
    intro v
    rw [hRG, hR, Finset.mem_sdiff, Finset.mem_sdiff, hBG, Finset.mem_filter]
    simp
  have hRK_mem : ∀ j : Fin m, j ∈ RK ↔ Sum.inr j ∈ R := by
    intro j
    rw [hRK, hR, Finset.mem_sdiff, Finset.mem_sdiff, hBK, Finset.mem_filter]
    simp
  have hn_le : ∀ i : Fin 5, (Bi i).card ≤ c13 i := by
    intro i
    calc (Bi i).card
        ≤ (Finset.univ.filter (fun v : V13 => v.1.1 = i)).card :=
          Finset.card_le_card fun v hv => by
            rw [hBi i] at hv
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
            exact hv.2
      _ = c13 i := cluster_card_V13 i
  have hRG_cl_card : ∀ i : Fin 5, (RG.filter (fun v : V13 => v.1.1 = i)).card = c13 i - (Bi i).card := by
    intro i
    let Cl : Finset V13 := Finset.univ.filter (fun v : V13 => v.1.1 = i)
    have hu : Bi i ∪ RG.filter (fun v : V13 => v.1.1 = i) = Cl := by
      ext v
      simp only [Cl, Finset.mem_union, hBi i, hRG, Finset.mem_filter, Finset.mem_sdiff,
        Finset.mem_univ, true_and]
      tauto
    have hd : Disjoint (Bi i) (RG.filter (fun v : V13 => v.1.1 = i)) := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      rw [hBi i, Finset.mem_filter] at h1
      rw [Finset.mem_filter, hRG, Finset.mem_sdiff] at h2
      exact h2.1.2 h1.1
    have hcard := Finset.card_union_of_disjoint hd
    rw [hu, cluster_card_V13 i] at hcard
    omega
  have hBG_eq_biUnion : BG = (Finset.univ : Finset (Fin 5)).biUnion Bi := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, hBi, Finset.mem_filter]
    exact ⟨fun hv => ⟨v.1.1, hv, rfl⟩, fun ⟨_, hv, _⟩ => hv⟩
  have hBi_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 5)) Bi := by
    intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro v h1 h2
    rw [hBi i, Finset.mem_filter] at h1
    rw [hBi j, Finset.mem_filter] at h2
    exact hij (h1.2.symm.trans h2.2)
  have hn_sum : ∑ i : Fin 5, (Bi i).card = BG.card := by
    rw [hBG_eq_biUnion, Finset.card_biUnion hBi_disj]
  -- Build AllPairs and intSet
  let AllPairs : Finset (Σ i : Fin 5, V13 × V13) :=
    (Finset.univ : Finset (Fin 5)).sigma (fun i => Bi i ×ˢ Bi (i + 2))
  have hpair_mem : ∀ p ∈ AllPairs,
      (p.2.1 ∈ BG ∧ p.2.1.1.1 = p.1) ∧ (p.2.2 ∈ BG ∧ p.2.2.1.1 = p.1 + 2) := by
    intro p hp
    simp only [AllPairs, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_product, hBi,
      Finset.mem_filter] at hp
    exact hp
  have hpair_ne : ∀ p ∈ AllPairs, preFun p.2.1 ≠ preFun p.2.2 := by
    intro p hp heq
    obtain ⟨⟨huB, hu1⟩, ⟨hvB, hv1⟩⟩ := hpair_mem p hp
    have hveq : p.2.1 = p.2.2 := Sum.inl.inj (by rw [← hf_pre p.2.1 huB, ← hf_pre p.2.2 hvB, heq])
    have hcl : p.1 = p.1 + 2 := hu1.symm.trans ((congrArg (fun z : V13 => z.1.1) hveq).trans hv1)
    exact (c5_dist2_not_adj p.1).1 hcl
  let intSet : (Σ i : Fin 5, V13 × V13) → Finset (V13 ⊕ Fin m) := fun p =>
    if h : preFun p.2.1 ≠ preFun p.2.2 then
      ((P (preFun p.2.1) (preFun p.2.2) h).support.tail.dropLast).toFinset
    else ∅
  have hint_sub : ∀ p ∈ AllPairs, intSet p ⊆ R := by
    intro p hp x hx
    have hne := hpair_ne p hp
    dsimp only [intSet] at hx
    rw [dif_pos hne, List.mem_toFinset] at hx
    have hnot : x ∉ Set.range f := hM.internal_avoid _ _ hne x hx
    rw [hR, Finset.mem_sdiff]
    refine ⟨Finset.mem_univ x, fun hxB => ?_⟩
    rw [hB] at hxB
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxB
    exact hnot ⟨a, rfl⟩
  have hint_disj : Set.PairwiseDisjoint (AllPairs : Set (Σ i : Fin 5, V13 × V13)) intSet := by
    intro p₁ hp₁ p₂ hp₂ hne
    dsimp only [Function.onFun]
    have hne1 := hpair_ne p₁ hp₁
    have hne2 := hpair_ne p₂ hp₂
    have hsym_ne : s(preFun p₁.2.1, preFun p₁.2.2) ≠ s(preFun p₂.2.1, preFun p₂.2.2) := by
      intro hsym
      obtain ⟨⟨hu1B, hu1c⟩, ⟨hv1B, hv1c⟩⟩ := hpair_mem p₁ hp₁
      obtain ⟨⟨hu2B, hu2c⟩, ⟨hv2B, hv2c⟩⟩ := hpair_mem p₂ hp₂
      rw [Sym2.eq_iff] at hsym
      rcases hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hv1 : p₁.2.1 = p₂.2.1 :=
          Sum.inl.inj (by rw [← hf_pre p₁.2.1 hu1B, ← hf_pre p₂.2.1 hu2B, h1])
        have hv2 : p₁.2.2 = p₂.2.2 :=
          Sum.inl.inj (by rw [← hf_pre p₁.2.2 hv1B, ← hf_pre p₂.2.2 hv2B, h2])
        have hi : p₁.1 = p₂.1 := hu1c.symm.trans ((congrArg (fun z : V13 => z.1.1) hv1).trans hu2c)
        rcases p₁ with ⟨i₁, ⟨u₁, v₁⟩⟩
        rcases p₂ with ⟨i₂, ⟨u₂, v₂⟩⟩
        dsimp at hi hv1 hv2
        subst hi; subst hv1; subst hv2
        exact hne rfl
      · have hv1 : p₁.2.1 = p₂.2.2 :=
          Sum.inl.inj (by rw [← hf_pre p₁.2.1 hu1B, ← hf_pre p₂.2.2 hv2B, h1])
        have hv2 : p₁.2.2 = p₂.2.1 :=
          Sum.inl.inj (by rw [← hf_pre p₁.2.2 hv1B, ← hf_pre p₂.2.1 hu2B, h2])
        have hc1 : p₁.1 = p₂.1 + 2 := hu1c.symm.trans ((congrArg (fun z : V13 => z.1.1) hv1).trans hv2c)
        have hc2 : p₁.1 + 2 = p₂.1 := hv1c.symm.trans ((congrArg (fun z : V13 => z.1.1) hv2).trans hu2c)
        exact c5_pair_unique_aux p₁.1 p₂.1 ⟨hc1, hc2⟩
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    dsimp only [intSet] at hx1 hx2
    rw [dif_pos hne1, List.mem_toFinset] at hx1
    rw [dif_pos hne2, List.mem_toFinset] at hx2
    exact hM.internal_disjoint _ _ hne1 _ _ hne2 hsym_ne x hx1 hx2
  have hsum_le_six : ∑ p ∈ AllPairs, (intSet p).card ≤ 6 := by
    rw [← hR_card, ← Finset.card_biUnion hint_disj]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr hint_sub)
  have hpair_na : ∀ p ∈ AllPairs, ¬ (Hm m).Adj (f (preFun p.2.1)) (f (preFun p.2.2)) := by
    intro p hp hadj
    obtain ⟨⟨huB, hu1⟩, ⟨hvB, hv1⟩⟩ := hpair_mem p hp
    rw [hf_pre p.2.1 huB, hf_pre p.2.2 hvB] at hadj
    rcases hadj with ⟨h1, _⟩ | h | h
    · rw [hu1, hv1] at h1; exact (c5_dist2_not_adj p.1).1 h1
    · rw [hu1, hv1] at h; exact (c5_dist2_not_adj p.1).2.1 h
    · rw [hu1, hv1] at h; exact (c5_dist2_not_adj p.1).2.2 h
  have hint_ge1 : ∀ p ∈ AllPairs, 1 ≤ (intSet p).card := by
    intro p hp
    have hne := hpair_ne p hp
    dsimp only [intSet]
    rw [dif_pos hne]
    exact internal_card_ge_one (fun h => hne (hM.injective h)) (hpair_na p hp)
      (P _ _ hne) (hM.isPath _ _ hne)
  -- Helper: any subset of AllPairs whose elements each hit a target set S has card ≤ S.card
  have hhit_card_le : ∀ {α : Type} [DecidableEq α] (U : Finset (Σ i : Fin 5, V13 × V13))
      (S : Finset α) (emb : α → V13 ⊕ Fin m),
      U ⊆ AllPairs → Function.Injective emb →
      (∀ p ∈ U, ∃ a ∈ S, emb a ∈ intSet p) → U.card ≤ S.card := by
    intro α _ U S emb hUsub hemb hhit
    have hpick : ∀ p : ↥U, ∃ a : α, a ∈ S ∧ emb a ∈ intSet p.1 := fun p => hhit p.1 p.2
    choose g hgS hgin using hpick
    have hinj : Function.Injective g := by
      intro p₁ p₂ heq
      by_contra hne
      have hpne : p₁.1 ≠ p₂.1 := fun h => hne (Subtype.ext h)
      have hdisj := hint_disj (hUsub p₁.2) (hUsub p₂.2) hpne
      exact Finset.disjoint_left.mp hdisj (hgin p₁) (heq ▸ hgin p₂)
    calc U.card = (Finset.univ : Finset ↥U).card := (Fintype.card_coe U).symm
      _ = ((Finset.univ : Finset ↥U).image g).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ S.card := Finset.card_le_card fun a ha => by
          obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
          exact hgS p
  -- Bound 1: Apex and Mid sets
  let Apex : Finset (Σ i : Fin 5, V13 × V13) :=
    AllPairs.filter (fun p => ∃ j : Fin m, Sum.inr j ∈ intSet p)
  have hApex_le : Apex.card ≤ RK.card := by
    refine hhit_card_le Apex RK Sum.inr (Finset.filter_subset _ _) Sum.inr_injective fun p hp => ?_
    simp only [Apex, Finset.mem_filter] at hp
    obtain ⟨j, hj⟩ := hp.2
    exact ⟨j, (hRK_mem j).mpr (hint_sub p hp.1 hj), hj⟩
  let Mid : Fin 5 → Finset (V13 × V13) := fun i =>
    (Bi i ×ˢ Bi (i + 2)).filter (fun q => ∃ x ∈ RG, x.1.1 = i + 1 ∧ Sum.inl x ∈ intSet ⟨i, q⟩)
  have hMid_le : ∀ i : Fin 5, (Mid i).card ≤ min ((Bi i).card * (Bi (i + 2)).card) (c13 (i + 1) - (Bi (i + 1)).card) := by
    intro i
    refine le_min ?_ ?_
    · calc (Mid i).card ≤ (Bi i ×ˢ Bi (i + 2)).card := Finset.card_filter_le _ _
        _ = (Bi i).card * (Bi (i + 2)).card := Finset.card_product _ _
    · let Ui : Finset (Σ j : Fin 5, V13 × V13) := (Mid i).image (fun q => ⟨i, q⟩)
      have hUi_card : Ui.card = (Mid i).card :=
        Finset.card_image_of_injective _ fun q₁ q₂ h => by
          cases h; rfl
      rw [← hUi_card, ← hRG_cl_card (i + 1)]
      refine hhit_card_le Ui (RG.filter (fun v : V13 => v.1.1 = i + 1)) Sum.inl ?_ Sum.inl_injective ?_
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        simp only [Mid, Finset.mem_filter] at hq
        simp only [AllPairs, Finset.mem_sigma, Finset.mem_univ, true_and]
        exact hq.1
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        simp only [Mid, Finset.mem_filter] at hq
        obtain ⟨x, hxRG, hxcl, hxin⟩ := hq.2
        exact ⟨x, Finset.mem_filter.mpr ⟨hxRG, hxcl⟩, hxin⟩
  have htwo_le : ∀ p ∈ AllPairs,
      2 ≤ (intSet p).card + (if p ∈ Apex then 1 else 0) + (if p.2 ∈ Mid p.1 then 1 else 0) := by
    intro p hp
    by_cases hA : p ∈ Apex
    · have := hint_ge1 p hp
      simp only [hA, ↓reduceIte]
      omega
    · by_cases hMd : p.2 ∈ Mid p.1
      · have := hint_ge1 p hp
        simp only [hA, hMd, ↓reduceIte]
        omega
      · simp only [hA, hMd, ↓reduceIte, add_zero]
        have hne := hpair_ne p hp
        dsimp only [intSet]
        rw [dif_pos hne]
        obtain ⟨⟨huB, hu1⟩, ⟨hvB, hv1⟩⟩ := hpair_mem p hp
        refine internal_card_ge_two_of_no_mid (fun h => hne (hM.injective h)) (hpair_na p hp)
          (P _ _ hne) (hM.isPath _ _ hne) fun z hz ⟨haz, hzb⟩ => ?_
        have hzin : z ∈ intSet p := by
          dsimp only [intSet]; rw [dif_pos hne, List.mem_toFinset]; exact hz
        cases z with
        | inr j =>
          exact hA (Finset.mem_filter.mpr ⟨hp, ⟨j, hzin⟩⟩)
        | inl x =>
          rw [hf_pre p.2.1 huB] at haz
          rw [hf_pre p.2.2 hvB] at hzb
          have hx1 : p.1 = x.1.1 ∨ p.1 - x.1.1 = 1 ∨ x.1.1 - p.1 = 1 := by
            rw [← hu1]
            rcases haz with ⟨h1, _⟩ | h | h
            · exact Or.inl h1
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          have hx2 : x.1.1 = p.1 + 2 ∨ x.1.1 - (p.1 + 2) = 1 ∨ (p.1 + 2) - x.1.1 = 1 := by
            rw [← hv1]
            rcases hzb with ⟨h1, _⟩ | h | h
            · exact Or.inl h1
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          have hxcl : x.1.1 = p.1 + 1 := c5_common_nb_cluster p.1 x.1.1 hx1 hx2
          have hxRG : x ∈ RG := (hRG_mem x).mpr (hint_sub p hp hzin)
          have hp2 : p.2 ∈ Bi p.1 ×ˢ Bi (p.1 + 2) := by
            simp only [AllPairs, Finset.mem_sigma, Finset.mem_univ, true_and] at hp
            exact hp
          exact hMd (Finset.mem_filter.mpr ⟨hp2, ⟨x, hxRG, hxcl, hzin⟩⟩)
  have hbound1 :
      ∑ i : Fin 5, (2 * ((Bi i).card * (Bi (i + 2)).card) -
          min ((Bi i).card * (Bi (i + 2)).card) (c13 (i + 1) - (Bi (i + 1)).card)) ≤
        6 + RK.card := by
    have hsum2 : ∑ p ∈ AllPairs, 2 ≤
        (∑ p ∈ AllPairs, (intSet p).card) +
        (∑ p ∈ AllPairs, if p ∈ Apex then 1 else 0) +
        (∑ p ∈ AllPairs, if p.2 ∈ Mid p.1 then 1 else 0) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum htwo_le
    have hlhs_eq : ∑ p ∈ AllPairs, 2 = ∑ i : Fin 5, 2 * ((Bi i).card * (Bi (i + 2)).card) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_const, Finset.card_product, smul_eq_mul, mul_comm]
    have hApex_sum : (∑ p ∈ AllPairs, if p ∈ Apex then 1 else 0) = Apex.card := by
      rw [← Finset.card_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1, h⟩⟩
    have hMid_sum : (∑ p ∈ AllPairs, if p.2 ∈ Mid p.1 then 1 else 0) = ∑ i : Fin 5, (Mid i).card := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.card_filter]
      congr 1
      ext q
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1, h⟩⟩
    have hMid_sum_le : ∑ i : Fin 5, (Mid i).card ≤
        ∑ i : Fin 5, min ((Bi i).card * (Bi (i + 2)).card) (c13 (i + 1) - (Bi (i + 1)).card) :=
      Finset.sum_le_sum fun i _ => hMid_le i
    have hsub_le : ∑ i : Fin 5, (2 * ((Bi i).card * (Bi (i + 2)).card) -
          min ((Bi i).card * (Bi (i + 2)).card) (c13 (i + 1) - (Bi (i + 1)).card)) +
        ∑ i : Fin 5, min ((Bi i).card * (Bi (i + 2)).card) (c13 (i + 1) - (Bi (i + 1)).card) =
        ∑ i : Fin 5, 2 * ((Bi i).card * (Bi (i + 2)).card) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : min ((Bi i).card * (Bi (i + 2)).card) (c13 (i + 1) - (Bi (i + 1)).card) ≤
          2 * ((Bi i).card * (Bi (i + 2)).card) := by
        have := min_le_left ((Bi i).card * (Bi (i + 2)).card) (c13 (i + 1) - (Bi (i + 1)).card)
        omega
      omega
    omega
  -- Bound 2: Vertex-cut bound when cluster i + 1 is full
  have hbound2 : ∀ i : Fin 5, (Bi (i + 1)).card = c13 (i + 1) →
      (Bi i).card * (Bi (i + 2)).card ≤ RK.card + (c13 (i + 4) - (Bi (i + 4)).card) ∧
      (Bi i).card * (Bi (i + 2)).card ≤ RK.card + (c13 (i + 3) - (Bi (i + 3)).card) := by
    intro i hfull
    have hRG_i1_empty : ∀ x ∈ RG, x.1.1 ≠ i + 1 := by
      intro x hx hxcl
      have h0 : (RG.filter (fun v : V13 => v.1.1 = i + 1)).card = 0 := by
        rw [hRG_cl_card (i + 1), hfull, Nat.sub_self]
      have hmem : x ∈ RG.filter (fun v : V13 => v.1.1 = i + 1) := Finset.mem_filter.mpr ⟨hx, hxcl⟩
      have hpos := Finset.card_pos.mpr ⟨x, hmem⟩
      omega
    let Qi : Finset (Σ j : Fin 5, V13 × V13) :=
      ((Bi i ×ˢ Bi (i + 2)).image (fun q => ⟨i, q⟩)).filter (fun p => p ∉ Apex)
    have hQi_sub : Qi ⊆ AllPairs := by
      intro p hp
      simp only [Qi, Finset.mem_filter, Finset.mem_image] at hp
      obtain ⟨q, hq, rfl⟩ := hp.1
      simp only [AllPairs, Finset.mem_sigma, Finset.mem_univ, true_and]
      exact hq
    have hQi_card : (Bi i).card * (Bi (i + 2)).card ≤ Qi.card + RK.card := by
      let Tot : Finset (Σ j : Fin 5, V13 × V13) := (Bi i ×ˢ Bi (i + 2)).image (fun q => ⟨i, q⟩)
      have hTot_card : Tot.card = (Bi i).card * (Bi (i + 2)).card := by
        rw [Finset.card_image_of_injective _ (fun q₁ q₂ h => by cases h; rfl), Finset.card_product]
      have hsplit : Tot.card = (Tot.filter (fun p => p ∉ Apex)).card +
          (Tot.filter (fun p => p ∈ Apex)).card := by
        rw [add_comm]
        exact (Finset.card_filter_add_card_filter_not (s := Tot) (p := fun p => p ∈ Apex)).symm
      have hleA : (Tot.filter (fun p => p ∈ Apex)).card ≤ Apex.card :=
        Finset.card_le_card fun p hp => (Finset.mem_filter.mp hp).2
      rw [← hTot_card]
      change Tot.card ≤ (Tot.filter (fun p => p ∉ Apex)).card + RK.card
      omega
    have hhit_i4 : ∀ p ∈ Qi, ∃ x ∈ RG.filter (fun v : V13 => v.1.1 = i + 4), Sum.inl x ∈ intSet p := by
      intro p hp
      have hpAll := hQi_sub hp
      have hpNotA : p ∉ Apex := (Finset.mem_filter.mp hp).2
      have hpi : p.1 = i := by
        simp only [Qi, Finset.mem_filter, Finset.mem_image] at hp
        obtain ⟨_, _, rfl⟩ := hp.1
        rfl
      have hne := hpair_ne p hpAll
      obtain ⟨⟨huB, hu1⟩, ⟨hvB, hv1⟩⟩ := hpair_mem p hpAll
      rw [hpi] at hu1 hv1
      let w := P (preFun p.2.1) (preFun p.2.2) hne
      let Q : V13 ⊕ Fin m → Prop := fun z => ∃ u : V13, z = Sum.inl u ∧ u.1.1 = i
      have hQa : Q (f (preFun p.2.1)) := ⟨p.2.1, hf_pre p.2.1 huB, hu1⟩
      have hQb : ¬ Q (f (preFun p.2.2)) := by
        rintro ⟨v', hv'eq, hv'1⟩
        rw [hf_pre p.2.2 hvB] at hv'eq
        have : p.2.2 = v' := Sum.inl.inj hv'eq
        rw [← this, hv1] at hv'1
        exact (c5_dist2_not_adj i).1 hv'1.symm
      obtain ⟨x, y, hxy, ⟨u, rfl, hucl⟩, hQy, hytail⟩ := walk_first_exit Q w hQa hQb
      have hy_ne_end : y ≠ f (preFun p.2.2) := by
        intro heq
        rw [heq, hf_pre p.2.2 hvB] at hxy
        rcases hxy with ⟨h1, _⟩ | h | h
        · rw [hucl, hv1] at h1; exact (c5_dist2_not_adj i).1 h1
        · rw [hucl, hv1] at h; exact (c5_dist2_not_adj i).2.1 h
        · rw [hucl, hv1] at h; exact (c5_dist2_not_adj i).2.2 h
      have hy_int : y ∈ w.support.tail.dropLast :=
        mem_dropLast_of_ne_getLast _ y (f (preFun p.2.2))
          (walk_tail_getLast?_of_ne w (fun h => hne (hM.injective h))) hytail hy_ne_end
      have hy_in : y ∈ intSet p := by
        dsimp only [intSet]; rw [dif_pos hne, List.mem_toFinset]; exact hy_int
      cases y with
      | inr j => exact absurd (Finset.mem_filter.mpr ⟨hpAll, ⟨j, hy_in⟩⟩) hpNotA
      | inl v =>
        have hvRG : v ∈ RG := (hRG_mem v).mpr (hint_sub p hpAll hy_in)
        have hv_ne_i : v.1.1 ≠ i := fun h => hQy ⟨v, rfl, h⟩
        have hv_ne_i1 : v.1.1 ≠ i + 1 := hRG_i1_empty v hvRG
        have hadj_cl : i = v.1.1 ∨ i - v.1.1 = 1 ∨ v.1.1 - i = 1 := by
          rw [← hucl]
          rcases hxy with ⟨h1, _⟩ | h | h
          · exact Or.inl h1
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        have hv_cl : v.1.1 = i + 4 := by
          by_contra hne4
          exact c5_exit_i_aux i v.1.1 ⟨hadj_cl, hv_ne_i, hv_ne_i1, hne4⟩
        exact ⟨v, Finset.mem_filter.mpr ⟨hvRG, hv_cl⟩, hy_in⟩
    have hhit_i3 : ∀ p ∈ Qi, ∃ x ∈ RG.filter (fun v : V13 => v.1.1 = i + 3), Sum.inl x ∈ intSet p := by
      intro p hp
      have hpAll := hQi_sub hp
      have hpNotA : p ∉ Apex := (Finset.mem_filter.mp hp).2
      have hpi : p.1 = i := by
        simp only [Qi, Finset.mem_filter, Finset.mem_image] at hp
        obtain ⟨_, _, rfl⟩ := hp.1
        rfl
      have hne := hpair_ne p hpAll
      obtain ⟨⟨huB, hu1⟩, ⟨hvB, hv1⟩⟩ := hpair_mem p hpAll
      rw [hpi] at hu1 hv1
      let w := P (preFun p.2.1) (preFun p.2.2) hne
      let Q' : V13 ⊕ Fin m → Prop := fun z => ∃ u : V13, z = Sum.inl u ∧ (u.1.1 = i ∨ u.1.1 = i + 4)
      have hQa : Q' (f (preFun p.2.1)) := ⟨p.2.1, hf_pre p.2.1 huB, Or.inl hu1⟩
      have hQb : ¬ Q' (f (preFun p.2.2)) := by
        rintro ⟨v', hv'eq, hv'1⟩
        rw [hf_pre p.2.2 hvB] at hv'eq
        have : p.2.2 = v' := Sum.inl.inj hv'eq
        rw [← this, hv1] at hv'1
        rcases hv'1 with h | h
        · exact (c5_dist2_not_adj i).1 h.symm
        · exact (c5_i4_not_adj_i2 i).1 h.symm
      obtain ⟨x, y, hxy, ⟨u, rfl, hucl⟩, hQy, hytail⟩ := walk_first_exit Q' w hQa hQb
      have hy_ne_end : y ≠ f (preFun p.2.2) := by
        intro heq
        rw [heq, hf_pre p.2.2 hvB] at hxy
        rcases hucl with hu0 | hu4
        · rcases hxy with ⟨h1, _⟩ | h | h
          · rw [hu0, hv1] at h1; exact (c5_dist2_not_adj i).1 h1
          · rw [hu0, hv1] at h; exact (c5_dist2_not_adj i).2.1 h
          · rw [hu0, hv1] at h; exact (c5_dist2_not_adj i).2.2 h
        · rcases hxy with ⟨h1, _⟩ | h | h
          · rw [hu4, hv1] at h1; exact (c5_i4_not_adj_i2 i).1 h1
          · rw [hu4, hv1] at h; exact (c5_i4_not_adj_i2 i).2.1 h
          · rw [hu4, hv1] at h; exact (c5_i4_not_adj_i2 i).2.2 h
      have hy_int : y ∈ w.support.tail.dropLast :=
        mem_dropLast_of_ne_getLast _ y (f (preFun p.2.2))
          (walk_tail_getLast?_of_ne w (fun h => hne (hM.injective h))) hytail hy_ne_end
      have hy_in : y ∈ intSet p := by
        dsimp only [intSet]; rw [dif_pos hne, List.mem_toFinset]; exact hy_int
      cases y with
      | inr j => exact absurd (Finset.mem_filter.mpr ⟨hpAll, ⟨j, hy_in⟩⟩) hpNotA
      | inl v =>
        have hvRG : v ∈ RG := (hRG_mem v).mpr (hint_sub p hpAll hy_in)
        have hv_ne_i : v.1.1 ≠ i := fun h => hQy ⟨v, rfl, Or.inl h⟩
        have hv_ne_i4 : v.1.1 ≠ i + 4 := fun h => hQy ⟨v, rfl, Or.inr h⟩
        have hv_ne_i1 : v.1.1 ≠ i + 1 := hRG_i1_empty v hvRG
        have hadj_cl : u.1.1 = v.1.1 ∨ u.1.1 - v.1.1 = 1 ∨ v.1.1 - u.1.1 = 1 := by
          rcases hxy with ⟨h1, _⟩ | h | h
          · exact Or.inl h1
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        have hv_cl : v.1.1 = i + 3 := by
          by_contra hne3
          exact c5_exit_i_i4_aux i u.1.1 v.1.1 ⟨hucl, hadj_cl, hv_ne_i, hv_ne_i4, hv_ne_i1, hne3⟩
        exact ⟨v, Finset.mem_filter.mpr ⟨hvRG, hv_cl⟩, hy_in⟩
    have hle4 : Qi.card ≤ c13 (i + 4) - (Bi (i + 4)).card := by
      rw [← hRG_cl_card (i + 4)]
      exact hhit_card_le Qi _ Sum.inl hQi_sub Sum.inl_injective hhit_i4
    have hle3 : Qi.card ≤ c13 (i + 3) - (Bi (i + 3)).card := by
      rw [← hRG_cl_card (i + 3)]
      exact hhit_card_le Qi _ Sum.inl hQi_sub Sum.inl_injective hhit_i3
    omega
  -- Apply the 576-tuple finite impossibility check
  let n0 : Fin 4 := ⟨(Bi 0).card, by have := hn_le 0; dsimp [c13] at this; omega⟩
  let n1 : Fin 4 := ⟨(Bi 1).card, by have := hn_le 1; dsimp [c13] at this; omega⟩
  let n2 : Fin 3 := ⟨(Bi 2).card, by have := hn_le 2; dsimp [c13] at this; omega⟩
  let n3 : Fin 4 := ⟨(Bi 3).card, by have := hn_le 3; dsimp [c13] at this; omega⟩
  let n4 : Fin 3 := ⟨(Bi 4).card, by have := hn_le 4; dsimp [c13] at this; omega⟩
  have hsum5 : n0.1 + n1.1 + n2.1 + n3.1 + n4.1 = BG.card := by
    have h5 : (∑ i : Fin 5, (Bi i).card) =
        (Bi 0).card + (Bi 1).card + (Bi 2).card + (Bi 3).card + (Bi 4).card := Fin.sum_univ_five _
    dsimp only [n0, n1, n2, n3, n4]
    omega
  have hb1_5 :
      (2 * (n0.1 * n2.1) - min (n0.1 * n2.1) (3 - n1.1)) +
      (2 * (n1.1 * n3.1) - min (n1.1 * n3.1) (2 - n2.1)) +
      (2 * (n2.1 * n4.1) - min (n2.1 * n4.1) (3 - n3.1)) +
      (2 * (n3.1 * n0.1) - min (n3.1 * n0.1) (2 - n4.1)) +
      (2 * (n4.1 * n1.1) - min (n4.1 * n1.1) (3 - n0.1)) ≤
        6 + (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) := by
    rw [Fin.sum_univ_five] at hbound1
    dsimp only [n0, n1, n2, n3, n4]
    rw [hsum5, ← ht_eq]
    exact hbound1
  have hb2_0 : n1.1 = 3 →
      n0.1 * n2.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (2 - n4.1) ∧
      n0.1 * n2.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (3 - n3.1) := by
    intro h; rw [hsum5, ← ht_eq]; exact hbound2 0 h
  have hb2_1 : n2.1 = 2 →
      n1.1 * n3.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (3 - n0.1) ∧
      n1.1 * n3.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (2 - n4.1) := by
    intro h; rw [hsum5, ← ht_eq]; exact hbound2 1 h
  have hb2_2 : n3.1 = 3 →
      n2.1 * n4.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (3 - n1.1) ∧
      n2.1 * n4.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (3 - n0.1) := by
    intro h; rw [hsum5, ← ht_eq]; exact hbound2 2 h
  have hb2_3 : n4.1 = 2 →
      n3.1 * n0.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (2 - n2.1) ∧
      n3.1 * n0.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (3 - n1.1) := by
    intro h; rw [hsum5, ← ht_eq]; exact hbound2 3 h
  have hb2_4 : n0.1 = 3 →
      n4.1 * n1.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (3 - n3.1) ∧
      n4.1 * n1.1 ≤ (n0.1 + n1.1 + n2.1 + n3.1 + n4.1 - 7) + (2 - n2.1) := by
    intro h; rw [hsum5, ← ht_eq]; exact hbound2 4 h
  exact catlin_tuple_impossible n0 n1 n2 n3 n4
    ⟨by omega, hb1_5, hb2_0, hb2_1, hb2_2, hb2_3, hb2_4⟩

private lemma no_subdivision_Hm (m : ℕ) :
    ¬ HajosConjecture.ContainsSubdivision (completeGraph (Fin (7 + m))) (Hm m) := by
  classical
  rintro ⟨f, P, hM⟩
  let B : Finset (V13 ⊕ Fin m) := Finset.univ.image f
  let BG : Finset V13 := Finset.univ.filter (fun v : V13 => Sum.inl v ∈ B)
  let BK : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => Sum.inr j ∈ B)
  let preFun : V13 → Fin (7 + m) := fun v =>
    if hv : Sum.inl v ∈ B then Classical.choose (Finset.mem_image.mp hv) else ⟨0, by omega⟩
  have hf_pre : ∀ v ∈ BG, f (preFun v) = Sum.inl v := fun v hv => by
    have hvB : Sum.inl v ∈ B := (Finset.mem_filter.mp hv).2
    simp only [preFun, dif_pos hvB]
    exact (Classical.choose_spec (Finset.mem_image.mp hvB)).2
  exact no_subdivision_aux m f P hM B (Finset.univ \ B) rfl rfl
    BG (Finset.univ \ BG) rfl rfl BK (Finset.univ \ BK) rfl rfl
    (fun i => BG.filter (fun v => v.1.1 = i)) (fun _ => rfl) preFun hf_pre

end HajosCatlinProof

theorem OMA.solution : type_of% @HajosConjecture.hajos_conjecture.variants.catlin := by
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = 7 + m := ⟨k - 7, by omega⟩
  exact ⟨HajosCatlinProof.V13 ⊕ Fin m, inferInstance, HajosCatlinProof.Hm m,
    HajosCatlinProof.chromaticNumber_Hm_ge m, HajosCatlinProof.no_subdivision_Hm m⟩
