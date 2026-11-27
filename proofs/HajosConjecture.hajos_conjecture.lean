import FormalConjectures.Wikipedia.HajosConjecture

/-!
# Counterexample to Hajós' Conjecture via Catlin's `C_5[K_3]`

We disprove Hajós' conjecture using Catlin's 15-vertex graph `G15 = C_5[K_3]` on `Fin 5 × Fin 3`
with `k = 8`:

1. Every independent set in `G15` has size at most `2` (as `α(C_5) = 2` and each cluster is a
   clique), so `G15` is not `7`-colorable (`7 * 2 < 15`), hence `8 ≤ G15.chromaticNumber`.
2. Suppose `G15` contains a subdivision of `K_8` on branch set `B` (`|B| = 8`, remaining set
   `R = V \ B` of size `7`). Let `n i` be the number of branch vertices in cluster `i : Fin 5`
   (`n i ≤ 3`, `∑ n i = 8`). Every pair `(u, v) ∈ B_i × B_{i+2}` is non-adjacent in `G15`,
   so its subdivision path uses at least `1` internal vertex in `R`, and if `n (i + 1) = 3`
   (leaving no vertex of `R` in the unique common neighboring cluster `i + 1`) it uses at least
   `2` internal vertices in `R`. Disjointness of internal vertices gives
   `∑ i : Fin 5, n i * n (i + 2) * (if n (i + 1) = 3 then 2 else 1) ≤ 7`,
   contradicting that this sum is at least `8` for every `n : Fin 5 → Fin 4` with `∑ n i = 8`.
-/

-- Problem: Hajós' conjecture (1961) — disproved.
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/HajosConjecture.lean:71 (declaration HajosConjecture.hajos_conjecture)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace HajosCounterexampleProof

open SimpleGraph Finset

private abbrev V15 := Fin 5 × Fin 3

private def c5k3Adj (u v : V15) : Prop :=
  (u.1 = v.1 ∧ u.2 ≠ v.2) ∨ u.1 - v.1 = 1 ∨ v.1 - u.1 = 1

private instance : DecidableRel c5k3Adj := fun u v =>
  inferInstanceAs (Decidable ((u.1 = v.1 ∧ u.2 ≠ v.2) ∨ u.1 - v.1 = 1 ∨ v.1 - u.1 = 1))

private def G15 : SimpleGraph V15 where
  Adj := c5k3Adj
  symm := ⟨fun _ _ h => by
    rcases h with ⟨h1, h2⟩ | h | h
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨fun u h => by
    rcases h with ⟨_, h2⟩ | h | h
    · exact h2 rfl
    · rw [sub_self] at h; exact absurd h (by decide)
    · rw [sub_self] at h; exact absurd h (by decide)⟩

private instance : DecidableRel G15.Adj := fun u v =>
  inferInstanceAs (Decidable (c5k3Adj u v))

/- ### Section 1: Finite checks on `Fin 5` and `Fin 4` -/

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
    ∀ i j : Fin 5, ¬ ((i = j + 2 ∧ i + 2 = j)) := by
  decide

private lemma tuple_weighted_nonedges_ge_eight :
    ∀ n0 n1 n2 n3 n4 : Fin 4,
      n0.1 + n1.1 + n2.1 + n3.1 + n4.1 = 8 →
      8 ≤ n0.1 * n2.1 * (if n1.1 = 3 then 2 else 1) +
          n1.1 * n3.1 * (if n2.1 = 3 then 2 else 1) +
          n2.1 * n4.1 * (if n3.1 = 3 then 2 else 1) +
          n3.1 * n0.1 * (if n4.1 = 3 then 2 else 1) +
          n4.1 * n1.1 * (if n0.1 = 3 then 2 else 1) := by
  decide

/- ### Section 2: `8 ≤ G15.chromaticNumber` -/

private lemma indep_card_le_two (S : Finset V15)
    (hind : ∀ u ∈ S, ∀ v ∈ S, ¬ G15.Adj u v) : S.card ≤ 2 := by
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
  have huv_na : ¬ c5k3Adj u v := hind u hu v hvS
  have huw_na : ¬ c5k3Adj u w := hind u hu w hwS
  have hvw_na : ¬ c5k3Adj v w := hind v hvS w hwS
  have extract : ∀ x y : V15, x ≠ y → ¬ c5k3Adj x y →
      x.1 ≠ y.1 ∧ x.1 - y.1 ≠ 1 ∧ y.1 - x.1 ≠ 1 := by
    intro x y hne hna
    refine ⟨fun h1 => hna (Or.inl ⟨h1, fun h2 => hne (Prod.ext h1 h2)⟩),
      fun h => hna (Or.inr (Or.inl h)), fun h => hna (Or.inr (Or.inr h))⟩
  obtain ⟨huv1, huv2, huv3⟩ := extract u v hvu.symm huv_na
  obtain ⟨huw1, huw2, huw3⟩ := extract u w hwu.symm huw_na
  obtain ⟨hvw1, hvw2, hvw3⟩ := extract v w hwv.symm hvw_na
  exact c5_no_three_indep_aux u.1 v.1 w.1 ⟨huv1, huw1, hvw1, huv2, huv3, huw2, huw3, hvw2, hvw3⟩

private lemma chromaticNumber_ge_eight : (8 : ℕ∞) ≤ G15.chromaticNumber := by
  by_contra hlt
  have hle7 : G15.chromaticNumber ≤ (7 : ℕ) := by
    cases hcn : G15.chromaticNumber with
    | top =>
      rw [hcn] at hlt
      exact absurd le_top hlt
    | coe m =>
      rw [hcn] at hlt
      have hm : m < 8 := by
        by_contra hge
        have : (8 : ℕ) ≤ m := by omega
        exact hlt (Nat.cast_le.mpr this)
      exact Nat.cast_le.mpr (by omega : m ≤ 7)
  obtain ⟨col⟩ := SimpleGraph.chromaticNumber_le_iff_colorable.mp hle7
  have hcard15 : (Finset.univ : Finset V15).card = 15 := by decide
  have hpart : (Finset.univ : Finset V15) =
      (Finset.univ : Finset (Fin 7)).biUnion (fun t => Finset.univ.filter (fun v : V15 => col v = t)) := by
    ext v
    simp
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 7))
      (fun t => Finset.univ.filter (fun v : V15 => col v = t)) := by
    intro t₁ _ t₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hne (h1.symm.trans h2)
  have hsum : 15 = ∑ t : Fin 7, (Finset.univ.filter (fun v : V15 => col v = t)).card := by
    calc 15 = (Finset.univ : Finset V15).card := hcard15.symm
      _ = ((Finset.univ : Finset (Fin 7)).biUnion
            (fun t => Finset.univ.filter (fun v : V15 => col v = t))).card := by rw [← hpart]
      _ = ∑ t : Fin 7, (Finset.univ.filter (fun v : V15 => col v = t)).card :=
          Finset.card_biUnion hdisj
  have hle14 : ∑ t : Fin 7, (Finset.univ.filter (fun v : V15 => col v = t)).card ≤ 14 := by
    calc ∑ t : Fin 7, (Finset.univ.filter (fun v : V15 => col v = t)).card
        ≤ ∑ _t : Fin 7, 2 := by
          refine Finset.sum_le_sum fun t _ => indep_card_le_two _ fun u hu v hv huv => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
          exact col.valid huv (hu.trans hv.symm)
      _ = 14 := by decide
  omega

/- ### Section 3: No `K_8` subdivision in `G15` -/

private lemma internal_card_ge_one {u v : V15} (hne : u ≠ v) (hna : ¬ G15.Adj u v)
    (w : G15.Walk u v) (hw : w.IsPath) :
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

private lemma internal_card_ge_two_of_no_common_nb {u v : V15} (hne : u ≠ v) (hna : ¬ G15.Adj u v)
    (w : G15.Walk u v) (hw : w.IsPath)
    (hno_mid : ∀ x, x ∈ w.support.tail.dropLast → ¬ (G15.Adj u x ∧ G15.Adj x v)) :
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

private lemma no_K8_subdivision_aux
    (f : Fin 8 → V15)
    (P : ∀ w w', (completeGraph (Fin 8)).Adj w w' → G15.Walk (f w) (f w'))
    (hM : HajosConjecture.IsSubdivisionModel (completeGraph (Fin 8)) G15 f P)
    (B R : Finset V15) (hB : B = Finset.univ.image f) (hR : R = Finset.univ \ B)
    (Bi : Fin 5 → Finset V15) (hBi : ∀ i, Bi i = B.filter (fun v => v.1 = i))
    (preFun : V15 → Fin 8) (hf_pre : ∀ v ∈ B, f (preFun v) = v) :
    False := by
  have hB_card : B.card = 8 := by
    rw [hB, Finset.card_image_of_injective _ hM.injective, Finset.card_univ, Fintype.card_fin]
  have hR_card : R.card = 7 := by
    have h15 : (Finset.univ : Finset V15).card = 15 := by decide
    have hu := Finset.card_union_of_disjoint (Finset.disjoint_sdiff : Disjoint B (Finset.univ \ B))
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ B), h15, hB_card, ← hR] at hu
    omega
  have hcluster_card : ∀ i : Fin 5, (Finset.univ.filter (fun v : V15 => v.1 = i)).card = 3 := by
    decide
  have hn_le : ∀ i : Fin 5, (Bi i).card ≤ 3 := by
    intro i
    calc (Bi i).card
        ≤ (Finset.univ.filter (fun v : V15 => v.1 = i)).card :=
          Finset.card_le_card fun v hv => by
            rw [hBi i] at hv
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
            exact hv.2
      _ = 3 := hcluster_card i
  have hB_eq_biUnion : B = (Finset.univ : Finset (Fin 5)).biUnion Bi := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, hBi, Finset.mem_filter]
    exact ⟨fun hv => ⟨v.1, hv, rfl⟩, fun ⟨_, hv, _⟩ => hv⟩
  have hBi_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 5)) Bi := by
    intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro v h1 h2
    rw [hBi i, Finset.mem_filter] at h1
    rw [hBi j, Finset.mem_filter] at h2
    exact hij (h1.2.symm.trans h2.2)
  have hn_sum : ∑ i : Fin 5, (Bi i).card = 8 := by
    rw [← hB_card, hB_eq_biUnion, Finset.card_biUnion hBi_disj]
  have hfull_cluster : ∀ i : Fin 5, (Bi i).card = 3 → ∀ x : V15, x.1 = i → x ∈ Set.range f := by
    intro i hni x hx
    have hsub : Bi i ⊆ Finset.univ.filter (fun v : V15 => v.1 = i) := fun v hv => by
      rw [hBi i] at hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hv.2
    have heq : Bi i = Finset.univ.filter (fun v : V15 => v.1 = i) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcluster_card i]; exact le_of_eq hni.symm)
    have hxBi : x ∈ Bi i := by rw [heq]; simp [hx]
    rw [hBi i, Finset.mem_filter, hB] at hxBi
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hxBi.1
    exact ⟨a, ha⟩
  let AllPairs : Finset (Σ i : Fin 5, V15 × V15) :=
    (Finset.univ : Finset (Fin 5)).sigma (fun i => Bi i ×ˢ Bi (i + 2))
  have hpair_mem : ∀ t ∈ AllPairs,
      (t.2.1 ∈ B ∧ t.2.1.1 = t.1) ∧ (t.2.2 ∈ B ∧ t.2.2.1 = t.1 + 2) := by
    intro t ht
    simp only [AllPairs, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_product, hBi,
      Finset.mem_filter] at ht
    exact ht
  have hpair_ne : ∀ t ∈ AllPairs, preFun t.2.1 ≠ preFun t.2.2 := by
    intro t ht heq
    obtain ⟨⟨huB, hu1⟩, ⟨hvB, hv1⟩⟩ := hpair_mem t ht
    have hveq : t.2.1 = t.2.2 := by rw [← hf_pre t.2.1 huB, ← hf_pre t.2.2 hvB, heq]
    have hcl : t.1 = t.1 + 2 := hu1.symm.trans ((congrArg Prod.fst hveq).trans hv1)
    exact (c5_dist2_not_adj t.1).1 hcl
  let intSet : (Σ i : Fin 5, V15 × V15) → Finset V15 := fun t =>
    if h : preFun t.2.1 ≠ preFun t.2.2 then
      ((P (preFun t.2.1) (preFun t.2.2) h).support.tail.dropLast).toFinset
    else ∅
  have hint_sub : ∀ t ∈ AllPairs, intSet t ⊆ R := by
    intro t ht x hx
    have hne := hpair_ne t ht
    dsimp only [intSet] at hx
    rw [dif_pos hne, List.mem_toFinset] at hx
    have hnot : x ∉ Set.range f := hM.internal_avoid _ _ hne x hx
    rw [hR, Finset.mem_sdiff]
    refine ⟨Finset.mem_univ x, fun hxB => ?_⟩
    rw [hB] at hxB
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxB
    exact hnot ⟨a, rfl⟩
  have hint_disj : Set.PairwiseDisjoint (AllPairs : Set (Σ i : Fin 5, V15 × V15)) intSet := by
    intro t₁ ht₁ t₂ ht₂ hne
    dsimp only [Function.onFun]
    have hne1 := hpair_ne t₁ ht₁
    have hne2 := hpair_ne t₂ ht₂
    have hsym_ne : s(preFun t₁.2.1, preFun t₁.2.2) ≠ s(preFun t₂.2.1, preFun t₂.2.2) := by
      intro hsym
      obtain ⟨⟨hu1B, hu1c⟩, ⟨hv1B, hv1c⟩⟩ := hpair_mem t₁ ht₁
      obtain ⟨⟨hu2B, hu2c⟩, ⟨hv2B, hv2c⟩⟩ := hpair_mem t₂ ht₂
      rw [Sym2.eq_iff] at hsym
      rcases hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hv1 : t₁.2.1 = t₂.2.1 := by
          rw [← hf_pre t₁.2.1 hu1B, ← hf_pre t₂.2.1 hu2B, h1]
        have hv2 : t₁.2.2 = t₂.2.2 := by
          rw [← hf_pre t₁.2.2 hv1B, ← hf_pre t₂.2.2 hv2B, h2]
        have hi : t₁.1 = t₂.1 := by rw [← hu1c, hv1, hu2c]
        rcases t₁ with ⟨i₁, ⟨u₁, v₁⟩⟩
        rcases t₂ with ⟨i₂, ⟨u₂, v₂⟩⟩
        dsimp at hi hv1 hv2
        subst hi; subst hv1; subst hv2
        exact hne rfl
      · have hv1 : t₁.2.1 = t₂.2.2 := by
          rw [← hf_pre t₁.2.1 hu1B, ← hf_pre t₂.2.2 hv2B, h1]
        have hv2 : t₁.2.2 = t₂.2.1 := by
          rw [← hf_pre t₁.2.2 hv1B, ← hf_pre t₂.2.1 hu2B, h2]
        have hc1 : t₁.1 = t₂.1 + 2 := by rw [← hu1c, hv1, hv2c]
        have hc2 : t₁.1 + 2 = t₂.1 := by rw [← hv1c, hv2, hu2c]
        exact c5_pair_unique_aux t₁.1 t₂.1 ⟨hc1, hc2⟩
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    dsimp only [intSet] at hx1 hx2
    rw [dif_pos hne1, List.mem_toFinset] at hx1
    rw [dif_pos hne2, List.mem_toFinset] at hx2
    exact hM.internal_disjoint _ _ hne1 _ _ hne2 hsym_ne x hx1 hx2
  have hsum_le_seven : ∑ t ∈ AllPairs, (intSet t).card ≤ 7 := by
    rw [← hR_card, ← Finset.card_biUnion hint_disj]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr hint_sub)
  have hterm_ge : ∀ t ∈ AllPairs,
      (if (Bi (t.1 + 1)).card = 3 then 2 else 1) ≤ (intSet t).card := by
    intro t ht
    have hne := hpair_ne t ht
    dsimp only [intSet]
    rw [dif_pos hne]
    obtain ⟨⟨huB, hu1⟩, ⟨hvB, hv1⟩⟩ := hpair_mem t ht
    set a := preFun t.2.1
    set b := preFun t.2.2
    have hfa : f a = t.2.1 := hf_pre t.2.1 huB
    have hfb : f b = t.2.2 := hf_pre t.2.2 hvB
    have hfa_cl : (f a).1 = t.1 := by rw [hfa]; exact hu1
    have hfb_cl : (f b).1 = t.1 + 2 := by rw [hfb]; exact hv1
    have hfab_ne : f a ≠ f b := fun h => hne (hM.injective h)
    have hfab_na : ¬ G15.Adj (f a) (f b) := by
      intro hadj
      rcases hadj with ⟨h1, _⟩ | h | h
      · rw [hfa_cl, hfb_cl] at h1; exact (c5_dist2_not_adj t.1).1 h1
      · rw [hfa_cl, hfb_cl] at h; exact (c5_dist2_not_adj t.1).2.1 h
      · rw [hfa_cl, hfb_cl] at h; exact (c5_dist2_not_adj t.1).2.2 h
    split_ifs with hfull
    · refine internal_card_ge_two_of_no_common_nb hfab_ne hfab_na (P a b hne)
        (hM.isPath a b hne) fun x hx ⟨hax, hxb⟩ => ?_
      have hx1 : t.1 = x.1 ∨ t.1 - x.1 = 1 ∨ x.1 - t.1 = 1 := by
        rw [← hfa_cl]
        rcases hax with ⟨h1, _⟩ | h | h
        · exact Or.inl h1
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      have hx2 : x.1 = t.1 + 2 ∨ x.1 - (t.1 + 2) = 1 ∨ (t.1 + 2) - x.1 = 1 := by
        rw [← hfb_cl]
        rcases hxb with ⟨h1, _⟩ | h | h
        · exact Or.inl h1
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      have hx_cl : x.1 = t.1 + 1 := c5_common_nb_cluster t.1 x.1 hx1 hx2
      exact hM.internal_avoid a b hne x hx (hfull_cluster (t.1 + 1) hfull x hx_cl)
    · exact internal_card_ge_one hfab_ne hfab_na (P a b hne) (hM.isPath a b hne)
  have hsum_ge_weighted :
      (∑ i : Fin 5, (Bi i).card * (Bi (i + 2)).card * (if (Bi (i + 1)).card = 3 then 2 else 1)) ≤
        ∑ t ∈ AllPairs, (intSet t).card := by
    calc (∑ i : Fin 5, (Bi i).card * (Bi (i + 2)).card * (if (Bi (i + 1)).card = 3 then 2 else 1))
        = ∑ i : Fin 5, ∑ _p ∈ Bi i ×ˢ Bi (i + 2), (if (Bi (i + 1)).card = 3 then 2 else 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_const, Finset.card_product, smul_eq_mul]
      _ = ∑ t ∈ AllPairs, (if (Bi (t.1 + 1)).card = 3 then 2 else 1) := by
          rw [Finset.sum_sigma]
      _ ≤ ∑ t ∈ AllPairs, (intSet t).card := Finset.sum_le_sum hterm_ge
  have hsum_ge_eight :
      8 ≤ ∑ i : Fin 5, (Bi i).card * (Bi (i + 2)).card * (if (Bi (i + 1)).card = 3 then 2 else 1) := by
    let m : Fin 5 → Fin 4 := fun i => ⟨(Bi i).card, by have := hn_le i; omega⟩
    have hm_sum : (m 0).1 + (m 1).1 + (m 2).1 + (m 3).1 + (m 4).1 = 8 := by
      have h5 : (∑ i : Fin 5, (Bi i).card) =
          (Bi 0).card + (Bi 1).card + (Bi 2).card + (Bi 3).card + (Bi 4).card := by
        rw [Fin.sum_univ_five]
      dsimp only [m]
      omega
    have h8 := tuple_weighted_nonedges_ge_eight (m 0) (m 1) (m 2) (m 3) (m 4) hm_sum
    have hsum5 :
        (∑ i : Fin 5, (Bi i).card * (Bi (i + 2)).card * (if (Bi (i + 1)).card = 3 then 2 else 1)) =
          (Bi 0).card * (Bi 2).card * (if (Bi 1).card = 3 then 2 else 1) +
          (Bi 1).card * (Bi 3).card * (if (Bi 2).card = 3 then 2 else 1) +
          (Bi 2).card * (Bi 4).card * (if (Bi 3).card = 3 then 2 else 1) +
          (Bi 3).card * (Bi 0).card * (if (Bi 4).card = 3 then 2 else 1) +
          (Bi 4).card * (Bi 1).card * (if (Bi 0).card = 3 then 2 else 1) := by
      rw [Fin.sum_univ_five]
      rfl
    dsimp only [m] at h8
    omega
  omega

private lemma no_K8_subdivision :
    ¬ HajosConjecture.ContainsSubdivision (completeGraph (Fin 8)) G15 := by
  classical
  rintro ⟨f, P, hM⟩
  let B : Finset V15 := Finset.univ.image f
  let preFun : V15 → Fin 8 := fun v =>
    if hv : v ∈ B then Classical.choose (Finset.mem_image.mp hv) else 0
  have hf_pre : ∀ v ∈ B, f (preFun v) = v := fun v hv => by
    simp only [preFun, dif_pos hv]
    exact (Classical.choose_spec (Finset.mem_image.mp hv)).2
  exact no_K8_subdivision_aux f P hM B (Finset.univ \ B) rfl rfl
    (fun i => B.filter (fun v => v.1 = i)) (fun _ => rfl) preFun hf_pre

end HajosCounterexampleProof

theorem OMA.solution : type_of% @HajosConjecture.hajos_conjecture := by
  intro h
  exact HajosCounterexampleProof.no_K8_subdivision
    (h HajosCounterexampleProof.G15 8 HajosCounterexampleProof.chromaticNumber_ge_eight)
