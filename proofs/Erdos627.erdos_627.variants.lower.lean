import FormalConjectures.ErdosProblems.«627»

/-!
# Erdős’s lower bound for the chromatic-to-clique ratio

Counting labelled graphs yields a graph with clique and independence numbers at most
twice the binary logarithm. Each colour class is independent, so these two bounds
give a chromatic-to-clique ratio of at least n divided by four times the squared logarithm.
-/

-- Problem: Erdős Problem 627 — lower
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/627.lean:87 (declaration Erdos627.erdos_627.variants.lower)
-- Credit: @Halldon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter SimpleGraph

namespace Erdos627Lower

/- The Boolean edge-labelling construction and union bound are from @TheWaler's
   proof of Erdős 78 in this repository (PR #299, commit 1dba85f).
   We retain only the finite graph counting argument. -/
private abbrev Pair (n : ℕ) := { p : Fin n × Fin n // p.1 < p.2 }

private def toGraph {n : ℕ} (c : Pair n → Bool) : SimpleGraph (Fin n) where
  Adj u v :=
    if h : u < v then c ⟨(u, v), h⟩ = true
    else if h' : v < u then c ⟨(v, u), h'⟩ = true
    else False
  symm := ⟨by
    intro u v huv
    by_cases h1 : u < v
    · have h2 : ¬ v < u := not_lt_of_gt h1
      simp only [h1, h2, ↓reduceDIte] at huv ⊢
      exact huv
    · by_cases h2 : v < u
      · simp only [h1, h2, ↓reduceDIte] at huv ⊢
        exact huv
      · simp only [h1, h2, ↓reduceDIte] at huv⟩
  loopless := ⟨by
    intro u
    simp⟩

private lemma toGraph_adj_of_lt {n : ℕ} (c : Pair n → Bool) {u v : Fin n} (h : u < v) :
    (toGraph c).Adj u v ↔ c ⟨(u, v), h⟩ = true := by
  simp [toGraph, h]

private lemma toGraph_compl_adj_of_lt {n : ℕ} (c : Pair n → Bool) {u v : Fin n} (h : u < v) :
    (toGraph c)ᶜ.Adj u v ↔ c ⟨(u, v), h⟩ = false := by
  simp [SimpleGraph.compl_adj, ne_of_lt h, toGraph, h]

private def pairsIn {n : ℕ} (s : Finset (Fin n)) : Finset (Pair n) :=
  Finset.univ.filter (fun p => p.1.1 ∈ s ∧ p.1.2 ∈ s)

private lemma pairsIn_card {n : ℕ} (s : Finset (Fin n)) :
    (pairsIn s).card = s.card * (s.card - 1) / 2 := by
  let L : Finset (Fin n × Fin n) := (s ×ˢ s).filter (fun p => p.1 < p.2)
  let G : Finset (Fin n × Fin n) := (s ×ˢ s).filter (fun p => p.2 < p.1)
  let D : Finset (Fin n × Fin n) := (s ×ˢ s).filter (fun p => p.1 = p.2)
  have hPL : (pairsIn s).card = L.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [L, Finset.mem_filter, Finset.mem_product]
      exact ⟨hp, p.2⟩
    · intro p₁ _ p₂ _ h
      exact Subtype.ext h
    · intro q hq
      simp only [L, Finset.mem_filter, Finset.mem_product] at hq
      exact ⟨⟨q, hq.2⟩, by simp [pairsIn, hq.1], rfl⟩
  have hLG : L.card = G.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [L, Finset.mem_filter, Finset.mem_product] at hp
      simp only [G, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p₁ _ p₂ _ h
      cases p₁; cases p₂
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      simp only [G, Finset.mem_filter, Finset.mem_product] at hq
      exact ⟨(q.2, q.1), by simp [L, hq.1.1, hq.1.2, hq.2], by simp⟩
  have hDs : D.card = s.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [D, Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1.1
    · intro p₁ hp₁ p₂ hp₂ h
      simp only [D, Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
      exact Prod.ext h (hp₁.2.symm.trans (h.trans hp₂.2))
    · intro x hx
      exact ⟨(x, x), by simp [D, hx], rfl⟩
  have hdisj1 : Disjoint L G := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [L, G, Finset.mem_filter] at hp1 hp2
    exact lt_asymm hp1.2 hp2.2
  have hdisj2 : Disjoint (L ∪ G) D := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [L, G, D, Finset.mem_union, Finset.mem_filter] at hp1 hp2
    rcases hp1 with h1 | h1
    · exact ne_of_lt h1.2 hp2.2
    · exact ne_of_gt h1.2 hp2.2
  have hunion : (L ∪ G) ∪ D = s ×ˢ s := by
    ext ⟨u, v⟩
    simp only [L, G, D, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    · intro h
      rcases lt_trichotomy u v with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨h, hlt⟩)
      · exact Or.inr ⟨h, heq⟩
      · exact Or.inl (Or.inr ⟨h, hgt⟩)
  have htotal : 2 * (pairsIn s).card + s.card = s.card * s.card := by
    have hc : ((L ∪ G) ∪ D).card = (s ×ˢ s).card := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
      Finset.card_product, ← hLG, ← hPL, hDs] at hc
    omega
  cases hk : s.card with
  | zero =>
    rw [hk] at htotal
    omega
  | succ m =>
    rw [hk] at htotal
    have hmul : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
    rw [hmul] at htotal
    have h2 : 2 * (pairsIn s).card = (m + 1) * m := by omega
    simp only [Nat.add_sub_cancel]
    omega

private def monoGraphs {n : ℕ} (s : Finset (Fin n)) (b : Bool) : Finset (Pair n → Bool) :=
  Finset.univ.filter (fun c => ∀ p ∈ pairsIn s, c p = b)

private lemma monoGraphs_card_mul {n : ℕ} (s : Finset (Fin n)) (b : Bool) :
    (monoGraphs s b).card * 2 ^ (pairsIn s).card ≤ 2 ^ Fintype.card (Pair n) := by
  let res : (Pair n → Bool) → ({p : Pair n // p ∉ pairsIn s} → Bool) :=
    fun c p => c p.1
  have hinj : Set.InjOn res (monoGraphs s b) := by
    intro c₁ hc₁ c₂ hc₂ heq
    simp only [Finset.mem_coe, monoGraphs, Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
    funext p
    by_cases hp : p ∈ pairsIn s
    · rw [hc₁ p hp, hc₂ p hp]
    · exact congrFun heq ⟨p, hp⟩
  have hle : (monoGraphs s b).card ≤ Fintype.card ({p : Pair n // p ∉ pairsIn s} → Bool) := by
    have h := Finset.card_le_card_of_injOn res (fun _ _ => Finset.mem_univ _) hinj
    simpa [Finset.card_univ] using h
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_coe] at hle
  have hsub : (pairsIn s).card ≤ Fintype.card (Pair n) := Finset.card_le_univ (pairsIn s)
  have hmul := Nat.mul_le_mul_right (2 ^ (pairsIn s).card) hle
  rwa [← pow_add, Nat.sub_add_cancel hsub] at hmul

private lemma exists_ramsey_counterexample {n k : ℕ}
    (hlt : 2 * n.choose k < 2 ^ (k * (k - 1) / 2)) :
    ∃ C : SimpleGraph (Fin n),
      ¬ (completeGraph (Fin k)).IsContained C ∧ ¬ (completeGraph (Fin k)).IsContained Cᶜ := by
  let Bad : Finset (Pair n → Bool) :=
    ((Finset.univ : Finset (Fin n)).powersetCard k).biUnion
      (fun s => monoGraphs s true ∪ monoGraphs s false)
  have hbad_mul : Bad.card * 2 ^ (k * (k - 1) / 2) ≤
      (2 * n.choose k) * 2 ^ Fintype.card (Pair n) := by
    have h1 : Bad.card ≤
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          (monoGraphs s true ∪ monoGraphs s false).card :=
      Finset.card_biUnion_le
    calc Bad.card * 2 ^ (k * (k - 1) / 2)
        ≤ (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            (monoGraphs s true ∪ monoGraphs s false).card) * 2 ^ (k * (k - 1) / 2) :=
          Nat.mul_le_mul_right _ h1
      _ = ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            (monoGraphs s true ∪ monoGraphs s false).card * 2 ^ (k * (k - 1) / 2) :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ _s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            (2 * 2 ^ Fintype.card (Pair n)) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hscard : s.card = k := (Finset.mem_powersetCard.mp hs).2
          have hpcard : (pairsIn s).card = k * (k - 1) / 2 := by
            rw [pairsIn_card, hscard]
          rw [← hpcard]
          have hu := Finset.card_union_le (monoGraphs s true) (monoGraphs s false)
          calc (monoGraphs s true ∪ monoGraphs s false).card * 2 ^ (pairsIn s).card
              ≤ ((monoGraphs s true).card + (monoGraphs s false).card) * 2 ^ (pairsIn s).card :=
                Nat.mul_le_mul_right _ hu
            _ = (monoGraphs s true).card * 2 ^ (pairsIn s).card +
                (monoGraphs s false).card * 2 ^ (pairsIn s).card :=
                Nat.add_mul _ _ _
            _ ≤ 2 ^ Fintype.card (Pair n) + 2 ^ Fintype.card (Pair n) :=
                Nat.add_le_add (monoGraphs_card_mul s true) (monoGraphs_card_mul s false)
            _ = 2 * 2 ^ Fintype.card (Pair n) := by ring
      _ = ((Finset.univ : Finset (Fin n)).powersetCard k).card *
            (2 * 2 ^ Fintype.card (Pair n)) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = (2 * n.choose k) * 2 ^ Fintype.card (Pair n) := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          ring
  have hbad_lt_mul : Bad.card * 2 ^ (k * (k - 1) / 2) <
      2 ^ (k * (k - 1) / 2) * 2 ^ Fintype.card (Pair n) :=
    lt_of_le_of_lt hbad_mul (Nat.mul_lt_mul_of_pos_right hlt (by positivity))
  have hbad_lt : Bad.card < (Finset.univ : Finset (Pair n → Bool)).card := by
    have hlt' : Bad.card < 2 ^ Fintype.card (Pair n) := by
      rw [mul_comm (2 ^ (k * (k - 1) / 2))] at hbad_lt_mul
      exact Nat.lt_of_mul_lt_mul_right hbad_lt_mul
    simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool] using hlt'
  have hex : ∃ c : Pair n → Bool, c ∉ Bad := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Pair n → Bool)) ⊆ Bad := fun c _ => hall c
    exact not_le_of_gt hbad_lt (Finset.card_le_card hsub)
  obtain ⟨c, hc⟩ := hex
  refine ⟨toGraph c, ?_, ?_⟩
  · intro hf
    rcases (hf : Nonempty _) with ⟨f⟩
    let s : Finset (Fin n) := Finset.univ.image f
    have hscard : s.card = k := by
      dsimp only [s]
      rw [← SimpleGraph.Copy.coe_toHom, Finset.card_image_of_injective _ f.injective,
        Finset.card_univ, Fintype.card_fin]
    have hs_mem : s ∈ (Finset.univ : Finset (Fin n)).powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hscard⟩
    have hc_mono : c ∈ monoGraphs s true := by
      simp only [monoGraphs, Finset.mem_filter, Finset.mem_univ, true_and]
      intro p hp
      simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp.1
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp.2
      have hij : i ≠ j := by
        intro h
        subst h
        exact ne_of_lt p.2 (hi.symm.trans hj)
      have hadj : (toGraph c).Adj p.1.1 p.1.2 := by
        rw [← hi, ← hj]
        exact f.toHom.map_rel' hij
      exact (toGraph_adj_of_lt c p.2).mp hadj
    exact hc (Finset.mem_biUnion.mpr ⟨s, hs_mem, Finset.mem_union_left _ hc_mono⟩)
  · intro hf
    rcases (hf : Nonempty _) with ⟨f⟩
    let s : Finset (Fin n) := Finset.univ.image f
    have hscard : s.card = k := by
      dsimp only [s]
      rw [← SimpleGraph.Copy.coe_toHom, Finset.card_image_of_injective _ f.injective,
        Finset.card_univ, Fintype.card_fin]
    have hs_mem : s ∈ (Finset.univ : Finset (Fin n)).powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hscard⟩
    have hc_mono : c ∈ monoGraphs s false := by
      simp only [monoGraphs, Finset.mem_filter, Finset.mem_univ, true_and]
      intro p hp
      simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp.1
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp.2
      have hij : i ≠ j := by
        intro h
        subst h
        exact ne_of_lt p.2 (hi.symm.trans hj)
      have hadj : (toGraph c)ᶜ.Adj p.1.1 p.1.2 := by
        rw [← hi, ← hj]
        exact f.toHom.map_rel' hij
      exact (toGraph_compl_adj_of_lt c p.2).mp hadj
    exact hc (Finset.mem_biUnion.mpr ⟨s, hs_mem, Finset.mem_union_right _ hc_mono⟩)


private lemma four_pow_le_factorial (k : ℕ) (hk : 9 ≤ k) : 4 ^ k ≤ k.factorial := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ, Nat.factorial_succ, mul_comm (k + 1)]
    exact Nat.mul_le_mul ih (by omega)

/-- Keeping the factorial in the binomial coefficient allows us to use
    twice the *floor* of the binary logarithm as the forbidden clique size. -/
private lemma ramsey_threshold (n t : ℕ) (ht : 5 ≤ t) (hn : n ≤ 2 ^ (t + 1)) :
    2 * n.choose (2 * t) < 2 ^ ((2 * t) * (2 * t - 1) / 2) := by
  let k := 2 * t
  change 2 * n.choose k < 2 ^ (k * (k - 1) / 2)
  have hk : 9 ≤ k := by dsimp [k]; omega
  have hchoose : 4 ^ k * n.choose k ≤ n ^ k := calc
    _ ≤ k.factorial * n.choose k := Nat.mul_le_mul_right _ (four_pow_le_factorial k hk)
    _ = n.descFactorial k := (Nat.descFactorial_eq_factorial_mul_choose n k).symm
    _ ≤ _ := Nat.descFactorial_le_pow n k
  have hexp : 1 + (t + 1) * k < 2 * k + k * (k - 1) / 2 := by
    have h : k * (k - 1) / 2 = t * (2*t - 1) := by
      rw [show k = 2*t by rfl, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    rw [h]
    have hsub : 2*t - 1 + 1 = 2*t := by omega
    have hmul := congrArg (t * ·) hsub
    dsimp [k] at *
    nlinarith
  apply Nat.lt_of_mul_lt_mul_left (a := 4 ^ k)
  calc
    4 ^ k * (2 * n.choose k) = 2 * (4 ^ k * n.choose k) := by ring
    _ ≤ 2 * n ^ k := Nat.mul_le_mul_left _ hchoose
    _ ≤ 2 * (2 ^ (t + 1)) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn _)
    _ = 2 ^ (1 + (t + 1) * k) := by
      rw [pow_add 2 1 ((t + 1) * k), pow_one, pow_mul 2 (t + 1) k]
    _ < 2 ^ (2 * k + k * (k - 1) / 2) := Nat.pow_lt_pow_right (by decide) hexp
    _ = 4 ^ k * 2 ^ (k * (k - 1) / 2) := by rw [pow_add, pow_mul]; norm_num

private lemma clique_le_of_free {n k : ℕ} (G : SimpleGraph (Fin n))
    (h : ¬ (completeGraph (Fin k)).IsContained G) : G.cliqueNum ≤ k := by
  by_contra! hlt
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hfree : G.CliqueFree k := by
    by_contra hf
    exact h ((G.not_cliqueFree_iff_top_isContained k).1 hf)
  exact hs.not_cliqueFree (CliqueFree.mono hlt.le hfree)

private lemma ratio_bound {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (G : SimpleGraph (Fin n)) (hc : G.cliqueNum ≤ k) (hi : G.indepNum ≤ k) :
    (n : ℝ) / (k : ℝ) ^ 2 ≤ Erdos627.maxChromaticCliqueRatio n := by
  classical
  have one_le (H : SimpleGraph (Fin n)) : 1 ≤ H.cliqueNum := by
    let v : Fin n := ⟨0, hn⟩
    have h : H.IsClique (({v} : Finset (Fin n)) : Set (Fin n)) := by simp
    simpa using h.card_le_cliqueNum
  have hpω : 0 < (G.cliqueNum : ℝ) := by exact_mod_cast one_le G
  have hα : 0 < G.indepNum := (by decide : 0 < 1).trans_le (by simpa using one_le Gᶜ)
  have hχ : G.chromaticNumber ≠ ⊤ :=
    chromaticNumber_ne_top_iff_exists.mpr ⟨_, G.colorable_of_fintype⟩
  have hcolor := card_div_indepNum_le_chromaticNumber (G := G)
  rw [← ENat.natCast_toNat hχ] at hcolor
  have hceil : ⌈((n : ℚ≥0) / G.indepNum)⌉₊ ≤ G.chromaticNumber.toNat := by
    simpa [Nat.card_eq_fintype_card] using hcolor
  have hnn := (div_le_iff₀ (show 0 < (G.indepNum : ℚ≥0) by exact_mod_cast hα)).mp
    (Nat.ceil_le.mp hceil)
  have hnc : n ≤ G.chromaticNumber.toNat * G.indepNum := by exact_mod_cast hnn
  have hnk : (n : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) * k := by
    exact_mod_cast hnc.trans (Nat.mul_le_mul_left _ hi)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hratio : (n : ℝ) / (k : ℝ)^2 ≤ (G.chromaticNumber.toNat : ℝ) / G.cliqueNum := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hk') hpω]
    calc
      (n : ℝ) * G.cliqueNum ≤ (n : ℝ) * k := by gcongr
      _ ≤ ((G.chromaticNumber.toNat : ℝ) * k) * k := by gcongr
      _ = _ := by ring
  exact le_ciSup_of_le (Set.finite_range _).bddAbove G hratio

end Erdos627Lower

theorem OMA.solution : type_of% @Erdos627.erdos_627.variants.lower := by
  intro ε hε
  filter_upwards [eventually_ge_atTop 32] with n hn
  let t := Nat.log 2 n
  have ht : 5 ≤ t := (Nat.le_log_iff_pow_le (by decide) (by omega)).2 (by simpa using hn)
  have htt := Erdos627Lower.ramsey_threshold n t ht (Nat.lt_pow_succ_log_self (by decide) n).le
  obtain ⟨G, hG, hG'⟩ := Erdos627Lower.exists_ramsey_counterexample htt
  have hc := Erdos627Lower.clique_le_of_free G hG
  have hi : G.indepNum ≤ 2 * t := by
    simpa using Erdos627Lower.clique_le_of_free Gᶜ hG'
  have hmax := Erdos627Lower.ratio_bound (by omega) (by omega) G hc hi
  have htl : (t : ℝ) ≤ Real.logb 2 n := by simpa [t, Nat.log2_eq_log_two] using Real.log2_le_logb n
  have ht' : 0 < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hL := ht'.trans_le htl
  calc
    _ ≤ (1 / 4 : ℝ) * ((n : ℝ) / Real.logb 2 n ^ 2) := by gcongr; linarith
    _ = (n : ℝ) / (2 * Real.logb 2 n) ^ 2 := by ring
    _ ≤ (n : ℝ) / ((2 * t : ℕ) : ℝ) ^ 2 := by
      push_cast
      gcongr
    _ ≤ _ := hmax
