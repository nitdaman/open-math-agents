import FormalConjectures.ErdosProblems.«74»

-- Reduction Erdos74.erdos_74.variants.sqrt.R1 of Erdős Problem 74 — sqrt
-- Credit: @preternatural-tocsin
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos74_erdos_74_variants_sqrt_R1

def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (G : SimpleGraph (Fin N)), ¬ G.Colorable 3 ∧
    ∀ S : Finset (Fin N), ∃ (c : Fin N → Bool) (E : Finset (Sym2 (Fin N))),
      (E.card : ℝ) ≤ ε * Real.sqrt S.card ∧
      ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → s(u, v) ∉ E → c u ≠ c v

def H2 : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    (∀ δ : ℝ, 0 < δ → ∃ (N : ℕ) (G : SimpleGraph (Fin N)), ¬ G.Colorable k ∧
      ∀ S : Finset (Fin N), ∃ (c : Fin N → Bool) (E : Finset (Sym2 (Fin N))),
        (E.card : ℝ) ≤ δ * Real.sqrt S.card ∧
        ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → s(u, v) ∉ E → c u ≠ c v) →
    ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (G : SimpleGraph (Fin N)), ¬ G.Colorable (k + 1) ∧
      ∀ S : Finset (Fin N), ∃ (c : Fin N → Bool) (E : Finset (Sym2 (Fin N))),
        (E.card : ℝ) ≤ ε * Real.sqrt S.card ∧
        ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → s(u, v) ∉ E → c u ≠ c v

lemma geom_quarter_sum (M : ℕ) :
    ∑ k ∈ Finset.range M, ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) ^ 2 =
      (1 - ((1 : ℝ) / 4) ^ M) / 3 := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hpow : ((1 : ℝ) / (2 : ℝ) ^ (m + 1)) ^ 2 = ((1 : ℝ) / 4) ^ (m + 1) := by
      rw [one_div, one_div, inv_pow, inv_pow, ← pow_mul, mul_comm (m + 1) 2, pow_mul]
      norm_num
    rw [hpow, pow_succ]
    ring

lemma weighted_sqrt_sum_le (K : Finset ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ K, ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) * Real.sqrt (f k) ≤
      Real.sqrt (∑ k ∈ K, f k : ℕ) := by
  have hnonneg_lhs : 0 ≤ ∑ k ∈ K, ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) * Real.sqrt (f k) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hcs :
      (∑ k ∈ K, ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) * Real.sqrt (f k)) ^ 2 ≤
        (∑ k ∈ K, ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) ^ 2) *
          (∑ k ∈ K, (Real.sqrt (f k)) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq K _ _
  have hsq : ∑ k ∈ K, (Real.sqrt (f k)) ^ 2 = ((∑ k ∈ K, f k : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have hM : ∃ M : ℕ, K ⊆ Finset.range M := by
    refine ⟨K.sup id + 1, fun k hk => ?_⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  obtain ⟨M, hKM⟩ := hM
  have hwt : ∑ k ∈ K, ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) ^ 2 ≤ 1 := by
    calc ∑ k ∈ K, ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) ^ 2
        ≤ ∑ k ∈ Finset.range M, ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hKM (fun _ _ _ => sq_nonneg _)
      _ = (1 - ((1 : ℝ) / 4) ^ M) / 3 := geom_quarter_sum M
      _ ≤ 1 := by
          have : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ M := by positivity
          linarith
  have hsq_le :
      (∑ k ∈ K, ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) * Real.sqrt (f k)) ^ 2 ≤
        ((∑ k ∈ K, f k : ℕ) : ℝ) := by
    calc (∑ k ∈ K, ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) * Real.sqrt (f k)) ^ 2
        ≤ (∑ k ∈ K, ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) ^ 2) *
            ((∑ k ∈ K, f k : ℕ) : ℝ) := by simpa [hsq] using hcs
      _ ≤ 1 * ((∑ k ∈ K, f k : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hwt (Nat.cast_nonneg _)
      _ = ((∑ k ∈ K, f k : ℕ) : ℝ) := one_mul _
  exact (Real.le_sqrt hnonneg_lhs (Nat.cast_nonneg _)).mpr hsq_le

lemma exists_family (h1 : H1) (h2 : H2) :
    ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (G : SimpleGraph (Fin N)), ¬ G.Colorable k ∧
      ∀ S : Finset (Fin N), ∃ (c : Fin N → Bool) (E : Finset (Sym2 (Fin N))),
        (E.card : ℝ) ≤ ε * Real.sqrt S.card ∧
        ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → s(u, v) ∉ E → c u ≠ c v := by
  have hge3 : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ (N : ℕ) (G : SimpleGraph (Fin N)), ¬ G.Colorable (m + 3) ∧
        ∀ S : Finset (Fin N), ∃ (c : Fin N → Bool) (E : Finset (Sym2 (Fin N))),
          (E.card : ℝ) ≤ ε * Real.sqrt S.card ∧
          ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → s(u, v) ∉ E → c u ≠ c v := by
    intro m
    induction m with
    | zero => exact h1
    | succ m ih =>
      intro ε hε
      exact h2 (m + 3) (by omega) ih ε hε
  intro k ε hε
  by_cases hk : 3 ≤ k
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
    exact hge3 m ε hε
  · obtain ⟨N, G, hnc, hbip⟩ := h1 ε hε
    refine ⟨N, G, fun hc => hnc (hc.mono (by omega)), hbip⟩

theorem main : H1 → H2 → type_of% @Erdos74.erdos_74.variants.sqrt := by
  classical
  intro h1 h2
  have hfam : ∀ k : ℕ, ∃ (N : ℕ) (G : SimpleGraph (Fin N)), ¬ G.Colorable k ∧
      ∀ S : Finset (Fin N), ∃ (c : Fin N → Bool) (E : Finset (Sym2 (Fin N))),
        (E.card : ℝ) ≤ ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) * Real.sqrt S.card ∧
        ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → s(u, v) ∉ E → c u ≠ c v :=
    fun k => exists_family h1 h2 k ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) (by positivity)
  choose N Gs hcol hbip using hfam
  let V := ULift (Σ k : ℕ, Fin (N k))
  let G : SimpleGraph V :=
    { Adj := fun x y => ∃ h : x.down.1 = y.down.1, (Gs x.down.1).Adj x.down.2 (h ▸ y.down.2)
      symm := by
        constructor
        rintro ⟨⟨k, u⟩⟩ ⟨⟨k', v⟩⟩ ⟨h, hadj⟩
        dsimp at h hadj
        subst h
        exact ⟨rfl, (Gs k).symm.symm _ _ hadj⟩
      loopless := by
        constructor
        rintro ⟨⟨k, u⟩⟩ ⟨h, hadj⟩
        exact (Gs k).loopless.irrefl u hadj }
  refine ⟨V, G, ?_, ?_⟩
  · by_contra hne
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
    have hcolG : G.Colorable k :=
      SimpleGraph.chromaticNumber_le_iff_colorable.mp (le_of_eq hk.symm)
    obtain ⟨f⟩ := hcolG
    have hfk : (Gs k).Colorable k := by
      refine ⟨SimpleGraph.Coloring.mk (fun u => f (ULift.up ⟨k, u⟩)) ?_⟩
      intro u v huv
      exact f.valid ⟨rfl, huv⟩
    exact hcol k hfk
  · intro n
    unfold Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite
    by_cases hempty : (Erdos74.SimpleGraph.subgraphEdgeDistsToBipartite G n).Nonempty
    · have hmem : sSup (Erdos74.SimpleGraph.subgraphEdgeDistsToBipartite G n) ∈
          Erdos74.SimpleGraph.subgraphEdgeDistsToBipartite G n :=
        Nat.sSup_mem hempty (Erdos74.SimpleGraph.subgraphEdgeDistsToBipartite_bddAbove G n)
      rcases hmem with ⟨A, hn, hfin, heq⟩
      rw [← heq]
      let S : Finset V := hfin.toFinset
      have hScard : S.card = n := by
        rw [← hn, Set.ncard_eq_toFinset_card _ hfin]
      let K : Finset ℕ := S.image (fun v => v.down.1)
      let comp : ∀ k : ℕ, Finset (Fin (N k)) :=
        fun k => Finset.univ.filter (fun u => ULift.up ⟨k, u⟩ ∈ S)
      have hsum_card : ∑ k ∈ K, (comp k).card = n := by
        rw [← hScard, ← Finset.card_sigma]
        refine Finset.card_bij (fun p _ => ULift.up ⟨p.1, p.2⟩) ?_ ?_ ?_
        · intro p hp
          rw [Finset.mem_sigma] at hp
          exact (Finset.mem_filter.mp hp.2).2
        · rintro ⟨k1, u1⟩ _ ⟨k2, u2⟩ _ h
          have h' : (⟨k1, u1⟩ : Σ k, Fin (N k)) = ⟨k2, u2⟩ := ULift.up.inj h
          exact h'
        · intro v hv
          refine ⟨⟨v.down.1, v.down.2⟩, ?_, ?_⟩
          · rw [Finset.mem_sigma]
            refine ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            rcases v with ⟨⟨k, u⟩⟩
            exact hv
          · rcases v with ⟨⟨k, u⟩⟩
            rfl
      choose ck Ek hEk_card hEk_col using fun k => hbip k (comp k)
      let liftE : ∀ k : ℕ, Finset (Sym2 V) :=
        fun k => (Ek k).image (Sym2.map fun u => ULift.up ⟨k, u⟩)
      let Eall : Finset (Sym2 V) := K.biUnion liftE
      let E : Set (Sym2 V) := (Eall : Set (Sym2 V)) ∩ A.edgeSet
      have hE_sub : E ⊆ A.edgeSet := Set.inter_subset_right
      have hE_bip : SimpleGraph.IsBipartite (A.deleteEdges E).coe := by
        refine ⟨SimpleGraph.Coloring.mk
          (fun v => if ck v.1.down.1 v.1.down.2 then (1 : Fin 2) else 0) ?_⟩
        rintro ⟨⟨⟨k1, u1⟩⟩, hv1⟩ ⟨⟨⟨k2, u2⟩⟩, hv2⟩ hadj
        have hAadj : A.Adj (ULift.up ⟨k1, u1⟩) (ULift.up ⟨k2, u2⟩) := hadj.1
        have hnotE : s(ULift.up ⟨k1, u1⟩, ULift.up ⟨k2, u2⟩) ∉ E := hadj.2
        have hGadj : G.Adj (ULift.up ⟨k1, u1⟩) (ULift.up ⟨k2, u2⟩) := A.adj_sub hAadj
        rcases hGadj with ⟨hk, hadj_k⟩
        dsimp at hk hadj_k
        subst hk
        have hv1S : ULift.up ⟨k1, u1⟩ ∈ S := (Set.Finite.mem_toFinset hfin).mpr hv1
        have hv2S : ULift.up ⟨k1, u2⟩ ∈ S := (Set.Finite.mem_toFinset hfin).mpr hv2
        have hkK : k1 ∈ K := Finset.mem_image.mpr ⟨ULift.up ⟨k1, u1⟩, hv1S, rfl⟩
        have hu1 : u1 ∈ comp k1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv1S⟩
        have hu2 : u2 ∈ comp k1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv2S⟩
        have hnotEk : s(u1, u2) ∉ Ek k1 := by
          intro hmemEk
          apply hnotE
          refine ⟨?_, A.mem_edgeSet.mpr hAadj⟩
          rw [Finset.mem_coe, Finset.mem_biUnion]
          refine ⟨k1, hkK, Finset.mem_image.mpr ⟨s(u1, u2), hmemEk, ?_⟩⟩
          rfl
        have hne : ck k1 u1 ≠ ck k1 u2 := hEk_col k1 u1 hu1 u2 hu2 hadj_k hnotEk
        dsimp
        cases h1 : ck k1 u1 <;> cases h2 : ck k1 u2 <;> simp_all
      have hmin_le : Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤ E.ncard := by
        apply Nat.sInf_le
        exact ⟨E, hE_sub, hE_bip, rfl⟩
      have hncard_le : E.ncard ≤ Eall.card := by
        calc E.ncard ≤ (Eall : Set (Sym2 V)).ncard :=
              Set.ncard_le_ncard Set.inter_subset_left Eall.finite_toSet
          _ = Eall.card := Set.ncard_coe_finset Eall
      have hEall_le : Eall.card ≤ ∑ k ∈ K, (Ek k).card := by
        calc Eall.card ≤ ∑ k ∈ K, (liftE k).card := Finset.card_biUnion_le
          _ ≤ ∑ k ∈ K, (Ek k).card :=
              Finset.sum_le_sum fun k _ => Finset.card_image_le
      have hreal : (Erdos74.SimpleGraph.minEdgeDistToBipartite A : ℝ) ≤ Real.sqrt n := by
        calc (Erdos74.SimpleGraph.minEdgeDistToBipartite A : ℝ)
            ≤ (E.ncard : ℝ) := Nat.cast_le.mpr hmin_le
          _ ≤ (Eall.card : ℝ) := Nat.cast_le.mpr hncard_le
          _ ≤ ((∑ k ∈ K, (Ek k).card : ℕ) : ℝ) := Nat.cast_le.mpr hEall_le
          _ = ∑ k ∈ K, ((Ek k).card : ℝ) := Nat.cast_sum _ _
          _ ≤ ∑ k ∈ K, ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) * Real.sqrt (comp k).card :=
              Finset.sum_le_sum fun k _ => hEk_card k
          _ ≤ Real.sqrt (∑ k ∈ K, (comp k).card : ℕ) :=
              weighted_sqrt_sum_le K (fun k => (comp k).card)
          _ = Real.sqrt n := by rw [hsum_card]
      exact hreal
    · rw [Set.not_nonempty_iff_eq_empty.mp hempty, csSup_empty]
      simp [Real.sqrt_nonneg]

end OMA.R_Erdos74_erdos_74_variants_sqrt_R1
