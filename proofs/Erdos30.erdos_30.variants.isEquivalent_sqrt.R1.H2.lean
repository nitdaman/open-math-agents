import OMAReductions.R_Erdos30_erdos_30_variants_isEquivalent_sqrt_R1

-- Step Erdos30.erdos_30.variants.isEquivalent_sqrt.R1.H2: hypothesis H2 of reduction Erdos30.erdos_30.variants.isEquivalent_sqrt.R1
-- Credit: @malikfassi
-- H2 := ∀ N : ℕ, (Erdos30.h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1
-- H2 is word for word the statement of the Lindström variant of Erdős Problem 30, which has a
-- merged proof in this repository (proofs/Erdos30.erdos_30.variants.lindstrom.lean). The two
-- lemmas and the final argument below are that proof, restated for this step; nothing new is
-- claimed here beyond the bookkeeping.

lemma oma_sum_ge_of_pos (D : Finset ℕ) (hD : ∀ x ∈ D, 1 ≤ x) :
    D.card * (D.card + 1) ≤ 2 * ∑ x ∈ D, x := by
  let e := D.orderIsoOfFin rfl
  have hge : ∀ i : ℕ, (hi : i < D.card) → i + 1 ≤ (e ⟨i, hi⟩ : ℕ) := by
    intro i
    induction i with
    | zero =>
      intro hi
      exact hD _ (e ⟨0, hi⟩).2
    | succ i ih =>
      intro hi
      have hi' : i < D.card := by omega
      have hprev := ih hi'
      have hlt : (e ⟨i, hi'⟩ : ℕ) < (e ⟨i + 1, hi⟩ : ℕ) :=
        e.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
      omega
  have hsum_eq : ∑ x ∈ D, x = ∑ i : Fin D.card, (e i : ℕ) := by
    rw [← Finset.sum_coe_sort D (fun x => x)]
    exact (Fintype.sum_equiv e.toEquiv (fun i => (e i : ℕ)) (fun x : ↥D => (x : ℕ)) (fun _ => rfl)).symm
  rw [hsum_eq]
  have hle : ∑ i : Fin D.card, (i.val + 1) ≤ ∑ i : Fin D.card, (e i : ℕ) :=
    Finset.sum_le_sum fun i _ => hge i.val i.isLt
  have hid : 2 * ∑ i : Fin D.card, (i.val + 1) = D.card * (D.card + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i + 1)]
    have : 2 * ∑ i ∈ Finset.range D.card, (i + 1) = D.card * (D.card + 1) := by
      induction D.card with
      | zero => simp
      | succ m ihm =>
        rw [Finset.sum_range_succ, mul_add, ihm]
        ring
    exact this
  omega

lemma oma_sidon_lindstrom (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hS : IsSidon (A : Set ℕ)) :
    (A.card : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  by_cases hN0 : N = 0
  · subst hN0
    have hAe : A = ∅ := Finset.subset_empty.mp (by simpa using hA)
    simp [hAe]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hNreal : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
  set k := A.card
  set u : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ)
  set r : ℕ := Nat.floor u + 1
  have hu_nonneg : 0 ≤ u := by positivity
  have hr_gt : u < (r : ℝ) := by
    have := Nat.lt_floor_add_one u
    push_cast [r]
    exact this
  have hr_le : (r : ℝ) ≤ u + 1 := by
    have := Nat.floor_le hu_nonneg
    push_cast [r]
    linarith
  have hr_pos : 1 ≤ r := by omega
  by_cases hkr : k ≤ r
  · have h1 : (k : ℝ) ≤ (r : ℝ) := Nat.cast_le.mpr hkr
    have h2 : (0 : ℝ) ≤ (N : ℝ).sqrt := Real.sqrt_nonneg _
    linarith
  have hrk : r < k := by omega
  let e := A.orderIsoOfFin rfl
  let a : Fin k → ℕ := fun i => (e i : ℕ)
  have ha_mono : StrictMono a := fun i j hij => e.strictMono hij
  have ha_mem : ∀ i : Fin k, a i ∈ A := fun i => (e i).2
  have ha_le : ∀ i : Fin k, a i ≤ N := fun i => (Finset.mem_Icc.mp (hA (ha_mem i))).2
  let P : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 r).biUnion fun d => (Finset.range (k - d)).image fun j => (d, j)
  have hP_mem : ∀ p ∈ P, 1 ≤ p.1 ∧ p.1 ≤ r ∧ p.2 + p.1 < k := by
    intro ⟨d, j⟩ hp
    simp only [P, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image, Finset.mem_range] at hp
    rcases hp with ⟨d', ⟨hd1, hd2⟩, j', hj', heq⟩
    rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
    exact ⟨hd1, hd2, by omega⟩
  let diffFn : ℕ × ℕ → ℕ := fun p =>
    if h : p.2 + p.1 < k then a ⟨p.2 + p.1, h⟩ - a ⟨p.2, by omega⟩ else 0
  have hdiff_inj : Set.InjOn diffFn (P : Set (ℕ × ℕ)) := by
    intro ⟨d₁, j₁⟩ h1 ⟨d₂, j₂⟩ h2 heq
    have hm1 := hP_mem (d₁, j₁) (Finset.mem_coe.mp h1)
    have hm2 := hP_mem (d₂, j₂) (Finset.mem_coe.mp h2)
    have hlt1 : a ⟨j₁, by omega⟩ < a ⟨j₁ + d₁, hm1.2.2⟩ :=
      ha_mono (Fin.mk_lt_mk.mpr (by omega))
    have hlt2 : a ⟨j₂, by omega⟩ < a ⟨j₂ + d₂, hm2.2.2⟩ :=
      ha_mono (Fin.mk_lt_mk.mpr (by omega))
    simp only [diffFn, dif_pos hm1.2.2, dif_pos hm2.2.2] at heq
    have hpair := Finset.IsSidon.eq_of_tsub hS
      (ha_mem ⟨j₁ + d₁, hm1.2.2⟩) (ha_mem ⟨j₁, by omega⟩)
      (ha_mem ⟨j₂ + d₂, hm2.2.2⟩) (ha_mem ⟨j₂, by omega⟩)
      hlt1 hlt2 heq
    have hj_eq : j₁ = j₂ := by
      have := ha_mono.injective hpair.2
      exact congrArg Fin.val this
    have hjd_eq : j₁ + d₁ = j₂ + d₂ := by
      have := ha_mono.injective hpair.1
      exact congrArg Fin.val this
    ext <;> omega
  let D : Finset ℕ := P.image diffFn
  have hD_card : D.card = P.card := Finset.card_image_of_injOn hdiff_inj
  have hD_pos : ∀ x ∈ D, 1 ≤ x := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨⟨d, j⟩, hp, rfl⟩
    have hm := hP_mem (d, j) hp
    have hlt : a ⟨j, by omega⟩ < a ⟨j + d, hm.2.2⟩ :=
      ha_mono (Fin.mk_lt_mk.mpr (by omega))
    simp only [diffFn, dif_pos hm.2.2]
    omega
  have hP_card : P.card = r * k - r * (r + 1) / 2 := by
    have hdisj : (Finset.Icc 1 r : Set ℕ).PairwiseDisjoint fun d =>
        (Finset.range (k - d)).image fun j => (d, j) := by
      intro d₁ _ d₂ _ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro ⟨a₁, b₁⟩ h1 h2
      simp only [Finset.mem_image] at h1 h2
      rcases h1 with ⟨_, _, e1⟩
      rcases h2 with ⟨_, _, e2⟩
      have := congrArg Prod.fst (e1.trans e2.symm)
      exact hne this
    dsimp [P]
    rw [Finset.card_biUnion hdisj]
    have hterm : ∀ d ∈ Finset.Icc 1 r,
        ((Finset.range (k - d)).image fun j => (d, j)).card = k - d := by
      intro d _
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro j₁ j₂ h; exact congrArg Prod.snd h
    rw [Finset.sum_congr rfl hterm]
    have hsum_d : ∑ d ∈ Finset.Icc 1 r, (k - d) = r * k - ∑ d ∈ Finset.Icc 1 r, d := by
      have h1 : ∑ d ∈ Finset.Icc 1 r, (k - d) + ∑ d ∈ Finset.Icc 1 r, d =
          ∑ d ∈ Finset.Icc 1 r, k := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hdle : d ≤ k := by
          have := (Finset.mem_Icc.mp hd).2
          omega
        exact Nat.sub_add_cancel hdle
      have h2 : ∑ _d ∈ Finset.Icc 1 r, k = r * k := by
        simp [Nat.card_Icc]
      omega
    have htri : 2 * ∑ d ∈ Finset.Icc 1 r, d = r * (r + 1) := by
      induction r with
      | zero => simp
      | succ m ihm =>
        rw [Finset.sum_Icc_succ_top (by omega), mul_add, ihm]
        ring
    rw [hsum_d, show ∑ d ∈ Finset.Icc 1 r, d = r * (r + 1) / 2 by omega]
  have h_lower := oma_sum_ge_of_pos D hD_pos
  rw [hD_card] at h_lower
  have hsum_D_eq : ∑ x ∈ D, x = ∑ p ∈ P, diffFn p := Finset.sum_image (fun x hx y hy h => hdiff_inj hx hy h)
  have h_upper_nat : ∑ p ∈ P, diffFn p ≤ (r * (r + 1) / 2) * N := by
    have hdisj : (Finset.Icc 1 r : Set ℕ).PairwiseDisjoint fun d =>
        (Finset.range (k - d)).image fun j => (d, j) := by
      intro d₁ _ d₂ _ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro ⟨a₁, b₁⟩ h1 h2
      simp only [Finset.mem_image] at h1 h2
      rcases h1 with ⟨_, _, e1⟩
      rcases h2 with ⟨_, _, e2⟩
      exact hne (congrArg Prod.fst (e1.trans e2.symm))
    dsimp [P]
    rw [Finset.sum_biUnion hdisj]
    have h_each : ∀ d ∈ Finset.Icc 1 r,
        ∑ p ∈ (Finset.range (k - d)).image (fun j => (d, j)), diffFn p ≤ d * N := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdr : d ≤ r := (Finset.mem_Icc.mp hd).2
      have hdk : d < k := by omega
      rw [Finset.sum_image (fun j₁ _ j₂ _ h => congrArg Prod.snd h)]
      let a' : ℕ → ℝ := fun i => if h : i < k then (a ⟨i, h⟩ : ℝ) else 0
      have hcast_sum : ((∑ j ∈ Finset.range (k - d), diffFn (d, j) : ℕ) : ℝ) =
          ∑ j ∈ Finset.range (k - d), (a' (j + d) - a' j) := by
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        have hjd : j + d < k := by omega
        have hj' : j < k := by omega
        have hle : a ⟨j, hj'⟩ ≤ a ⟨j + d, hjd⟩ :=
          (ha_mono.monotone (Fin.mk_le_mk.mpr (by omega)))
        simp only [diffFn, dif_pos hjd, a', dif_pos hjd, dif_pos hj']
        exact Nat.cast_sub hle
      have htele : ∑ j ∈ Finset.range (k - d), (a' (j + d) - a' j) ≤ (d : ℝ) * (N : ℝ) := by
        rw [Finset.sum_sub_distrib]
        have hshift : ∑ j ∈ Finset.range (k - d), a' (j + d) = ∑ i ∈ Finset.Ico d k, a' i := by
          refine Finset.sum_bij (fun j _ => j + d) ?_ ?_ ?_ ?_
          · intro j hj; rw [Finset.mem_range] at hj; rw [Finset.mem_Ico]; omega
          · intro j₁ _ j₂ _ h; omega
          · intro i hi; rw [Finset.mem_Ico] at hi; exact ⟨i - d, Finset.mem_range.mpr (by omega), by omega⟩
          · intro _ _; rfl
        rw [hshift]
        have hsplit1 : ∑ i ∈ Finset.Ico d k, a' i =
            ∑ i ∈ (Finset.Ico d k) ∩ (Finset.range (k - d)), a' i +
            ∑ i ∈ (Finset.Ico d k) \ (Finset.range (k - d)), a' i :=
          (Finset.sum_inter_add_sum_sdiff _ _ _).symm
        have hsplit2 : ∑ i ∈ Finset.range (k - d), a' i =
            ∑ i ∈ (Finset.range (k - d)) ∩ (Finset.Ico d k), a' i +
            ∑ i ∈ (Finset.range (k - d)) \ (Finset.Ico d k), a' i :=
          (Finset.sum_inter_add_sum_sdiff _ _ _).symm
        rw [hsplit1, hsplit2, Finset.inter_comm (Finset.range (k - d)) (Finset.Ico d k)]
        have hnonneg : 0 ≤ ∑ i ∈ (Finset.range (k - d)) \ (Finset.Ico d k), a' i := by
          refine Finset.sum_nonneg fun i _ => ?_
          dsimp [a']; split_ifs <;> positivity
        have hsub_ico : (Finset.Ico d k) \ (Finset.range (k - d)) ⊆ Finset.Ico (k - d) k := by
          intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_range] at hx ⊢
          omega
        have hcard_le : ((Finset.Ico d k) \ (Finset.range (k - d))).card ≤ d := by
          have := Finset.card_le_card hsub_ico
          rw [Nat.card_Ico] at this
          omega
        have hbound : ∑ i ∈ (Finset.Ico d k) \ (Finset.range (k - d)), a' i ≤
            ((Finset.Ico d k) \ (Finset.range (k - d))).card * (N : ℝ) := by
          calc ∑ i ∈ (Finset.Ico d k) \ (Finset.range (k - d)), a' i
            _ ≤ ∑ _i ∈ (Finset.Ico d k) \ (Finset.range (k - d)), (N : ℝ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hik : i < k := (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hi).1).2
              simp only [a', dif_pos hik]
              exact_mod_cast ha_le ⟨i, hik⟩
            _ = _ := by simp
        have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        have hcard_r : (((Finset.Ico d k) \ (Finset.range (k - d))).card : ℝ) ≤ (d : ℝ) :=
          Nat.cast_le.mpr hcard_le
        nlinarith
      exact_mod_cast hcast_sum.symm ▸ htele
    calc ∑ d ∈ Finset.Icc 1 r, ∑ p ∈ (Finset.range (k - d)).image (fun j => (d, j)), diffFn p
      _ ≤ ∑ d ∈ Finset.Icc 1 r, d * N := Finset.sum_le_sum h_each
      _ = (∑ d ∈ Finset.Icc 1 r, d) * N := (Finset.sum_mul _ _ _).symm
      _ = (r * (r + 1) / 2) * N := by
        congr 1
        have htri : 2 * ∑ d ∈ Finset.Icc 1 r, d = r * (r + 1) := by
          induction r with
          | zero => simp
          | succ m ihm =>
            rw [Finset.sum_Icc_succ_top (by omega), mul_add, ihm]
            ring
        omega
  have hineq_nat : P.card * (P.card + 1) ≤ r * (r + 1) * N := by
    have h1 : P.card * (P.card + 1) ≤ 2 * (r * (r + 1) / 2 * N) := by linarith
    have heven : 2 ∣ r * (r + 1) := Nat.even_mul_succ_self r |>.two_dvd
    have h2 : 2 * (r * (r + 1) / 2 * N) = r * (r + 1) * N := by
      rw [← mul_assoc, Nat.mul_div_cancel' heven]
    linarith
  have hP_real : (P.card : ℝ) = (r : ℝ) * (k : ℝ) - (r : ℝ) * ((r : ℝ) + 1) / 2 := by
    have heven : 2 ∣ r * (r + 1) := Nat.even_mul_succ_self r |>.two_dvd
    have hle : r * (r + 1) / 2 ≤ r * k := by
      have : r * (r + 1) ≤ 2 * (r * k) := by
        nlinarith [show r + 1 ≤ k by omega]
      exact Nat.div_le_of_le_mul this
    rw [hP_card, Nat.cast_sub hle, Nat.cast_div heven (by norm_num)]
    push_cast
    ring
  have hineq_real : (P.card : ℝ) ^ 2 ≤ (r : ℝ) * ((r : ℝ) + 1) * (N : ℝ) := by
    have h1 : (P.card : ℝ) * ((P.card : ℝ) + 1) ≤ (r : ℝ) * ((r : ℝ) + 1) * (N : ℝ) := by
      exact_mod_cast hineq_nat
    have hPnn : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
    nlinarith
  by_contra! hgt
  have hu2 : u ^ 2 = (N : ℝ).sqrt := by
    dsimp [u]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hNreal.le]
    norm_num
  have hu4 : u ^ 4 = (N : ℝ) := by
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = ((N : ℝ).sqrt) ^ 2 := by rw [hu2]
      _ = (N : ℝ) := Real.sq_sqrt hNreal.le
  have hr_pos_r : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  have hP_gt : (r : ℝ) * ((N : ℝ).sqrt + u / 2) < (P.card : ℝ) := by
    rw [hP_real]
    nlinarith
  have hsqrt_nn : 0 ≤ (N : ℝ).sqrt := Real.sqrt_nonneg _
  have hP_sq_gt : (r : ℝ) ^ 2 * ((N : ℝ) + u * (N : ℝ).sqrt + u ^ 2 / 4) < (P.card : ℝ) ^ 2 := by
    have hpos_lhs : 0 ≤ (r : ℝ) * ((N : ℝ).sqrt + u / 2) := by positivity
    have h1 : ((r : ℝ) * ((N : ℝ).sqrt + u / 2)) ^ 2 < (P.card : ℝ) ^ 2 := by
      nlinarith
    have h2 : ((r : ℝ) * ((N : ℝ).sqrt + u / 2)) ^ 2 =
        (r : ℝ) ^ 2 * ((N : ℝ) + u * (N : ℝ).sqrt + u ^ 2 / 4) := by
      have : ((N : ℝ).sqrt) ^ 2 = (N : ℝ) := Real.sq_sqrt hNreal.le
      calc ((r : ℝ) * ((N : ℝ).sqrt + u / 2)) ^ 2
        _ = (r : ℝ) ^ 2 * (((N : ℝ).sqrt) ^ 2 + u * (N : ℝ).sqrt + u ^ 2 / 4) := by ring
        _ = (r : ℝ) ^ 2 * ((N : ℝ) + u * (N : ℝ).sqrt + u ^ 2 / 4) := by rw [this]
    linarith
  have h_gap : (r : ℝ) * ((r : ℝ) + 1) * (N : ℝ) <
      (r : ℝ) ^ 2 * ((N : ℝ) + u * (N : ℝ).sqrt + u ^ 2 / 4) := by
    have hu_pos : 0 < u := Real.rpow_pos_of_pos hNreal _
    have hsqrt_pos : 0 < (N : ℝ).sqrt := Real.sqrt_pos.mpr hNreal
    have hru : (N : ℝ) < (r : ℝ) * u * (N : ℝ).sqrt := by
      have hNeq : (N : ℝ) = u * u * (N : ℝ).sqrt := by
        calc (N : ℝ) = ((N : ℝ).sqrt) ^ 2 := (Real.sq_sqrt hNreal.le).symm
          _ = (N : ℝ).sqrt * (N : ℝ).sqrt := sq _
          _ = u ^ 2 * (N : ℝ).sqrt := by rw [hu2]
          _ = u * u * (N : ℝ).sqrt := by ring
      nlinarith
    have : 0 ≤ (r : ℝ) ^ 2 * (u ^ 2 / 4) := by positivity
    nlinarith
  linarith

theorem OMA.solution : OMA.R_Erdos30_erdos_30_variants_isEquivalent_sqrt_R1.H2 := by
  intro N
  dsimp [Erdos30.h, Finset.maxSidonSubsetCard]
  have hsup : ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ => IsSidon (B : Set ℕ)).sup
      Finset.card ≤ Nat.floor ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
    refine Finset.sup_le fun B hB => ?_
    rw [Finset.mem_filter, Finset.mem_powerset] at hB
    have hle := oma_sidon_lindstrom N B hB.1 hB.2
    exact Nat.le_floor hle
  have hle_real : ((Finset.maxSidonSubsetCard (Finset.Icc 1 N) : ℕ) : ℝ) ≤
      (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
    have h1 := Nat.cast_le (α := ℝ).mpr hsup
    have h2 : (Nat.floor ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) : ℝ) ≤
        (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 :=
      Nat.floor_le (by positivity)
    exact h1.trans h2
  exact_mod_cast hle_real
