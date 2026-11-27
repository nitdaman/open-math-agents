import FormalConjectures.ErdosProblems.«650»

-- Problem: Erdős Problem 650 — erdos selfridge
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/650.lean:103 (declaration Erdos650.erdos_650.variants.erdos_selfridge)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

private lemma exists_modEq_finset {ι : Type*} (s : Finset ι) (r a : ι → ℕ)
    (hcop : (↑s : Set ι).Pairwise (fun i j => Nat.Coprime (a i) (a j))) :
    ∃ M : ℕ, ∀ i ∈ s, M ≡ r i [MOD a i] := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨M₀, hM₀⟩ := ih (hcop.mono (Finset.coe_subset.mpr (Finset.subset_insert i s)))
    have hcop_prod : Nat.Coprime (∏ j ∈ s, a j) (a i) := by
      refine Nat.Coprime.prod_left fun j hj => ?_
      exact hcop (Finset.mem_insert_of_mem hj) (Finset.mem_insert_self i s) (fun h => hi (h ▸ hj))
    obtain ⟨M, hM1, hM2⟩ := Nat.chineseRemainder hcop_prod M₀ (r i)
    refine ⟨M, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hM2
    · exact (hM1.of_dvd (Finset.dvd_prod_of_mem a hj)).trans (hM₀ j hj)

private lemma dvd_sub_of_modEq {a M u : ℕ} (hu : u ≤ M) (h : M ≡ u [MOD a]) : a ∣ M - u := by
  have h1 : (a : ℤ) ∣ (u : ℤ) - (M : ℤ) := Nat.modEq_iff_dvd.mp h
  have h2 : (a : ℤ) ∣ ((M - u : ℕ) : ℤ) := by
    rw [Nat.cast_sub hu]
    have : ((M : ℤ) - (u : ℤ)) = -((u : ℤ) - (M : ℤ)) := by ring
    rw [this]
    exact dvd_neg.mpr h1
  exact Int.natCast_dvd_natCast.mp h2

theorem OMA.solution : type_of% @Erdos650.erdos_650.variants.erdos_selfridge := by
  intro m
  dsimp only [Erdos650.f]
  refine csSup_le ⟨0, fun _ _ _ _ _ _ => ⟨Fin.elim0, Fin.elim0,
    Function.injective_of_subsingleton _, Function.injective_of_subsingleton _,
    fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩ fun r hr => ?_
  by_cases hm : m = 0
  · subst hm
    have h0 := hr 1 ∅ (Finset.empty_subset _) (by simp) 1 le_rfl
    obtain ⟨fa, _, _, _, hfa, _, _⟩ := h0
    by_contra hr0
    have hpos : 0 < r := by omega
    exact absurd (hfa ⟨0, hpos⟩) (by simp)
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    have hm2_pos : 0 < m ^ 2 := sq_pos_of_pos hm_pos
    let K : ℕ := Nat.factorial (m ^ 2)
    have hK_pos : 0 < K := Nat.factorial_pos (m ^ 2)
    let u : Fin m → ℕ := fun i => K * (m ^ 2 + i.1) + 1
    let v : Fin m → ℕ := fun j => K * (m ^ 2 + m * j.1)
    let a : Fin m × Fin m → ℕ := fun p => u p.1 + v p.2
    let N : ℕ := 3 * m ^ 2 * K
    have ha_eq : ∀ p : Fin m × Fin m, a p = K * (2 * m ^ 2 + p.1.1 + m * p.2.1) + 1 := by
      intro ⟨i, j⟩
      dsimp only [a, u, v]
      ring
    have ha_pos : ∀ p, 0 < a p := fun p => by rw [ha_eq]; exact Nat.succ_pos _
    have hij_lt : ∀ p : Fin m × Fin m, p.1.1 + m * p.2.1 < m ^ 2 := by
      intro ⟨i, j⟩
      calc i.1 + m * j.1 < m + m * j.1 := Nat.add_lt_add_right i.2 _
        _ = m * (j.1 + 1) := by ring
        _ ≤ m * m := Nat.mul_le_mul_left m j.2
        _ = m ^ 2 := (sq m).symm
    have hidx_inj : ∀ p q : Fin m × Fin m, p.1.1 + m * p.2.1 = q.1.1 + m * q.2.1 → p = q := by
      intro ⟨i1, j1⟩ ⟨i2, j2⟩ h
      have hmod : (i1.1 + m * j1.1) % m = (i2.1 + m * j2.1) % m := congrArg (· % m) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i1.2, Nat.mod_eq_of_lt i2.2] at hmod
      have hi : i1 = i2 := Fin.ext hmod
      subst hi
      have hj : j1 = j2 := Fin.ext (Nat.mul_left_cancel hm_pos (Nat.add_left_cancel h))
      exact Prod.ext rfl hj
    have ha_inj : Function.Injective a := by
      intro p q h
      have h1 : K * (2 * m ^ 2 + p.1.1 + m * p.2.1) + 1 =
          K * (2 * m ^ 2 + q.1.1 + m * q.2.1) + 1 := by
        simpa only [ha_eq] using h
      have h2 : 2 * m ^ 2 + p.1.1 + m * p.2.1 = 2 * m ^ 2 + q.1.1 + m * q.2.1 :=
        Nat.mul_left_cancel hK_pos (Nat.add_right_cancel h1)
      exact hidx_inj p q (by omega)
    let A : Finset ℕ := (Finset.univ : Finset (Fin m × Fin m)).image a
    have hA_card : A.card = m ^ 2 := by
      rw [Finset.card_image_of_injective _ ha_inj, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, sq]
    have hA_sub : A ⊆ Finset.Icc 1 N := by
      intro y hy
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hy
      rw [Finset.mem_Icc]
      refine ⟨ha_pos p, ?_⟩
      have hp_lt := hij_lt p
      have hsum_le : 2 * m ^ 2 + p.1.1 + m * p.2.1 ≤ 3 * m ^ 2 - 1 := by omega
      calc a p = K * (2 * m ^ 2 + p.1.1 + m * p.2.1) + 1 := ha_eq p
        _ ≤ K * (3 * m ^ 2 - 1) + K := Nat.add_le_add (Nat.mul_le_mul_left K hsum_le) hK_pos
        _ = K * (3 * m ^ 2 - 1 + 1) := by ring
        _ = 3 * m ^ 2 * K := by rw [Nat.sub_add_cancel (by omega : 1 ≤ 3 * m ^ 2)]; ring
    have ha_cop : (↑(Finset.univ : Finset (Fin m × Fin m)) : Set (Fin m × Fin m)).Pairwise
        (fun p q => Nat.Coprime (a p) (a q)) := by
      intro p _ q _ hpq
      by_contra hnc
      set g := Nat.gcd (a p) (a q)
      set k := g.minFac
      have hk_prime : Nat.Prime k := Nat.minFac_prime hnc
      have hkg : k ∣ g := Nat.minFac_dvd g
      have hkp : k ∣ a p := hkg.trans (Nat.gcd_dvd_left _ _)
      have hkq : k ∣ a q := hkg.trans (Nat.gcd_dvd_right _ _)
      have hk_ndvd_K : ¬ k ∣ K := by
        intro hdiv
        have h1 : k ∣ 1 := (Nat.dvd_add_right (hdiv.mul_right (2 * m ^ 2 + p.1.1 + m * p.2.1))).mp
          (by simpa only [ha_eq] using hkp)
        exact hk_prime.not_dvd_one h1
      have hk_gt : m ^ 2 < k := by
        by_contra hle
        exact hk_ndvd_K (Nat.dvd_factorial hk_prime.pos (Nat.le_of_not_lt hle))
      have hkpZ : (k : ℤ) ∣ (a p : ℤ) := Int.natCast_dvd_natCast.mpr hkp
      have hkqZ : (k : ℤ) ∣ (a q : ℤ) := Int.natCast_dvd_natCast.mpr hkq
      have hsubZ : (k : ℤ) ∣ (K : ℤ) * ((p.1.1 + m * p.2.1 : ℤ) - (q.1.1 + m * q.2.1 : ℤ)) := by
        have hpZ : (a p : ℤ) = (K : ℤ) * (2 * (m : ℤ) ^ 2 + p.1.1 + m * p.2.1) + 1 := by
          exact_mod_cast ha_eq p
        have hqZ : (a q : ℤ) = (K : ℤ) * (2 * (m : ℤ) ^ 2 + q.1.1 + m * q.2.1) + 1 := by
          exact_mod_cast ha_eq q
        have hdiff : (K : ℤ) * ((p.1.1 + m * p.2.1 : ℤ) - (q.1.1 + m * q.2.1 : ℤ)) =
            (a p : ℤ) - (a q : ℤ) := by
          rw [hpZ, hqZ]
          ring
        rw [hdiff]
        exact dvd_sub hkpZ hkqZ
      have hdvd_abs : k ∣ K * ((p.1.1 + m * p.2.1 : ℤ) - (q.1.1 + m * q.2.1 : ℤ)).natAbs := by
        have h1 : (k : ℤ) ∣ (((K : ℤ) * ((p.1.1 + m * p.2.1 : ℤ) - (q.1.1 + m * q.2.1 : ℤ))).natAbs : ℤ) :=
          Int.dvd_natAbs.mpr hsubZ
        rw [Int.natAbs_mul, Int.natAbs_natCast] at h1
        exact Int.natCast_dvd_natCast.mp h1
      have hdvd_d : k ∣ ((p.1.1 + m * p.2.1 : ℤ) - (q.1.1 + m * q.2.1 : ℤ)).natAbs :=
        (hk_prime.dvd_mul.mp hdvd_abs).resolve_left hk_ndvd_K
      have hd_ne : ((p.1.1 + m * p.2.1 : ℤ) - (q.1.1 + m * q.2.1 : ℤ)).natAbs ≠ 0 := by
        intro h0
        have hsub0 : (p.1.1 + m * p.2.1 : ℤ) - (q.1.1 + m * q.2.1 : ℤ) = 0 := Int.natAbs_eq_zero.mp h0
        have heq : p.1.1 + m * p.2.1 = q.1.1 + m * q.2.1 := by omega
        exact hpq (hidx_inj p q heq)
      have hk_le_d : k ≤ ((p.1.1 + m * p.2.1 : ℤ) - (q.1.1 + m * q.2.1 : ℤ)).natAbs :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hd_ne) hdvd_d
      have hd_lt : ((p.1.1 + m * p.2.1 : ℤ) - (q.1.1 + m * q.2.1 : ℤ)).natAbs < m ^ 2 := by
        have hp_lt := hij_lt p
        have hq_lt := hij_lt q
        omega
      omega
    obtain ⟨M₀, hM₀⟩ := exists_modEq_finset Finset.univ (fun p => u p.1) a ha_cop
    let P : ℕ := ∏ p : Fin m × Fin m, a p
    have hP_pos : 0 < P := Finset.prod_pos fun p _ => ha_pos p
    let M : ℕ := M₀ + (N + 1) * P
    have hM_ge : N + 1 ≤ M := calc
      N + 1 = (N + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (N + 1) * P := Nat.mul_le_mul_left _ hP_pos
      _ ≤ M₀ + (N + 1) * P := Nat.le_add_left _ _
    have hu_le_N : ∀ i : Fin m, u i ≤ N := by
      intro i
      dsimp only [u, N]
      have hi1 : m ^ 2 + i.1 ≤ 2 * m ^ 2 - 1 := by
        have : i.1 < m := i.2
        have : m ≤ m ^ 2 := by nlinarith
        omega
      calc K * (m ^ 2 + i.1) + 1 ≤ K * (2 * m ^ 2 - 1) + K :=
            Nat.add_le_add (Nat.mul_le_mul_left K hi1) hK_pos
        _ = K * (2 * m ^ 2 - 1 + 1) := by ring
        _ = 2 * m ^ 2 * K := by rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * m ^ 2)]; ring
        _ ≤ 3 * m ^ 2 * K := by nlinarith
    have hM_dvd_left : ∀ p : Fin m × Fin m, a p ∣ M - u p.1 := by
      intro p
      have hdvdP : a p ∣ P := Finset.dvd_prod_of_mem a (Finset.mem_univ p)
      have hM_mod : M ≡ u p.1 [MOD a p] := by
        have h1 : M ≡ M₀ [MOD a p] := by
          rw [Nat.ModEq]
          have : (N + 1) * P % a p = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdvdP _)
          simp [M, Nat.add_mod, this]
        exact h1.trans (hM₀ p (Finset.mem_univ p))
      exact dvd_sub_of_modEq (le_trans (hu_le_N p.1) (by omega)) hM_mod
    have hM_dvd_right : ∀ p : Fin m × Fin m, a p ∣ M + v p.2 := by
      intro p
      have hsum : M + v p.2 = (M - u p.1) + a p := by
        have huM : u p.1 ≤ M := le_trans (hu_le_N p.1) (by omega)
        dsimp only [a]
        omega
      rw [hsum]
      exact dvd_add (hM_dvd_left p) dvd_rfl
    let x : ℝ := ((M - N : ℕ) : ℝ)
    have hx1 : (1 : ℝ) ≤ x := by
      dsimp only [x]
      exact_mod_cast (by omega : 1 ≤ M - N)
    obtain ⟨fa, fb, _, hfb_inj, hfa_mem, hfb_mem, hdvd⟩ := hr N A hA_sub hA_card x hx1
    let B : Finset ℕ := (Finset.univ.image (fun i : Fin m => M - u i)) ∪
        (Finset.univ.image (fun j : Fin m => M + v j))
    have hB_card : B.card ≤ 2 * m := by
      calc B.card ≤ (Finset.univ.image (fun i : Fin m => M - u i)).card +
            (Finset.univ.image (fun j : Fin m => M + v j)).card := Finset.card_union_le _ _
        _ ≤ (Finset.univ : Finset (Fin m)).card + (Finset.univ : Finset (Fin m)).card :=
            Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ = 2 * m := by simp [two_mul]
    have hfb_B : ∀ k : Fin r, fb k ∈ B := by
      intro k
      obtain ⟨p, _, hpa⟩ := Finset.mem_image.mp (hfa_mem k)
      have hdvd_y : a p ∣ fb k := hpa ▸ hdvd k
      obtain ⟨hx_lt, hlt_x2N⟩ := hfb_mem k
      have hy_gt : M - N < fb k := by
        dsimp only [x] at hx_lt
        exact_mod_cast hx_lt
      have hy_lt : fb k < M + N := by
        have hx2N : x + 2 * (N : ℝ) = ((M + N : ℕ) : ℝ) := by
          dsimp only [x]
          rw [Nat.cast_sub (by omega : N ≤ M)]
          push_cast
          ring
        rw [hx2N] at hlt_x2N
        exact_mod_cast hlt_x2N
      have huM : u p.1 ≤ M := le_trans (hu_le_N p.1) (by omega)
      have h2u_v : N < 2 * u p.1 + v p.2 := by
        dsimp only [u, v, N]
        have h1 : 3 * m ^ 2 * K = 2 * (K * m ^ 2) + K * m ^ 2 := by ring
        have h2 : 2 * (K * (m ^ 2 + p.1.1) + 1) + K * (m ^ 2 + m * p.2.1) =
            2 * (K * m ^ 2) + K * m ^ 2 + (2 * (K * p.1.1) + K * (m * p.2.1)) + 2 := by ring
        omega
      have hu_2v : N < u p.1 + 2 * v p.2 := by
        dsimp only [u, v, N]
        have h1 : 3 * m ^ 2 * K = K * m ^ 2 + 2 * (K * m ^ 2) := by ring
        have h2 : K * (m ^ 2 + p.1.1) + 1 + 2 * (K * (m ^ 2 + m * p.2.1)) =
            K * m ^ 2 + 2 * (K * m ^ 2) + (K * p.1.1 + 2 * (K * (m * p.2.1))) + 1 := by ring
        omega
      rcases lt_trichotomy (fb k) (M - u p.1) with h1 | h1 | h1
      · have hd1 : a p ∣ M - u p.1 - fb k := Nat.dvd_sub (hM_dvd_left p) hdvd_y
        have hle1 : a p ≤ M - u p.1 - fb k := Nat.le_of_dvd (by omega) hd1
        have : a p = u p.1 + v p.2 := rfl
        omega
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, h1.symm⟩)
      · rcases lt_trichotomy (fb k) (M + v p.2) with h2 | h2 | h2
        · have hd2 : a p ∣ fb k - (M - u p.1) := Nat.dvd_sub hdvd_y (hM_dvd_left p)
          have hle2 : a p ≤ fb k - (M - u p.1) := Nat.le_of_dvd (by omega) hd2
          have : a p = u p.1 + v p.2 := rfl
          omega
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, h2.symm⟩)
        · have hd3 : a p ∣ fb k - (M + v p.2) := Nat.dvd_sub hdvd_y (hM_dvd_right p)
          have hle3 : a p ≤ fb k - (M + v p.2) := Nat.le_of_dvd (by omega) hd3
          have : a p = u p.1 + v p.2 := rfl
          omega
    have hr_le_B : r ≤ B.card := by
      have hinj : Function.Injective (fun k : Fin r => (⟨fb k, hfb_B k⟩ : B)) := by
        intro k1 k2 h
        exact hfb_inj (congrArg Subtype.val h)
      simpa using Fintype.card_le_of_injective _ hinj
    exact le_trans hr_le_B hB_card
