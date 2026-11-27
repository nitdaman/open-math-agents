import FormalConjectures.Wikipedia.CramerConjecture

-- Problem: Westzynthius's Theorem
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/CramerConjecture.lean:137 (declaration CramerConjecture.cramer_conjecture.variants.westzynthius)
-- Credit: @mucoucah (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- One prime per survivor: if there are at least as many moduli as survivors, every survivor
gets its own modulus. -/
lemma OMA.one_by_one (S : Finset ℕ) : ∀ T : Finset ℕ, S.card ≤ T.card →
    ∃ a : ℕ → ℕ, ∀ j ∈ S, ∃ p ∈ T, j % p = a p := by
  classical
  induction S using Finset.induction_on with
  | empty => intro T _; exact ⟨fun _ => 0, by simp⟩
  | insert j S' hj ih =>
    intro T hT
    rw [Finset.card_insert_of_notMem hj] at hT
    obtain ⟨p, hp⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := ih (T.erase p) (by rw [Finset.card_erase_of_mem hp]; omega)
    refine ⟨Function.update a p (j % p), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with h | hi'
    · subst h
      exact ⟨p, hp, by simp⟩
    · obtain ⟨p', hp', h'⟩ := ha i hi'
      refine ⟨p', Finset.mem_of_mem_erase hp', ?_⟩
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hp')]
      exact h'

/-- Greedy stage: each modulus removes at least its fair share of the survivors. -/
lemma OMA.greedy (S : Finset ℕ) (T : Finset ℕ) (hT : ∀ p ∈ T, 0 < p) :
    ∃ a : ℕ → ℕ, ((S.filter (fun j => ∀ p ∈ T, j % p ≠ a p)).card : ℝ) ≤
      Real.exp (-(∑ p ∈ T, (1:ℝ) / p)) * S.card := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert q T' hq ih =>
    obtain ⟨a, ha⟩ := ih (fun p hp => hT p (Finset.mem_insert_of_mem hp))
    have hqpos : 0 < q := hT q (Finset.mem_insert_self q T')
    have hq0 : (0:ℝ) < q := by exact_mod_cast hqpos
    obtain ⟨r, hr, hfib⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
      (s := S.filter (fun j => ∀ p ∈ T', j % p ≠ a p)) (t := Finset.range q)
      (f := fun j => j % q)
      (b := ((S.filter (fun j => ∀ p ∈ T', j % p ≠ a p)).card : ℝ) / q)
      (fun j _ => Finset.mem_range.mpr (Nat.mod_lt j hqpos))
      ⟨0, Finset.mem_range.mpr hqpos⟩
      (by rw [Finset.card_range, nsmul_eq_mul]; exact le_of_eq (by field_simp))
    refine ⟨Function.update a q r, ?_⟩
    obtain ⟨S1, hS1⟩ : ∃ S1, S1 = S.filter (fun j => ∀ p ∈ T', j % p ≠ a p) := ⟨_, rfl⟩
    obtain ⟨F, hF⟩ : ∃ F, F = S1.filter (fun j => j % q = r) := ⟨_, rfl⟩
    obtain ⟨S2, hS2⟩ : ∃ S2, S2 = S.filter
      (fun j => ∀ p ∈ insert q T', j % p ≠ Function.update a q r p) := ⟨_, rfl⟩
    rw [← hS1] at ha hfib
    have hfib' : (S1.card : ℝ) / q ≤ F.card := by rw [hF]; exact hfib
    rw [← hS2]
    have hsub : S2 ∪ F ⊆ S1 := by
      intro j hj
      rcases Finset.mem_union.mp hj with h | h
      · rw [hS2] at h
        obtain ⟨hjS, hjP⟩ := Finset.mem_filter.mp h
        rw [hS1]
        refine Finset.mem_filter.mpr ⟨hjS, fun p hp => ?_⟩
        have h3 := hjP p (Finset.mem_insert_of_mem hp)
        have hne : p ≠ q := by rintro rfl; exact hq hp
        rwa [Function.update_of_ne hne] at h3
      · rw [hF] at h
        exact (Finset.mem_filter.mp h).1
    have hdisj : Disjoint S2 F := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      rw [hS2] at h1
      rw [hF] at h2
      have h3 := (Finset.mem_filter.mp h1).2 q (Finset.mem_insert_self q T')
      rw [Function.update_self] at h3
      exact h3 (Finset.mem_filter.mp h2).2
    have hcard : S2.card + F.card ≤ S1.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card hsub
    have hcardR : (S2.card : ℝ) + F.card ≤ S1.card := by exact_mod_cast hcard
    have h1 : (S2.card : ℝ) ≤ (1 - 1 / q) * S1.card := by
      have e : (1 - 1 / (q:ℝ)) * S1.card = S1.card - S1.card / q := by ring
      rw [e]; linarith
    have h2 : (1 - 1 / (q:ℝ)) ≤ Real.exp (-(1 / (q:ℝ))) := Real.one_sub_le_exp_neg _
    rw [Finset.sum_insert hq, neg_add, Real.exp_add]
    calc (S2.card : ℝ) ≤ (1 - 1 / q) * S1.card := h1
      _ ≤ Real.exp (-(1 / (q:ℝ))) * S1.card :=
          mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
      _ ≤ Real.exp (-(1 / (q:ℝ))) * (Real.exp (-(∑ p ∈ T', (1:ℝ) / p)) * S.card) :=
          mul_le_mul_of_nonneg_left ha (Real.exp_pos _).le
      _ = _ := by ring

/-- Counting the survivors of the zero stage. -/
lemma OMA.count_S1 (D z m : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ j ∈ S, 1 ≤ j ∧ j ≤ D * m ∧ ∀ p, p.Prime → z ≤ p → p ≤ m → ¬ p ∣ j) :
    (S.card : ℝ) ≤ 2 ^ z * Real.sqrt ((D * m : ℕ) : ℝ) +
      D * (Nat.primeCounting (D * m) : ℝ) := by
  classical
  have hsub : S ⊆ Nat.smoothNumbersUpTo (D * m) z ∪
      Finset.image (fun pr : ℕ × ℕ => pr.1 * pr.2)
        (Finset.range D ×ˢ Nat.primesLE (D * m)) := by
    intro j hj
    obtain ⟨hj1, hjy, hjP⟩ := hS j hj
    by_cases hs : j ∈ Nat.smoothNumbers z
    · exact Finset.mem_union_left _ (Nat.mem_smoothNumbersUpTo.mpr ⟨hjy, hs⟩)
    · have hex : ∃ q, q.Prime ∧ q ∣ j ∧ z ≤ q := by
        by_contra hcon
        apply hs
        rw [Nat.mem_smoothNumbers']
        intro p hp hpj
        by_contra hlt
        exact hcon ⟨p, hp, hpj, by omega⟩
      obtain ⟨q, hq, hqj, hzq⟩ := hex
      have hqm : m < q := by
        by_contra hle
        exact hjP q hq hzq (by omega) hqj
      obtain ⟨t, rfl⟩ := hqj
      have ht0 : 0 < t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · subst h; simp at hj1
        · exact h
      have ht : t < D := by
        by_contra hle
        have h1 : (m + 1) * D ≤ q * t := Nat.mul_le_mul (Nat.succ_le_of_lt hqm) (not_lt.mp hle)
        have h2 : (m + 1) * D = D * m + D := by ring
        omega
      have hqy : q ≤ D * m := le_trans (Nat.le_mul_of_pos_right q ht0) hjy
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(t, q), ?_, Nat.mul_comm t q⟩)
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr ht, Nat.mem_primesLE.mpr ⟨hqy, hq⟩⟩
  have hA : (Nat.smoothNumbersUpTo (D * m) z).card ≤ 2 ^ z * (D * m).sqrt := by
    have hc : (Nat.primesBelow z).card ≤ z :=
      (Finset.card_filter_le _ _).trans_eq (Finset.card_range z)
    exact le_trans (Nat.smoothNumbersUpTo_card_le _ _)
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hc))
  have hB : (Finset.image (fun pr : ℕ × ℕ => pr.1 * pr.2)
        (Finset.range D ×ˢ Nat.primesLE (D * m))).card ≤ D * Nat.primeCounting (D * m) := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Finset.card_range, Nat.primesLE_card_eq_primeCounting]
  have h1 : S.card ≤ 2 ^ z * (D * m).sqrt + D * Nat.primeCounting (D * m) :=
    le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add hA hB))
  have h1R : (S.card : ℝ) ≤ 2 ^ z * ((D * m).sqrt : ℝ) +
      D * (Nat.primeCounting (D * m) : ℝ) := by exact_mod_cast h1
  have h3 := Real.nat_sqrt_le_real_sqrt (a := D * m)
  have h2z : (0:ℝ) ≤ 2 ^ z := by positivity
  linarith [mul_le_mul_of_nonneg_left h3 h2z]

/-- The reciprocals of the primes diverge, so the greedy factor can be made tiny. -/
lemma OMA.exists_z (B : ℝ) :
    ∃ z : ℕ, B ≤ Real.exp (∑ p ∈ Nat.primesBelow z, (1:ℝ) / p) := by
  have hns : ¬ Summable (Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1:ℝ) / n)) :=
    not_summable_one_div_on_primes
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => Set.indicator_nonneg (fun _ _ => by positivity) _)] at hns
  obtain ⟨z, hz⟩ := (hns.eventually (Filter.eventually_ge_atTop B)).exists
  refine ⟨z, ?_⟩
  have e : ∑ i ∈ Finset.range z, Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1:ℝ) / n) i
      = ∑ p ∈ Nat.primesBelow z, (1:ℝ) / p := by
    rw [Nat.primesBelow_eq_filter_range, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Set.indicator_apply]
  rw [e] at hz
  linarith [Real.add_one_le_exp (∑ p ∈ Nat.primesBelow z, (1:ℝ) / p)]

/-- The logarithm is negligible against the square root. -/
lemma OMA.log_sqrt_small (B : ℝ) (hB : 0 < B) :
    ∀ᶠ m : ℕ in Filter.atTop, B * (Real.log m * Real.sqrt m) ≤ m := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1 / 2)).bound
    (by positivity : 0 < 1 / B)
  have h' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  filter_upwards [h'] with m hm
  rw [← Real.sqrt_eq_rpow] at hm
  have h1 : Real.log m ≤ 1 / B * Real.sqrt m := by
    calc Real.log m ≤ ‖Real.log m‖ := Real.le_norm_self _
      _ ≤ 1 / B * ‖Real.sqrt m‖ := hm
      _ = 1 / B * Real.sqrt m := by rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hs : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (Nat.cast_nonneg m)
  have h2 : B * (Real.log m * Real.sqrt m) ≤ B * (1 / B * Real.sqrt m * Real.sqrt m) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)) hB.le
  have h3 : B * (1 / B * Real.sqrt m * Real.sqrt m) = m := by
    rw [mul_assoc (1 / B), hs]; field_simp
  linarith

/-- Chebyshev input: the survivors, after the greedy saving, fit into the primes of `(m, 16 m]`. -/
lemma OMA.analytic (D z : ℕ) (hD : 1 ≤ D) (ε : ℝ) (hε : 0 ≤ ε)
    (h8 : 8 * ε * (D:ℝ) ^ 2 ≤ 1) :
    ∀ᶠ m : ℕ in Filter.atTop,
      ε * (2 ^ z * Real.sqrt ((D * m : ℕ) : ℝ) + D * (Nat.primeCounting (D * m) : ℝ)) ≤
        (Nat.primeCounting (16 * m) : ℝ) - Nat.primeCounting m := by
  have hB : 0 < 2 * ε * ((2:ℝ) ^ z + D) * Real.sqrt D + 4 := by positivity
  filter_upwards [OMA.log_sqrt_small _ hB, Filter.eventually_ge_atTop 17] with m h5 hm17
  have hmR : (17:ℝ) ≤ m := by exact_mod_cast hm17
  have hmpos : (0:ℝ) < m := by linarith
  have hDR : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hℓpos : 0 < Real.log m := Real.log_pos (by linarith)
  have hsqrt1 : 1 ≤ Real.sqrt m := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hℓs : Real.log m ≤ Real.log m * Real.sqrt m := by nlinarith
  have hlam : (1:ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog4nn : 0 ≤ Real.log 4 := by rw [hlog4]; linarith
  -- upper Chebyshev bound at `m`
  have h1 : Real.log m * (Nat.primeCounting m : ℝ) ≤
      4 * Real.log 2 * m + Real.log m * Real.sqrt m := by
    have h := Chebyshev.pi_le_log4_mul_div (x := (m:ℝ)) (by linarith)
    rw [Nat.floor_natCast, Real.log_sqrt (Nat.cast_nonneg m)] at h
    have h' := (le_div_iff₀ (half_pos hℓpos)).mp
      (by linarith : (Nat.primeCounting m : ℝ) - Real.sqrt m ≤ Real.log 4 * m / (Real.log m / 2))
    rw [hlog4] at h'
    nlinarith [h']
  -- lower Chebyshev bound at `16 m`
  have h2 : 16 * (m:ℝ) * Real.log 2 - 2 * Real.log m ≤
      2 * (Real.log m * (Nat.primeCounting (16 * m) : ℝ)) := by
    have h := Chebyshev.pi_ge (16 * m)
    have hcast : ((16 * m : ℕ) : ℝ) = 16 * (m:ℝ) := by push_cast; ring
    rw [hcast] at h
    have hlog16pos : 0 < Real.log (16 * (m:ℝ)) := Real.log_pos (by linarith)
    have h' := (div_le_iff₀ hlog16pos).mp h
    have hl16 : Real.log (16 * (m:ℝ)) ≤ 2 * Real.log m := by
      have h6 : Real.log (16 * (m:ℝ)) ≤ Real.log ((m:ℝ) * m) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_mul hmpos.ne' hmpos.ne'] at h6
      linarith
    have hl17 : Real.log (16 * (m:ℝ) + 1) ≤ 2 * Real.log m := by
      have h6 : Real.log (16 * (m:ℝ) + 1) ≤ Real.log ((m:ℝ) * m) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_mul hmpos.ne' hmpos.ne'] at h6
      linarith
    have h7 := mul_le_mul_of_nonneg_left hl16
      (Nat.cast_nonneg (α := ℝ) (Nat.primeCounting (16 * m)))
    nlinarith [h', h7, hl17]
  -- upper Chebyshev bound at `D m`
  have hcastD : ((D * m : ℕ) : ℝ) = (D:ℝ) * m := Nat.cast_mul D m
  have hsqD : Real.sqrt ((D * m : ℕ) : ℝ) = Real.sqrt D * Real.sqrt m := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg D)]
  have h3 : Real.log m * (Nat.primeCounting (D * m) : ℝ) ≤
      4 * Real.log 2 * ((D:ℝ) * m) + Real.sqrt D * (Real.log m * Real.sqrt m) := by
    have hy_ge : (m:ℝ) ≤ ((D * m : ℕ) : ℝ) := by rw [hcastD]; nlinarith
    have h := Chebyshev.pi_le_log4_mul_div (x := ((D * m : ℕ) : ℝ)) (by linarith)
    rw [Nat.floor_natCast] at h
    have hl : Real.log m / 2 ≤ Real.log (Real.sqrt ((D * m : ℕ) : ℝ)) := by
      rw [Real.log_sqrt (Nat.cast_nonneg _)]
      have h6 := Real.log_le_log hmpos hy_ge
      linarith
    have hd : Real.log 4 * ((D * m : ℕ) : ℝ) / Real.log (Real.sqrt ((D * m : ℕ) : ℝ)) ≤
        Real.log 4 * ((D * m : ℕ) : ℝ) / (Real.log m / 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hlog4nn (Nat.cast_nonneg _)) (half_pos hℓpos) hl
    have h' := (le_div_iff₀ (half_pos hℓpos)).mp
      (by linarith : (Nat.primeCounting (D * m) : ℝ) - Real.sqrt ((D * m : ℕ) : ℝ) ≤
        Real.log 4 * ((D * m : ℕ) : ℝ) / (Real.log m / 2))
    rw [hlog4, hsqD, hcastD] at h'
    nlinarith [h']
  rw [hsqD]
  have hm0 : (0:ℝ) ≤ m := hmpos.le
  have hlam0 : 0 ≤ Real.log 2 := by linarith
  have e1 := mul_le_mul_of_nonneg_left h3 (mul_nonneg hε (Nat.cast_nonneg (α := ℝ) D))
  have e2 := mul_le_mul_of_nonneg_left h8 (mul_nonneg hlam0 hm0)
  have e3 := mul_nonneg hm0 (sub_nonneg.mpr hlam)
  have key : Real.log m * (ε * (2 ^ z * (Real.sqrt D * Real.sqrt m) +
      D * (Nat.primeCounting (D * m) : ℝ))) ≤
      Real.log m * ((Nat.primeCounting (16 * m) : ℝ) - Nat.primeCounting m) := by
    nlinarith [e1, e2, e3, h5, h1, h2, hℓs, hm0]
  exact le_of_mul_le_mul_left key hℓpos

/-- The covering system: every `j` in `[1, D m]` lies in a chosen residue class modulo some
prime `p ≤ 16 m`. -/
lemma OMA.cover (D z m : ℕ) (hD : 1 ≤ D) (hz : z ≤ m)
    (hcount : Real.exp (-(∑ p ∈ Nat.primesBelow z, (1:ℝ) / p)) *
      (2 ^ z * Real.sqrt ((D * m : ℕ) : ℝ) + D * (Nat.primeCounting (D * m) : ℝ)) ≤
        (Nat.primeCounting (16 * m) : ℝ) - Nat.primeCounting m) :
    ∃ a : ℕ → ℕ, ∀ j ∈ Finset.Icc 1 (D * m), ∃ p, p.Prime ∧ p ≤ 16 * m ∧ j % p = a p := by
  classical
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = (Finset.Icc 1 (D * m)).filter
    (fun j => ∀ p, p.Prime → z ≤ p → p ≤ m → ¬ p ∣ j) := ⟨_, rfl⟩
  obtain ⟨aG, hG⟩ := OMA.greedy S1 (Nat.primesBelow z)
    (fun p hp => (Nat.prime_of_mem_primesBelow hp).pos)
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = S1.filter
    (fun j => ∀ p ∈ Nat.primesBelow z, j % p ≠ aG p) := ⟨_, rfl⟩
  rw [← hS2] at hG
  have hS1card := OMA.count_S1 D z m hD S1 (by
    intro j hj
    rw [hS1] at hj
    obtain ⟨hjI, hjP⟩ := Finset.mem_filter.mp hj
    exact ⟨(Finset.mem_Icc.mp hjI).1, (Finset.mem_Icc.mp hjI).2, hjP⟩)
  have hT : (Nat.primeCounting (16 * m) : ℝ) - Nat.primeCounting m ≤
      ((Nat.primesLE (16 * m) \ Nat.primesLE m).card : ℝ) := by
    have h := Finset.le_card_sdiff (Nat.primesLE m) (Nat.primesLE (16 * m))
    rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at h
    have h' : Nat.primeCounting (16 * m) ≤
        (Nat.primesLE (16 * m) \ Nat.primesLE m).card + Nat.primeCounting m := by omega
    have h'' : (Nat.primeCounting (16 * m) : ℝ) ≤
        ((Nat.primesLE (16 * m) \ Nat.primesLE m).card : ℝ) + Nat.primeCounting m := by
      exact_mod_cast h'
    linarith
  have hS2T : S2.card ≤ (Nat.primesLE (16 * m) \ Nat.primesLE m).card := by
    have hR : (S2.card : ℝ) ≤ ((Nat.primesLE (16 * m) \ Nat.primesLE m).card : ℝ) :=
      calc (S2.card : ℝ) ≤ Real.exp (-(∑ p ∈ Nat.primesBelow z, (1:ℝ) / p)) * S1.card := hG
        _ ≤ Real.exp (-(∑ p ∈ Nat.primesBelow z, (1:ℝ) / p)) *
            (2 ^ z * Real.sqrt ((D * m : ℕ) : ℝ) + D * (Nat.primeCounting (D * m) : ℝ)) :=
            mul_le_mul_of_nonneg_left hS1card (Real.exp_pos _).le
        _ ≤ _ := hcount
        _ ≤ _ := hT
    exact_mod_cast hR
  obtain ⟨aO, hO⟩ := OMA.one_by_one S2 _ hS2T
  refine ⟨fun p => if p < z then aG p else if p ≤ m then 0 else aO p, ?_⟩
  intro j hj
  by_cases h1 : ∃ p, p.Prime ∧ z ≤ p ∧ p ≤ m ∧ p ∣ j
  · obtain ⟨p, hp, hzp, hpm, hpj⟩ := h1
    refine ⟨p, hp, by omega, ?_⟩
    show j % p = (if p < z then aG p else if p ≤ m then 0 else aO p)
    rw [if_neg (not_lt.mpr hzp), if_pos hpm]
    obtain ⟨t, rfl⟩ := hpj
    simp
  · have hjS1 : j ∈ S1 := by
      rw [hS1]
      exact Finset.mem_filter.mpr ⟨hj, fun p hp hzp hpm hpj => h1 ⟨p, hp, hzp, hpm, hpj⟩⟩
    by_cases h2 : ∃ p ∈ Nat.primesBelow z, j % p = aG p
    · obtain ⟨p, hp, hpe⟩ := h2
      have hp' := Nat.mem_primesBelow.mp hp
      refine ⟨p, hp'.2, by omega, ?_⟩
      show j % p = (if p < z then aG p else if p ≤ m then 0 else aO p)
      rw [if_pos hp'.1]
      exact hpe
    · have hjS2 : j ∈ S2 := by
        rw [hS2]
        exact Finset.mem_filter.mpr ⟨hjS1, fun p hp hpe => h2 ⟨p, hp, hpe⟩⟩
      obtain ⟨p, hpT, hpe⟩ := hO j hjS2
      have hpT' := Finset.mem_sdiff.mp hpT
      have h16 := Nat.mem_primesLE.mp hpT'.1
      have hgt : m < p := by
        by_contra hle
        exact hpT'.2 (Nat.mem_primesLE.mpr ⟨by omega, h16.2⟩)
      refine ⟨p, h16.2, h16.1, ?_⟩
      show j % p = (if p < z then aG p else if p ≤ m then 0 else aO p)
      rw [if_neg (by omega : ¬ p < z), if_neg (by omega : ¬ p ≤ m)]
      exact hpe

/-- Chinese remainder theorem, placing the solution just above the primorial. -/
lemma OMA.crt (n : ℕ) (b : ℕ → ℕ) : ∃ A : ℕ, primorial n ≤ A ∧ A < 2 * primorial n ∧
    ∀ p, p.Prime → p ≤ n → A ≡ b p [MOD p] := by
  classical
  have hs : ∀ p ∈ Nat.primesLE n, (id p : ℕ) ≠ 0 :=
    fun p hp => (Nat.prime_of_mem_primesLE hp).ne_zero
  have pp : Set.Pairwise (Nat.primesLE n : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hne
    exact (Nat.coprime_primes (Nat.prime_of_mem_primesLE (Finset.mem_coe.mp hp))
      (Nat.prime_of_mem_primesLE (Finset.mem_coe.mp hq))).mpr hne
  obtain ⟨A0, hA0⟩ := Nat.chineseRemainderOfFinset b id (Nat.primesLE n) hs pp
  refine ⟨A0 % primorial n + primorial n, Nat.le_add_left _ _, ?_, ?_⟩
  · have := Nat.mod_lt A0 (primorial_pos n)
    omega
  · intro p hp hpn
    have hmem : p ∈ Nat.primesLE n := Nat.mem_primesLE.mpr ⟨hpn, hp⟩
    have hdvd : p ∣ primorial n := (Nat.Prime.dvd_primorial_iff hp).mpr hpn
    have h1 : A0 % primorial n ≡ A0 [MOD p] := (Nat.mod_modEq A0 (primorial n)).of_dvd hdvd
    have h2 : A0 % primorial n + primorial n ≡ A0 % primorial n [MOD p] := by
      have h3 : primorial n ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hdvd
      simpa using Nat.ModEq.add_left (A0 % primorial n) h3
    exact h2.trans (h1.trans (hA0 p hmem))

theorem OMA.solution : type_of% @CramerConjecture.cramer_conjecture.variants.westzynthius := by
  intro M
  rw [Filter.frequently_atTop]
  intro N0
  classical
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  obtain ⟨K, hK⟩ : ∃ K : ℕ, |M| ≤ K := ⟨⌈|M|⌉₊, Nat.le_ceil _⟩
  have hD1 : 1 ≤ 16 * (6 * K + 1) := by omega
  obtain ⟨z, hz⟩ := OMA.exists_z (8 * ((16 * (6 * K + 1) : ℕ) : ℝ) ^ 2)
  have hε0 : 0 ≤ Real.exp (-(∑ p ∈ Nat.primesBelow z, (1:ℝ) / p)) := (Real.exp_pos _).le
  have h8 : 8 * Real.exp (-(∑ p ∈ Nat.primesBelow z, (1:ℝ) / p)) *
      ((16 * (6 * K + 1) : ℕ) : ℝ) ^ 2 ≤ 1 := by
    have h1 : Real.exp (-(∑ p ∈ Nat.primesBelow z, (1:ℝ) / p)) *
        Real.exp (∑ p ∈ Nat.primesBelow z, (1:ℝ) / p) = 1 := by
      rw [← Real.exp_add]; simp
    have h2 := mul_le_mul_of_nonneg_left hz hε0
    linarith
  obtain ⟨m, hcount, hmge⟩ := ((OMA.analytic (16 * (6 * K + 1)) z hD1 _ hε0 h8).and
    (Filter.eventually_ge_atTop (z + Nat.nth Nat.Prime (N0 + 1) + 17))).exists
  obtain ⟨a, ha⟩ := OMA.cover (16 * (6 * K + 1)) z m hD1 (by omega) hcount
  obtain ⟨A, hA1, hA2, hA3⟩ := OMA.crt (16 * m) (fun p => p - a p)
  have hAm : 16 * m ≤ A := le_trans le_primorial_self hA1
  -- no primes in `(A, A + D m]`
  have hnp : ∀ j, 1 ≤ j → j ≤ 16 * (6 * K + 1) * m → ¬ (A + j).Prime := by
    intro j hj1 hj2 hprime
    obtain ⟨p, hp, hpn, hpa⟩ := ha j (Finset.mem_Icc.mpr ⟨hj1, hj2⟩)
    have hle : a p ≤ p := by rw [← hpa]; exact (Nat.mod_lt j hp.pos).le
    have hj' : j ≡ a p [MOD p] := by rw [← hpa]; exact (Nat.mod_modEq j p).symm
    have hmod : A + j ≡ (p - a p) + a p [MOD p] := Nat.ModEq.add (hA3 p hp hpn) hj'
    rw [Nat.sub_add_cancel hle] at hmod
    have hdvd : p ∣ A + j :=
      (Nat.modEq_zero_iff_dvd).mp (hmod.trans ((Nat.modEq_zero_iff_dvd).mpr (dvd_refl p)))
    have h := (Nat.prime_dvd_prime_iff_eq hp hprime).mp hdvd
    omega
  -- locate the prime gap
  have hcN : N0 + 1 ≤ Nat.count Nat.Prime (A + 1) := by
    have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime (N0 + 1)) = N0 + 1 :=
      Nat.primeCounting'_nth_eq (N0 + 1)
    have h2 : Nat.count Nat.Prime (Nat.nth Nat.Prime (N0 + 1)) ≤ Nat.count Nat.Prime (A + 1) :=
      Nat.count_monotone _ (by omega)
    omega
  obtain ⟨c, hc⟩ : ∃ c, c = Nat.count Nat.Prime (A + 1) := ⟨_, rfl⟩
  rw [← hc] at hcN
  have hlow : Nat.nth Nat.Prime (c - 1) < A + 1 := Nat.nth_lt_of_lt_count (by omega)
  have hhigh : A + 1 ≤ Nat.nth Nat.Prime c := by rw [hc]; exact Nat.le_nth_count hinf (A + 1)
  have hprime : (Nat.nth Nat.Prime c).Prime := Nat.nth_mem_of_infinite hinf c
  have hPprime : (Nat.nth Nat.Prime (c - 1)).Prime := Nat.nth_mem_of_infinite hinf (c - 1)
  have hfar : A + 16 * (6 * K + 1) * m < Nat.nth Nat.Prime c := by
    by_contra h
    have h' : Nat.nth Nat.Prime c ≤ A + 16 * (6 * K + 1) * m := not_lt.mp h
    obtain ⟨j, hj⟩ : ∃ j, Nat.nth Nat.Prime c = A + j :=
      ⟨_, (Nat.add_sub_cancel' (by omega)).symm⟩
    exact hnp j (by omega) (by omega) (hj ▸ hprime)
  have hgap : 16 * (6 * K + 1) * m ≤ primeGap (c - 1) := by
    unfold primeGap
    rw [show c - 1 + 1 = c by omega]
    omega
  refine ⟨c - 1, by omega, ?_⟩
  have hgapR : ((16 * (6 * K + 1) * m : ℕ) : ℝ) ≤ (primeGap (c - 1) : ℝ) := by
    exact_mod_cast hgap
  have hPpos : (0:ℝ) < (Nat.nth Nat.Prime (c - 1) : ℝ) := by exact_mod_cast hPprime.pos
  have hlogP0 : 0 ≤ Real.log (Nat.nth Nat.Prime (c - 1) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hPprime.one_lt.le)
  have h4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
    linarith
  have hP4 : (Nat.nth Nat.Prime (c - 1) : ℝ) ≤ (4:ℝ) ^ (16 * m + 1) := by
    have h1 : Nat.nth Nat.Prime (c - 1) ≤ 4 ^ (16 * m + 1) := by
      have h2 := primorial_le_four_pow (16 * m)
      rw [pow_succ]
      omega
    exact_mod_cast h1
  have hlogP : Real.log (Nat.nth Nat.Prime (c - 1) : ℝ) ≤ 3 * (16 * (m:ℝ) + 1) := by
    have h1 : Real.log (Nat.nth Nat.Prime (c - 1) : ℝ) ≤ Real.log ((4:ℝ) ^ (16 * m + 1)) :=
      Real.log_le_log hPpos hP4
    rw [Real.log_pow] at h1
    have h2 : (((16 * m + 1 : ℕ) : ℝ)) = 16 * (m:ℝ) + 1 := by push_cast; ring
    rw [h2] at h1
    have hm0 : (0:ℝ) ≤ 16 * (m:ℝ) + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h4 hm0]
  have hm1 : (1:ℝ) ≤ m := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg K
  have hcastD : ((16 * (6 * K + 1) * m : ℕ) : ℝ) = 16 * (6 * (K:ℝ) + 1) * m := by
    push_cast; ring
  rw [hcastD] at hgapR
  calc M * Real.log (Nat.nth Nat.Prime (c - 1) : ℝ)
      ≤ |M| * Real.log (Nat.nth Nat.Prime (c - 1) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self M) hlogP0
    _ ≤ K * (3 * (16 * (m:ℝ) + 1)) :=
        mul_le_mul hK hlogP hlogP0 hK0
    _ ≤ 16 * (6 * (K:ℝ) + 1) * m := by nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hm1)]
    _ ≤ _ := hgapR
