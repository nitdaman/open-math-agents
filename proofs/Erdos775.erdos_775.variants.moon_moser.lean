import FormalConjectures.ErdosProblems.«775»

-- Problem: Erdős Problem 775 — moon moser
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/775.lean:78 (declaration Erdos775.erdos_775.variants.moon_moser)
-- Credit: @vkascheev (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

theorem mm_comb (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ k ≤ n, (SimpleGraph.cliqueSizes G).ncard ≤ k + 1 ∧
      (SimpleGraph.cliqueSizes G).ncard ≤ 2 ^ (n - k) := by
  classical
  set P : Finset (Fin n) → Prop := fun T => G.IsClique (T : Set (Fin n)) with hP
  have hne : (univ.powerset.filter P).Nonempty := ⟨∅, by simp [hP]⟩
  obtain ⟨K, hKmem, hKmax⟩ := exists_max_image (univ.powerset.filter P) Finset.card hne
  have hK : P K := (mem_filter.1 hKmem).2
  have hle : ∀ T, P T → T.card ≤ K.card := fun T hT =>
    hKmax T (mem_filter.2 ⟨mem_powerset.2 (subset_univ _), hT⟩)
  refine ⟨K.card, by simpa using card_le_univ K, ?_, ?_⟩
  · have hsub : SimpleGraph.cliqueSizes G ⊆ (range (K.card + 1) : Set ℕ) := by
      rintro x ⟨S, hS, rfl⟩
      simp only [coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (hle S hS.1)
    calc (SimpleGraph.cliqueSizes G).ncard ≤ ((range (K.card + 1) : Finset ℕ) : Set ℕ).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = K.card + 1 := by rw [Set.ncard_coe_finset, card_range]
  · set M := univ.powerset.filter (fun S => Maximal P S) with hM
    have hsub : SimpleGraph.cliqueSizes G ⊆ ((M.image Finset.card : Finset ℕ) : Set ℕ) := by
      rintro x ⟨S, hS, rfl⟩
      simp only [coe_image, Set.mem_image, mem_coe]
      exact ⟨S, mem_filter.2 ⟨mem_powerset.2 (subset_univ _), hS⟩, rfl⟩
    have hinj : Set.InjOn (fun S => S \ K) (M : Set (Finset (Fin n))) := by
      have key : ∀ S S', Maximal P S → Maximal P S' → S \ K = S' \ K → S ⊆ S' := by
        intro S S' hS hS' heq x hx
        by_cases hxK : x ∈ K
        · have hcl : P (insert x S') := by
            simp only [hP, coe_insert]
            refine hS'.1.insert ?_
            intro y hy hxy
            by_cases hyK : y ∈ K
            · exact hK (by simpa using hxK) (by simpa using hyK) hxy
            · have : y ∈ S' \ K := mem_sdiff.2 ⟨hy, hyK⟩
              rw [← heq] at this
              exact hS.1 (by simpa using hx) (by simpa using (mem_sdiff.1 this).1) hxy
          have := hS'.2 hcl (subset_insert x S')
          exact this (mem_insert_self x S')
        · have : x ∈ S \ K := mem_sdiff.2 ⟨hx, hxK⟩
          rw [heq] at this
          exact (mem_sdiff.1 this).1
      intro S hS S' hS' heq
      have hS1 : Maximal P S := (mem_filter.1 hS).2
      have hS2 : Maximal P S' := (mem_filter.1 hS').2
      exact le_antisymm (key S S' hS1 hS2 heq) (key S' S hS2 hS1 heq.symm)
    have hmaps : ∀ S ∈ M, S \ K ∈ (univ \ K).powerset := by
      intro S _
      exact mem_powerset.2 (sdiff_subset_sdiff (subset_univ _) le_rfl)
    calc (SimpleGraph.cliqueSizes G).ncard ≤ ((M.image Finset.card : Finset ℕ) : Set ℕ).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (M.image Finset.card).card := Set.ncard_coe_finset _
      _ ≤ M.card := card_image_le
      _ ≤ (univ \ K).powerset.card := card_le_card_of_injOn _ hmaps hinj
      _ = 2 ^ (n - K.card) := by
          rw [card_powerset, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]

theorem mm_nat (t : ℕ) : t ≤ 2 ^ (t - 1) + 1 := by
  rcases t with _ | t
  · simp
  · simp only [Nat.add_sub_cancel]
    have := Nat.lt_two_pow_self (n := t)
    omega

theorem OMA.solution : type_of% @Erdos775.erdos_775.variants.moon_moser := by
  refine ⟨2, fun n G => ?_⟩
  obtain ⟨k, hkn, h1, h2⟩ := mm_comb n G
  set c := (SimpleGraph.cliqueSizes G).ncard
  set t := Nat.log 2 n with ht
  have hL : Real.logb 2 (n : ℝ) < (t : ℝ) + 1 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp; positivity
    · rw [Real.logb_lt_iff_lt_rpow (b := 2) (by norm_num) (by exact_mod_cast hn)]
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
      rw [← ht] at this
      have h' : ((n : ℕ) : ℝ) < ((2 ^ (t + 1) : ℕ) : ℝ) := by exact_mod_cast this
      rw [show ((t : ℝ) + 1) = ((t + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      exact_mod_cast h'
  by_cases hm : t ≤ n - k
  · have : (c : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast h1
    have hk : (k : ℝ) + (t : ℝ) ≤ n := by
      have : k + t ≤ n := by omega
      exact_mod_cast this
    linarith
  · push Not at hm
    have hpow : 2 ^ (n - k) ≤ 2 ^ (t - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have htn : 2 ^ t ≤ n := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp [ht] at hm
      · exact Nat.pow_log_le_self 2 (by omega)
    have h2t : 2 ^ t = 2 * 2 ^ (t - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hnat : c + t ≤ n + 1 := by
      have := mm_nat t
      omega
    have : (c : ℝ) + (t : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hnat
    linarith
