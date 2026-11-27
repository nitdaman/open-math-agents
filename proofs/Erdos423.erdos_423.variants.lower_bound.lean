import FormalConjectures.ErdosProblems.«423»

/-!
The power-of-two obstruction from the Hofstadter infinite-complement proof
(PR #622) also works on a finite interval. On geometric scales for the
logarithm of the index, each interval forces another increase in excess.
The block-sum argument is based on Tang, arXiv:2603.09939.
-/

open Erdos423 Finset Filter Asymptotics

private lemma twice_sum_Ico_add (i j c : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
    2 * (∑ l ∈ Ico i j, (l + c)) + (i + c - 1) * (i + c) =
      (j + c - 1) * (j + c) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
      rw [Finset.sum_Ico_succ_top hij]
      have hu : j + 1 + c - 1 = j + c := by omega
      have hv : j + c - 1 + 1 = j + c := by omega
      rw [hu]
      nlinarith [congrArg (fun x : ℕ => x * (j + c)) hv]

private lemma even_of_one_lt_of_dvd_two_pow {d m : ℕ} (hd : 1 < d) (hm : d ∣ 2 ^ m) :
    Even d := by
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hm
  cases k with
  | zero => simp at hd
  | succ k =>
      refine ⟨2 ^ k, ?_⟩
      rw [pow_succ]
      omega

private lemma no_large_even_square_gap {x y A B : ℕ}
    (hxy : x ≠ y) (hA : A < x) (hB : B < x) (h : x ^ 2 + A = y ^ 2 + B) :
    False := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hs : (x + 1) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  · have hs : y ^ 2 ≤ (x - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have heq : x - 1 + 1 = x := by omega
    nlinarith [congrArg (fun z : ℕ => z * (x - 1)) heq]

/-- A constant excess cannot persist from a power of two to its eighth power. -/
private lemma no_constant_excess {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    (d c : ℕ) (hN : 256 ≤ (2 : ℕ) ^ d) (hc : c ≤ 2 ^ d)
    (hlin : ∀ n, 2 ^ d ≤ n → n ≤ (2 ^ d) ^ 8 → a n = n + c) : False := by
  let N : ℕ := 2 ^ d
  change 256 ≤ N at hN
  change c ≤ N at hc
  change ∀ n, N ≤ n → n ≤ N ^ 8 → a n = n + c at hlin
  have hN2 : N ≤ N ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left N (show 1 ≤ N by omega)
  have hN8 : N ≤ N ^ 8 := hN2.trans (Nat.pow_le_pow_right (by omega) (by decide))

  let S := ∑ l ∈ Ico 1 N, a l
  let z := N + c - 1
  let m := 6 + 2 * d
  let t := 2 ^ m
  let P := 2 ^ (2 * m + 1)
  have ht : t = 64 * N ^ 2 := by
    dsimp [t, m, N]
    rw [pow_add, ← pow_mul, Nat.mul_comm 2 d]
    norm_num
  have hP : P = 2 * t ^ 2 := by
    dsimp [P, t]
    rw [pow_succ, two_mul, pow_add, pow_two, mul_comm]
  have hPt : 4 * t ≤ P := by
    rw [ht] at hP ⊢
    nlinarith [sq_nonneg (N ^ 2 - 1)]
  have hNP : N + c ≤ P := by
    have hs : 8 * (N + c) < 4 * t := by rw [ht]; omega
    omega
  have hS : S ≤ 2 * N ^ 2 := by
    have haN := hlin N le_rfl hN8
    calc
      S ≤ ∑ l ∈ Ico 1 N, (N + c) := by
        apply Finset.sum_le_sum
        intro l hl
        have h := (mem_Ico.mp hl)
        rw [← haN]
        exact ((ha.lt_iff_lt h.1 (by omega)).2 h.2).le
      _ ≤ N * (N + c) := by
        rw [Finset.sum_const, smul_eq_mul, Nat.card_Ico]
        exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ ≤ 2 * N ^ 2 := by
        calc
          N * (N + c) ≤ N * (2 * N) := Nat.mul_le_mul_left _ (by omega)
          _ = 2 * N ^ 2 := by ring
  have hoffset : (2 * z + 1) ^ 2 < 4 * t := by
    have hz : 2 * z + 1 ≤ 4 * N := by dsimp [z]; omega
    have hb := Nat.pow_le_pow_left hz 2
    rw [ht]
    nlinarith
  have hblocks : 8 * S < 4 * t := by rw [ht]; omega
  have hSP : S < P := by omega
  have hbound : P ≤ N ^ 8 := by
    have hs : 8192 ≤ N ^ 4 := (by decide : 8192 ≤ (256 : ℕ) ^ 4).trans
      (Nat.pow_le_pow_left hN 4)
    calc
      P = 8192 * N ^ 4 := by rw [hP, ht]; ring
      _ ≤ N ^ 4 * N ^ 4 := Nat.mul_le_mul_right _ hs
      _ = N ^ 8 := by rw [← pow_add]

  -- The sequence would contain this power of two within the constant-excess interval.
  have hrepresent := (ha.2.2 (P - c) (by omega)).1
  rw [hlin _ (by omega) (by omega), Nat.sub_add_cancel (by omega : c ≤ P)] at hrepresent
  obtain ⟨i, j, hi, hij, hjbound, heq⟩ := hrepresent
  rw [← Finset.Ico_succ_right_eq_Icc] at heq
  change P = ∑ l ∈ Ico i (j + 1), a l at heq

  have hj : N ≤ j := by
    by_contra! h
    have hsub : Ico i (j + 1) ⊆ Ico 1 N := by
      intro l hl
      simp only [mem_Ico] at hl ⊢
      omega
    have hle : (∑ l ∈ Ico i (j + 1), a l) ≤ S := Finset.sum_le_sum_of_subset hsub
    omega

  have hsum (k : ℕ) (hk : N ≤ k) (hkj : k ≤ j + 1) :
      2 * (∑ l ∈ Ico k (j + 1), a l) + (k + c - 1) * (k + c) =
        (j + c) * (j + c + 1) := by
    have hrewrite : (∑ l ∈ Ico k (j + 1), a l) = ∑ l ∈ Ico k (j + 1), (l + c) := by
      refine sum_congr rfl fun l hl => hlin l ?_ ?_
      · exact hk.trans (mem_Ico.mp hl).1
      · have hh := (mem_Ico.mp hl).2; omega
    rw [hrewrite]
    have h1 : j + 1 + c - 1 = j + c := by omega
    have h2 : j + 1 + c = j + c + 1 := by omega
    simpa only [h2, Nat.add_sub_cancel] using twice_sum_Ico_add k (j + 1) c (by omega) hkj

  by_cases hNi : N ≤ i
  · have hformula := hsum i hNi (by omega)
    rw [← heq] at hformula
    have hlen : j + 1 - i + i = j + 1 := by omega
    have hstart : i + c - 1 + 1 = i + c := by omega
    have hfactor : (j + 1 - i) * (i + j + 2 * c) = 2 * P := by
      nlinarith [congrArg (fun x : ℕ => x * (i + j + 2 * c)) hlen,
        congrArg (fun x : ℕ => x * (i + c)) hstart]
    have hpow : 2 * P = 2 ^ (2 * m + 1 + 1) := by simp [P, pow_succ, mul_comm]
    rw [hpow] at hfactor
    obtain ⟨p, hp⟩ := even_of_one_lt_of_dvd_two_pow
      (d := j + 1 - i) (by omega) ⟨_, hfactor.symm⟩
    obtain ⟨q, hq⟩ := even_of_one_lt_of_dvd_two_pow
      (d := i + j + 2 * c) (by omega) ⟨_, hfactor.symm.trans (mul_comm _ _)⟩
    omega
  · let A := ∑ l ∈ Ico i N, a l
    have hsub : Ico i N ⊆ Ico 1 N := by
      intro l hl
      simp only [mem_Ico] at hl ⊢
      omega
    have hA : A ≤ S := Finset.sum_le_sum_of_subset hsub
    have hsplit : A + ∑ l ∈ Ico N (j + 1), a l = P := by
      dsimp [A]
      rw [Finset.sum_Ico_consecutive _ (by omega : i ≤ N) (by omega : N ≤ j + 1)]
      exact heq.symm
    have hz : N + c = z + 1 := by dsimp [z]; omega
    have hformula := hsum N (le_refl _) (by omega)
    change 2 * (∑ l ∈ Ico N (j + 1), a l) + z * (N + c) =
      (j + c) * (j + c + 1) at hformula
    rw [hz] at hformula
    have hsquare : (4 * t) ^ 2 + (2 * z + 1) ^ 2 =
        (2 * (j + c) + 1) ^ 2 + 8 * A := by nlinarith
    apply no_large_even_square_gap (x := 4 * t) (y := 2 * (j + c) + 1)
      (A := (2 * z + 1) ^ 2) (B := 8 * A)
    · omega
    · exact hoffset
    · omega
    · exact hsquare


private def scale (k : ℕ) : ℕ := 2 ^ (8 ^ (k + 1))

private lemma scale_step (k : ℕ) : scale (k + 1) = scale k ^ 8 := by
  unfold scale
  rw [pow_succ (8 : ℕ) (k + 1), pow_mul]

private lemma scale_grows (k : ℕ) : scale k + 1 ≤ scale (k + 1) := by
  have hp : 2 ≤ scale k := by
    change 2 ≤ (2 : ℕ) ^ (8 ^ (k + 1))
    exact Nat.le_self_pow (by positivity) _
  rw [scale_step]
  have hsq : scale k + 1 ≤ scale k ^ 2 := by
    have hm := Nat.mul_le_mul_left (scale k) hp
    rw [pow_two]
    omega
  exact hsq.trans (Nat.pow_le_pow_right (by omega) (by decide))

private lemma scale_mono : Monotone scale :=
  monotone_nat_of_le_succ fun k => (Nat.le_succ _).trans (scale_grows k)

private lemma scale_lower (k : ℕ) : 256 ≤ scale k ∧ k + 1 ≤ scale k := by
  refine ⟨(show 256 ≤ scale 0 by decide).trans (scale_mono (Nat.zero_le _)), ?_⟩
  induction k with
  | zero => decide
  | succ k ih => have := scale_grows k; omega

private lemma excess_at_scale {a : ℕ → ℕ} (ha : IsHofstadterSeq a) (k : ℕ) :
    k ≤ a (scale k) - scale k := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hN := (scale_lower k).1
    have hk : k ≤ scale k := (Nat.le_succ k).trans (scale_lower k).2
    by_contra! h
    have hlin (n : ℕ) (hn : scale k ≤ n) (hn' : n ≤ scale k ^ 8) : a n = n + k := by
      rw [← scale_step] at hn'
      have hlo := erdos_423.variants.nondecreasing a ha (scale k) n (by omega) hn
      have hhi := erdos_423.variants.nondecreasing a ha n (scale (k + 1)) (by omega) hn'
      have hle := ha.le_apply n (by omega)
      omega
    exact no_constant_excess ha (8 ^ (k + 1)) k hN hk hlin

private lemma log_log_scale (k : ℕ) :
    Real.log (Real.log (scale k : ℝ)) =
      (k + 1 : ℝ) * Real.log 8 + Real.log (Real.log 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (0 : ℝ) < 8 ^ (k + 1) := by positivity
  simp only [scale, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_pow, Nat.cast_pow, Nat.cast_ofNat, Real.log_mul hp.ne' hlog.ne', Real.log_pow]
  simp

theorem OMA.solution : type_of% @Erdos423.erdos_423.variants.lower_bound := by
  intro a ha
  let C : ℝ := 3 * Real.log 8 + |Real.log (Real.log 2)|
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (scale 1)] with n hn
  have hex : ∃ t, n < scale t := ⟨n, by have := (scale_lower n).2; omega⟩
  let m := Nat.find hex
  have hm : n < scale m := Nat.find_spec hex
  have hm1 : 1 < m := by
    by_contra! h
    have := scale_mono h
    omega
  let k := m - 1
  have hk : 1 ≤ k := by omega
  have hmk : k + 1 = m := by omega
  have hkn : scale k ≤ n := le_of_not_gt (Nat.find_min hex (by omega : k < m))
  have hnu : n < scale (k + 1) := by rwa [hmk]
  have hN := (scale_lower 1).1
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hn1 : 1 ≤ n := by omega
  have hlogn : 1 ≤ Real.log n := by
    have h := Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.le.trans hn3)
    simpa using h
  have hloglog : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlogn
  have hu : Real.log (Real.log n) < Real.log (Real.log (scale (k + 1) : ℝ)) :=
    Real.log_lt_log (by linarith) (Real.log_lt_log (by linarith) (by exact_mod_cast hnu))
  rw [log_log_scale, Nat.cast_add, Nat.cast_one] at hu
  have hstep := erdos_423.variants.nondecreasing a ha (scale k) n
    (by have := (scale_lower k).1; omega) hkn
  have hreal : (k : ℝ) ≤ (a n : ℝ) - n := by
    have hnat : k + n ≤ a n := by
      have := excess_at_scale ha k
      have := ha.le_apply n hn1
      omega
    exact le_sub_iff_add_le.mpr (by exact_mod_cast hnat)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (a n : ℝ) - n ≥ 0 := (by positivity : (0 : ℝ) ≤ k).trans hreal
  rw [Real.norm_of_nonneg hloglog, Real.norm_of_nonneg hr]
  calc
    _ ≤ C * (k : ℝ) := by
      dsimp [C]
      nlinarith [le_abs_self (Real.log (Real.log 2)),
        mul_nonneg (show 0 ≤ (k : ℝ) - 1 by linarith) hlog8,
        mul_nonneg (show 0 ≤ (k : ℝ) - 1 by linarith) (abs_nonneg (Real.log (Real.log 2)))]
    _ ≤ _ := mul_le_mul_of_nonneg_left hreal hC