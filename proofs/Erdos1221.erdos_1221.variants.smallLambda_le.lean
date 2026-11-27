import FormalConjectures.ErdosProblems.«1221»

-- Problem: Erdős Problem 1221 — smallLambda le
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1221.lean:204 (declaration Erdos1221.erdos_1221.variants.smallLambda_le)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Proof of the de Bruijn--Erdos upper bound for `smallLambda` (arc-birth argument). -/

open Filter Erdos1221

namespace E1221W3

theorem unrolled_eq (a : ℕ → ℝ) {n k : ℕ} (m : ℕ) (hk : k < n) :
    unrolled a n (k + m * n) = sortedPoint a n ⟨k, hk⟩ + m := by
  have hn : 0 < n := by omega
  unfold unrolled
  rw [dif_pos hn]
  have h1 : (k + m * n) % n = k := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have h2 : (k + m * n) / n = m := by
    rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hk, zero_add]
  have h3 : sortedPoint a n ⟨(k + m * n) % n, Nat.mod_lt _ hn⟩ = sortedPoint a n ⟨k, hk⟩ := by
    congr 1; exact Fin.ext h1
  rw [h3, h2]

theorem unrolled_eq' (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    unrolled a n j = sortedPoint a n ⟨j % n, Nat.mod_lt _ hn⟩ + ((j / n : ℕ) : ℝ) := by
  unfold unrolled
  rw [dif_pos hn]

theorem unrolled_add (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    unrolled a n (j + n) = unrolled a n j + 1 := by
  rw [unrolled_eq' a hn, unrolled_eq' a hn]
  have h1 : (j + n) % n = j % n := Nat.add_mod_right j n
  have h2 : (j + n) / n = j / n + 1 := Nat.add_div_right j hn
  have h3 : sortedPoint a n ⟨(j + n) % n, Nat.mod_lt _ hn⟩ =
      sortedPoint a n ⟨j % n, Nat.mod_lt _ hn⟩ := by
    congr 1; exact Fin.ext h1
  rw [h3, h2]; push_cast; ring

theorem sum_shift_telescope {G : Type*} [AddCommGroup G] (f : ℕ → G) (c : G) (n : ℕ)
    (hf : ∀ j, f (j + n) = f j + c) (r : ℕ) :
    ∑ i ∈ Finset.range n, (f (i + r) - f i) = r • c := by
  induction r with
  | zero => simp
  | succ k ih =>
    have e : ∑ i ∈ Finset.range n, (f (i + (k + 1)) - f i) =
        ∑ i ∈ Finset.range n, (f (i + k) - f i) +
          ∑ i ∈ Finset.range n, ((fun i => f (i + k)) (i + 1) - (fun i => f (i + k)) i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only
      rw [show i + 1 + k = i + (k + 1) by omega]
      abel
    rw [e, ih, Finset.sum_range_sub (fun i => f (i + k))]
    simp only [zero_add]
    rw [show n + k = k + n by omega, hf, succ_nsmul]
    abel

theorem sum_rSpan (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (r : ℕ) :
    ∑ i ∈ Finset.range n, rSpan a n r i = r := by
  unfold rSpan
  rw [sum_shift_telescope (unrolled a n) 1 n (unrolled_add a hn) r]
  simp

theorem sortedPoint_strictMono (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    (n : ℕ) : StrictMono (sortedPoint a n) := by
  apply Monotone.strictMono_of_injective (Tuple.monotone_sort (pts a n))
  intro x y hxy
  have h : pts a n (Tuple.sort (pts a n) x) = pts a n (Tuple.sort (pts a n) y) := hxy
  have h2 := ha h
  have h3 : Tuple.sort (pts a n) x = Tuple.sort (pts a n) y := Fin.ext h2
  exact (Tuple.sort (pts a n)).injective h3

theorem sortedPoint_mem (a : ℕ → ℝ) (n : ℕ) (k : Fin n) :
    0 ≤ sortedPoint a n k ∧ sortedPoint a n k < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem unrolled_strictMono (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    {n : ℕ} (hn : 0 < n) : StrictMono (unrolled a n) := by
  intro j j' hjj
  rw [unrolled_eq' a hn, unrolled_eq' a hn]
  have hq : j / n ≤ j' / n := Nat.div_le_div_right hjj.le
  rcases hq.lt_or_eq with hlt | heq
  · have h1 := (sortedPoint_mem a n ⟨j % n, Nat.mod_lt _ hn⟩).2
    have h2 := (sortedPoint_mem a n ⟨j' % n, Nat.mod_lt _ hn⟩).1
    have h3 : ((j / n : ℕ) : ℝ) + 1 ≤ ((j' / n : ℕ) : ℝ) := by exact_mod_cast hlt
    linarith
  · have hm : j % n < j' % n := by
      have e1 := Nat.div_add_mod j n
      have e2 := Nat.div_add_mod j' n
      rw [heq] at e1
      omega
    have := sortedPoint_strictMono a ha n (show (⟨j % n, Nat.mod_lt _ hn⟩ : Fin n) < ⟨j' % n, Nat.mod_lt _ hn⟩ from hm)
    rw [heq]
    linarith

/-- forward range description -/
theorem unrolled_mem (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    ∃ t < n, ∃ m : ℕ, unrolled a n j = Int.fract (a t) + m := by
  rw [unrolled_eq' a hn]
  refine ⟨(Tuple.sort (pts a n) ⟨j % n, Nat.mod_lt _ hn⟩ : ℕ), Fin.is_lt _, j / n, rfl⟩

/-- backward range description -/
theorem mem_unrolled (a : ℕ → ℝ) {n t : ℕ} (ht : t < n) (m : ℕ) :
    ∃ j, unrolled a n j = Int.fract (a t) + m := by
  set k := (Tuple.sort (pts a n)).symm ⟨t, ht⟩ with hk
  refine ⟨k + m * n, ?_⟩
  rw [unrolled_eq a m k.is_lt]
  congr 1
  show pts a n (Tuple.sort (pts a n) ⟨k, k.is_lt⟩) = _
  have : (⟨(k : ℕ), k.is_lt⟩ : Fin n) = k := rfl
  rw [this, hk, Equiv.apply_symm_apply]
  rfl

theorem unrolled_add_mul (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j m : ℕ) :
    unrolled a n (j + m * n) = unrolled a n j + m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show j + (k + 1) * n = (j + k * n) + n by ring, unrolled_add a hn, ih]
    push_cast; ring

theorem rearrange (h : ℕ → ℝ) (hh : Antitone h) (r : ℕ) (s : ℕ → ℕ) :
    ∀ (S : Finset ℕ), (∀ k, (S.filter (fun i => s i < k)).card ≤ r * k) →
      ∑ i ∈ S, h (s i) ≤ ∑ j ∈ Finset.range S.card, h (j / r) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨i0, hi0, hmax⟩ := S.exists_max_image s hne
    have h4 : 0 < S.card := Finset.card_pos.mpr hne
    have hq : (S.card - 1) / r ≤ s i0 := by
      by_contra hlt
      push Not at hlt
      have h1 := hS ((S.card - 1) / r)
      have h2 : S.filter (fun i => s i < (S.card - 1) / r) = S := by
        apply Finset.filter_true_of_mem
        intro i hi; exact lt_of_le_of_lt (hmax i hi) hlt
      rw [h2] at h1
      have h3 : r * ((S.card - 1) / r) ≤ S.card - 1 := Nat.mul_div_le _ _
      omega
    have hsub : S.erase i0 ⊂ S := Finset.erase_ssubset hi0
    have ih' := ih _ hsub (fun k => le_trans (Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.erase_subset _ _))) (hS k))
    rw [Finset.card_erase_of_mem hi0] at ih'
    rw [← Finset.add_sum_erase S _ hi0]
    have hc : S.card = (S.card - 1) + 1 := by omega
    rw [hc, Finset.sum_range_succ]
    have := hh hq
    linarith


theorem card_ho_le (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    {n : ℕ} (hn : 0 < n) (R : ℕ) (z : ℝ) (S : Finset ℕ) (hS : S ⊆ Finset.range n)
    (hin : ∀ i ∈ S, ∃ m : ℤ, unrolled a n i ≤ z + m ∧ z + m < unrolled a n (i + R)) :
    S.card ≤ R := by
  set f : ℕ → ℤ := fun j => ⌈unrolled a n j - z⌉ with hf
  have hper : ∀ j, f (j + n) = f j + 1 := by
    intro j
    simp only [hf]
    rw [unrolled_add a hn, show unrolled a n j + 1 - z = (unrolled a n j - z) + 1 by ring,
      Int.ceil_add_one]
  have htel := sum_shift_telescope f 1 n hper R
  have hmono : StrictMono (unrolled a n) := unrolled_strictMono a ha hn
  have hnn : ∀ i, 0 ≤ f (i + R) - f i := by
    intro i
    have : f i ≤ f (i + R) := by
      simp only [hf]
      apply Int.ceil_mono
      have := hmono.monotone (show i ≤ i + R by omega)
      linarith
    omega
  have h1 : ∀ i ∈ S, (1 : ℤ) ≤ f (i + R) - f i := by
    intro i hi
    obtain ⟨m, hm1, hm2⟩ := hin i hi
    have e1 : f i ≤ m := by
      simp only [hf]; rw [Int.ceil_le]; linarith
    have e2 : m < f (i + R) := by
      simp only [hf]; rw [Int.lt_ceil]; linarith
    omega
  have : (S.card : ℤ) ≤ R := by
    calc (S.card : ℤ) = ∑ i ∈ S, (1 : ℤ) := by simp
      _ ≤ ∑ i ∈ S, (f (i + R) - f i) := Finset.sum_le_sum h1
      _ ≤ ∑ i ∈ Finset.range n, (f (i + R) - f i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hS (fun i _ _ => hnn i)
      _ = R := by rw [htel]; simp
  exact_mod_cast this

theorem lift {u v : ℕ → ℝ} (hu : StrictMono u) (hv : StrictMono v)
    (hsub : ∀ j, ∃ k, v k = u j) {A j0 : ℕ} (h0 : v A = u j0) (w : ℕ)
    (hw : ∀ k, A < k → k ≤ A + w → ∃ j, u j = v k) : v (A + w) = u (j0 + w) := by
  induction w with
  | zero => simpa using h0
  | succ w ih =>
    have ih' := ih (fun k h1 h2 => hw k h1 (by omega))
    obtain ⟨j, hj⟩ := hw (A + (w + 1)) (by omega) le_rfl
    obtain ⟨k', hk'⟩ := hsub (j0 + (w + 1))
    have h1 : j0 + w < j := by
      rw [← hu.lt_iff_lt, hj, ← ih']; exact hv (by omega)
    have h2 : A + w < k' := by
      rw [← hv.lt_iff_lt, hk', ih']; exact hu (by omega)
    have h3 : j ≤ j0 + (w + 1) := by
      rw [← hu.le_iff_le, hj, ← hk']; exact hv.monotone (by omega)
    have : j = j0 + (w + 1) := by omega
    rw [← hj, this]

theorem rSpan_mod (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (r i : ℕ) :
    rSpan a N r i = rSpan a N r (i % N) := by
  unfold rSpan
  have hi : i = i % N + (i / N) * N := by
    have := Nat.mod_add_div i N; rw [mul_comm] at this; omega
  conv_lhs => rw [hi, show i % N + i / N * N + r = (i % N + r) + i / N * N by ring]
  rw [unrolled_add_mul a hN, unrolled_add_mul a hN]
  ring

theorem minSpan_le_rSpan (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (r i : ℕ) :
    minSpan a N r ≤ rSpan a N r i := by
  rw [rSpan_mod a hN]
  unfold minSpan
  exact ciInf_le (Set.finite_range (fun j : Fin N => rSpan a N r j)).bddBelow
    (⟨i % N, Nat.mod_lt _ hN⟩ : Fin N)

theorem log_succ_sub_le {y : ℝ} (hy : 0 < y) : Real.log (y + 1) - Real.log y ≤ 1 / y := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (y + 1) / y by positivity)
  rw [Real.log_div (by linarith) hy.ne'] at h
  have : (y + 1) / y - 1 = 1 / y := by rw [add_div, div_self hy.ne']; ring
  linarith

theorem harmonic_lower {N r : ℕ} (hN : 1 ≤ N) (hr : 1 ≤ r) :
    (r + 1 : ℝ) * (Real.log (1 + 1 / (r : ℝ)) - 1 / (N : ℝ)) ≤
      ∑ j ∈ Finset.range N, (1 : ℝ) / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) := by
  set R : ℝ := (r : ℝ) + 1 with hR
  set C : ℝ := R * ((N : ℝ) + 1) with hC
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have step1 : ∀ j ∈ Finset.range N,
      R * ((fun j : ℕ => Real.log (C - j)) j - (fun j : ℕ => Real.log (C - j)) (j + 1)) ≤
      (1 : ℝ) / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp only
    push_cast
    have hj1 : j + 1 ≤ (r + 1) * (j / (r + 1)) + (r + 1) := by
      have := Nat.div_add_mod j (r + 1); have := Nat.mod_lt j (show 0 < r + 1 by omega)
      omega
    have hj2 : j / (r + 1) ≤ j := Nat.div_le_self _ _
    have hj1' : (j : ℝ) + 1 ≤ R * ((j / (r + 1) : ℕ) : ℝ) + R := by
      rw [hR]; exact_mod_cast hj1
    have hj2' : ((j / (r + 1) : ℕ) : ℝ) ≤ j := by exact_mod_cast hj2
    have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    have hpos : 0 < (N : ℝ) - ((j / (r + 1) : ℕ) : ℝ) := by linarith
    have hy : 0 < C - ((j : ℝ) + 1) := by
      rw [hC, hR]; nlinarith
    have h2 := log_succ_sub_le hy
    rw [show C - ((j : ℝ) + 1) + 1 = C - j by ring] at h2
    have h3 : R * (1 / (C - ((j : ℝ) + 1))) ≤ (1 : ℝ) / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) := by
      rw [mul_one_div, div_le_div_iff₀ hy hpos]
      rw [hC]; nlinarith
    calc R * (Real.log (C - j) - Real.log (C - ((j : ℝ) + 1)))
        ≤ R * (1 / (C - ((j : ℝ) + 1))) := by
          apply mul_le_mul_of_nonneg_left h2; rw [hR]; linarith
      _ ≤ _ := h3
  have hsum := Finset.sum_range_sub (fun j : ℕ => Real.log (C - j)) N
  simp only [Nat.cast_zero, sub_zero] at hsum
  have hsum' : ∑ j ∈ Finset.range N,
      ((fun j : ℕ => Real.log (C - j)) j - (fun j : ℕ => Real.log (C - j)) (j + 1)) =
      Real.log C - Real.log (C - N) := by
    rw [show Real.log C - Real.log (C - N) = -(Real.log (C - N) - Real.log C) by ring,
      ← hsum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro j _; push_cast; ring
  have hr0 : (r : ℝ) ≠ 0 := by intro h; linarith
  have hCN : 0 < C - N := by rw [hC, hR]; nlinarith
  have hC0 : 0 < C := by linarith
  have hq : 0 < 1 + 1 / (r : ℝ) := by positivity
  have hy0 : 0 < (C - N) * (1 + 1 / (r : ℝ)) / C := by positivity
  have hlog := Real.log_le_sub_one_of_pos hy0
  rw [Real.log_div (by positivity) hC0.ne', Real.log_mul hCN.ne' hq.ne'] at hlog
  have hy1 : (C - N) * (1 + 1 / (r : ℝ)) / C - 1 ≤ 1 / (N : ℝ) := by
    have e : (C - N) * (1 + 1 / (r : ℝ)) / C - 1 = 1 / ((r : ℝ) * ((N : ℝ) + 1)) := by
      rw [hC, hR]; field_simp; ring
    rw [e]
    apply one_div_le_one_div_of_le (by linarith)
    nlinarith
  calc R * (Real.log (1 + 1 / (r : ℝ)) - 1 / (N : ℝ))
      ≤ R * (Real.log C - Real.log (C - N)) := by
        apply mul_le_mul_of_nonneg_left _ (by rw [hR]; linarith); linarith
    _ = ∑ j ∈ Finset.range N,
        R * ((fun j : ℕ => Real.log (C - j)) j - (fun j : ℕ => Real.log (C - j)) (j + 1)) := by
        rw [← Finset.mul_sum, hsum']
    _ ≤ _ := Finset.sum_le_sum step1

theorem main (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k)) {r : ℕ} (hr : 1 ≤ r)
    {L : ℝ} (hL : 0 < L) {n0 : ℕ} (hn0 : 1 ≤ n0)
    (hm : ∀ t, n0 ≤ t → L < (t : ℝ) * minSpan a t r)
    {N : ℕ} (hN : 2 * n0 ≤ N) :
    L * ((r + 1 : ℝ) * (Real.log (1 + 1 / (r : ℝ)) - 1 / (N : ℝ))) ≤ r := by
  classical
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  -- points of the arc
  let P : ℕ → ℕ → Prop := fun i b =>
    ∀ w, w ≤ r → ∃ t < b, ∃ m : ℕ, unrolled a N (i + w) = Int.fract (a t) + m
  have hPN : ∀ i, ∃ b, P i b := fun i => ⟨N, fun w _ => unrolled_mem a hN0 (i + w)⟩
  let b : ℕ → ℕ := fun i => max n0 (Nat.find (hPN i))
  let s : ℕ → ℕ := fun i => N - b i
  have hbN : ∀ i, b i ≤ N := by
    intro i
    exact max_le (by omega) (Nat.find_min' (hPN i) (fun w _ => unrolled_mem a hN0 (i + w)))
  have hb0 : ∀ i, n0 ≤ b i := fun i => le_max_left _ _
  -- each span is at least L / b i
  have hlen : ∀ i, L / (b i : ℝ) ≤ rSpan a N r i := by
    intro i
    have hb1 : 0 < b i := by have := hb0 i; omega
    have hP : P i (b i) := by
      intro w hw
      obtain ⟨t, ht, m, hm'⟩ := Nat.find_spec (hPN i) w hw
      exact ⟨t, lt_of_lt_of_le ht (le_max_right _ _), m, hm'⟩
    have hu := unrolled_strictMono a ha hb1
    have hv := unrolled_strictMono a ha hN0
    have hsub : ∀ j, ∃ k, unrolled a N k = unrolled a (b i) j := by
      intro j
      obtain ⟨t, ht, m, hm'⟩ := unrolled_mem a hb1 j
      obtain ⟨k, hk⟩ := mem_unrolled a (show t < N by have := hbN i; omega) m
      exact ⟨k, by rw [hk, hm']⟩
    have hin : ∀ w, w ≤ r → ∃ j, unrolled a (b i) j = unrolled a N (i + w) := by
      intro w hw
      obtain ⟨t, ht, m, hm'⟩ := hP w hw
      obtain ⟨j, hj⟩ := mem_unrolled a ht m
      exact ⟨j, by rw [hj, hm']⟩
    obtain ⟨j0, hj0⟩ := hin 0 (Nat.zero_le _)
    rw [add_zero] at hj0
    have key := lift hu hv hsub hj0.symm r (fun k h1 h2 => by
      obtain ⟨j, hj⟩ := hin (k - i) (by omega)
      exact ⟨j, by rw [hj, show i + (k - i) = k by omega]⟩)
    have e : rSpan a N r i = rSpan a (b i) r j0 := by
      unfold rSpan; rw [key, hj0]
    rw [e]
    have h1 := minSpan_le_rSpan a hb1 r j0
    have h2 := hm (b i) (hb0 i)
    have hbpos : (0 : ℝ) < (b i : ℝ) := by exact_mod_cast hb1
    rw [div_le_iff₀ hbpos]
    nlinarith
  -- counting
  have hcount : ∀ k, ((Finset.range N).filter (fun i => s i < k)).card ≤ (r + 1) * k := by
    intro k
    by_cases hk : N - n0 < k
    · calc _ ≤ (Finset.range N).card := Finset.card_filter_le _ _
        _ = N := Finset.card_range N
        _ ≤ (r + 1) * k := by
          have : 2 * (N - n0) ≥ N := by omega
          nlinarith
    · push Not at hk
      have hsub : (Finset.range N).filter (fun i => s i < k) ⊆
          (Finset.range k).biUnion (fun d => (Finset.range N).filter (fun i =>
            ∃ m : ℤ, unrolled a N i ≤ Int.fract (a (N - k + d)) + m ∧
              Int.fract (a (N - k + d)) + m < unrolled a N (i + (r + 1)))) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
        have hsi : s i = N - b i := rfl
        have hbk : N - k < b i := by have := hbN i; omega
        have hfind : N - k < Nat.find (hPN i) := by
          rcases le_or_gt (Nat.find (hPN i)) (N - k) with h | h
          · exfalso
            have : b i ≤ N - k := max_le (by omega) h
            omega
          · exact h
        have hnot : ¬ P i (N - k) := Nat.find_min (hPN i) hfind
        obtain ⟨w, hw, hw2⟩ : ∃ w, w ≤ r ∧ ∀ t, t < N - k → ∀ m : ℕ,
            unrolled a N (i + w) ≠ Int.fract (a t) + m := by
          by_contra hc
          apply hnot
          intro w hw
          by_contra hc2
          exact hc ⟨w, hw, fun t ht m heq => hc2 ⟨t, ht, m, heq⟩⟩
        obtain ⟨t, ht, m, hm'⟩ := unrolled_mem a hN0 (i + w)
        have htk : N - k ≤ t := by
          by_contra hcon
          exact hw2 t (by omega) m hm'
        refine ⟨t - (N - k), by omega, hi.1, ?_⟩
        rw [show N - k + (t - (N - k)) = t by omega]
        refine ⟨(m : ℤ), ?_, ?_⟩
        · push_cast; rw [← hm']
          exact (unrolled_strictMono a ha hN0).monotone (by omega)
        · push_cast; rw [← hm']
          exact (unrolled_strictMono a ha hN0) (by omega)
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ ∑ d ∈ Finset.range k, ((Finset.range N).filter (fun i =>
            ∃ m : ℤ, unrolled a N i ≤ Int.fract (a (N - k + d)) + m ∧
              Int.fract (a (N - k + d)) + m < unrolled a N (i + (r + 1)))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ d ∈ Finset.range k, (r + 1) := Finset.sum_le_sum (fun d _ =>
            card_ho_le a ha hN0 (r + 1) _ _ (Finset.filter_subset _ _)
              (fun i hi => (Finset.mem_filter.mp hi).2))
        _ = (r + 1) * k := by simp [mul_comm]
  -- rearrangement
  have hh : Antitone (fun k : ℕ => -(L / ((N : ℝ) - ((min k (N - 1) : ℕ) : ℝ)))) := by
    intro x y hxy
    simp only [neg_le_neg_iff]
    have h1 : min x (N - 1) ≤ min y (N - 1) := min_le_min_right _ hxy
    have h2 : min y (N - 1) ≤ N - 1 := min_le_right _ _
    have h1' : ((min x (N - 1) : ℕ) : ℝ) ≤ ((min y (N - 1) : ℕ) : ℝ) := by exact_mod_cast h1
    have h2' : ((min y (N - 1) : ℕ) : ℝ) + 1 ≤ N := by
      have : min y (N - 1) + 1 ≤ N := by omega
      exact_mod_cast this
    apply div_le_div_of_nonneg_left hL.le (by linarith) (by linarith)
  have hre := rearrange _ hh (r + 1) s (Finset.range N) hcount
  rw [Finset.card_range] at hre
  have es : ∀ i, ((N : ℝ) - ((min (s i) (N - 1) : ℕ) : ℝ)) = (b i : ℝ) := by
    intro i
    have h1 : min (s i) (N - 1) = N - b i := by
      have := hb0 i; have := hbN i; simp only [s]; omega
    rw [h1, Nat.cast_sub (hbN i)]; ring
  have ej : ∀ j ∈ Finset.range N, ((min (j / (r + 1)) (N - 1) : ℕ) : ℝ) =
      ((j / (r + 1) : ℕ) : ℝ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have : j / (r + 1) ≤ N - 1 := le_trans (Nat.div_le_self _ _) (by omega)
    rw [min_eq_left this]
  simp only [Finset.sum_neg_distrib, neg_le_neg_iff] at hre
  have h1 : ∑ j ∈ Finset.range N, L / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) ≤
      ∑ i ∈ Finset.range N, L / (b i : ℝ) := by
    have e1 : ∑ j ∈ Finset.range N, L / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) =
        ∑ j ∈ Finset.range N, L / ((N : ℝ) - ((min (j / (r + 1)) (N - 1) : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl; intro j hj; rw [ej j hj]
    have e2 : ∑ i ∈ Finset.range N, L / (b i : ℝ) =
        ∑ i ∈ Finset.range N, L / ((N : ℝ) - ((min (s i) (N - 1) : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl; intro i _; rw [es i]
    rw [e1, e2]; exact hre
  have h2 : ∑ i ∈ Finset.range N, L / (b i : ℝ) ≤ r := by
    rw [← sum_rSpan a hN0 r]
    exact Finset.sum_le_sum (fun i _ => hlen i)
  have h3 := harmonic_lower (show 1 ≤ N by omega) hr
  have e : ∑ j ∈ Finset.range N, L / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) =
      L * ∑ j ∈ Finset.range N, (1 : ℝ) / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [mul_one_div]
  calc L * ((r + 1 : ℝ) * (Real.log (1 + 1 / (r : ℝ)) - 1 / (N : ℝ)))
      ≤ L * ∑ j ∈ Finset.range N, (1 : ℝ) / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 hL.le
    _ = _ := e.symm
    _ ≤ _ := h1
    _ ≤ _ := h2

end E1221W3

theorem OMA.solution : type_of% @Erdos1221.erdos_1221.variants.smallLambda_le := by
  intro r hr
  unfold smallLambda
  apply iSup₂_le
  intro a ha
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx1, hx2⟩ := exists_between hcon
  have hxtop : x ≠ ⊤ := ne_top_of_lt hx2
  set L := x.toReal
  have hxL : x = ENNReal.ofReal L := (ENNReal.ofReal_toReal hxtop).symm
  rw [hxL] at hx1 hx2
  have hcL := ENNReal.ofReal_lt_ofReal_iff'.mp hx1
  have hL : 0 < L := hcL.2
  have hev := Filter.eventually_lt_of_lt_liminf hx2
  rw [Filter.eventually_atTop] at hev
  obtain ⟨n0, hn0⟩ := hev
  have hm : ∀ t, max n0 1 ≤ t → L < (t : ℝ) * minSpan a t r := fun t ht =>
    (ENNReal.ofReal_lt_ofReal_iff'.mp (hn0 t (le_trans (le_max_left _ _) ht))).1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogpos : 0 < Real.log (1 + 1 / (r : ℝ)) := by
    apply Real.log_pos; have := one_div_pos.mpr hr0; linarith
  -- L * (r+1) * log > r
  have hgap : 0 < L * ((r + 1 : ℝ) * Real.log (1 + 1 / (r : ℝ))) - r := by
    have h := hcL.1
    have e : (r : ℝ) / ((r : ℝ) + 1) * (1 / Real.log (1 + 1 / (r : ℝ))) =
        r / (((r : ℝ) + 1) * Real.log (1 + 1 / (r : ℝ))) := by
      field_simp
    rw [e, div_lt_iff₀ (by positivity)] at h
    linarith
  obtain ⟨m, hmm⟩ := exists_nat_gt (L * (r + 1 : ℝ) /
    (L * ((r + 1 : ℝ) * Real.log (1 + 1 / (r : ℝ))) - r))
  obtain ⟨N, hN⟩ : ∃ N, N = max (2 * max n0 1) (m + 1) := ⟨_, rfl⟩
  have hN1 : 2 * max n0 1 ≤ N := by omega
  have hNm : m + 1 ≤ N := by omega
  have key := E1221W3.main a ha hr hL (le_max_right n0 1) hm hN1
  have hNr : (m : ℝ) + 1 ≤ N := by exact_mod_cast hNm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hNpos : (0 : ℝ) < N := by linarith
  have h5 : L * (r + 1 : ℝ) * (1 / (N : ℝ)) <
      L * ((r + 1 : ℝ) * Real.log (1 + 1 / (r : ℝ))) - r := by
    rw [mul_one_div, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hgap] at hmm
    nlinarith [mul_le_mul_of_nonneg_left hNr hgap.le]
  have e : L * ((r + 1 : ℝ) * (Real.log (1 + 1 / (r : ℝ)) - 1 / (N : ℝ))) =
      L * ((r + 1 : ℝ) * Real.log (1 + 1 / (r : ℝ))) - L * (r + 1 : ℝ) * (1 / (N : ℝ)) := by ring
  rw [e] at key
  linarith
