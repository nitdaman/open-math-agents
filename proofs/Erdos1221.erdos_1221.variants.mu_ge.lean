import FormalConjectures.ErdosProblems.«1221»

-- Problem: Erdős Problem 1221 — mu ge
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1221.lean:214 (declaration Erdos1221.erdos_1221.variants.mu_ge)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Proof of the de Bruijn--Erdos lower bound for `mu` (one new point: r + 1 new spans sum to r old spans). -/

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

theorem skip {u v : ℕ → ℝ} (hu : StrictMono u) (hv : StrictMono v)
    (hsub : ∀ j, ∃ k, v k = u j) {k j : ℕ} (h0 : v k = u j)
    (hnew : ∀ j', u j' ≠ v (k + 1)) (h2 : ∃ j', u j' = v (k + 2)) :
    v (k + 2) = u (j + 1) := by
  obtain ⟨j', hj'⟩ := h2
  have e1 : j < j' := by
    rw [← hu.lt_iff_lt, hj', ← h0]; exact hv (by omega)
  obtain ⟨k', hk'⟩ := hsub (j + 1)
  have e2 : k < k' := by
    rw [← hv.lt_iff_lt, hk', h0]; exact hu (by omega)
  have e3 : k' ≠ k + 1 := by
    intro h; rw [h] at hk'; exact hnew _ hk'.symm
  have e4 : j' ≤ j + 1 := by
    rw [← hu.le_iff_le, hj', ← hk']; exact hv.monotone (by omega)
  have : j' = j + 1 := by omega
  rw [← hj', this]

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

theorem rSpan_le_maxSpan (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (r i : ℕ) :
    rSpan a N r i ≤ maxSpan a N r := by
  rw [rSpan_mod a hN]
  unfold maxSpan
  exact le_ciSup (Set.finite_range (fun j : Fin N => rSpan a N r j)).bddAbove
    (⟨i % N, Nat.mod_lt _ hN⟩ : Fin N)

theorem minSpan_pos (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    {N r : ℕ} (hN : 0 < N) (hr : 1 ≤ r) : 0 < minSpan a N r := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun j : Fin N => rSpan a N r j)
  unfold minSpan
  rw [← hi]
  unfold rSpan
  have := unrolled_strictMono a ha hN (show (i : ℕ) < i + r by omega)
  linarith

theorem le_N_maxSpan (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (r : ℕ) :
    (r : ℝ) ≤ N * maxSpan a N r := by
  rw [← sum_rSpan a hN r]
  calc ∑ i ∈ Finset.range N, rSpan a N r i ≤ ∑ i ∈ Finset.range N, maxSpan a N r :=
        Finset.sum_le_sum (fun i _ => rSpan_le_maxSpan a hN r i)
    _ = N * maxSpan a N r := by simp

theorem unrolled_lt (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (k : ℕ) : unrolled a N k < k + 1 := by
  rw [unrolled_eq' a hN]
  have h1 := (sortedPoint_mem a N ⟨k % N, Nat.mod_lt _ hN⟩).2
  have h2 : ((k / N : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.div_le_self k N
  linarith

theorem fract_eq_of_add {x y : ℝ} {m m' : ℕ} (h : Int.fract x + m = Int.fract y + m') :
    Int.fract x = Int.fract y := by
  have := congrArg Int.fract h
  rwa [Int.fract_add_natCast, Int.fract_add_natCast, Int.fract_fract, Int.fract_fract] at this

/-- One step: the new point creates `r + 1` new `r`-spans whose total is the total of `r` old
`r`-spans. -/
theorem step (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k)) {n r : ℕ}
    (hr : 1 ≤ r) (hn : 2 * r ≤ n) :
    ((r : ℝ) + 1) * minSpan a (n + 1) r ≤ r * maxSpan a n r := by
  have hn0 : 0 < n := by omega
  have hn1 : 0 < n + 1 := by omega
  have hu := unrolled_strictMono a ha hn0
  have hv := unrolled_strictMono a ha hn1
  have hsub : ∀ j, ∃ k, unrolled a (n + 1) k = unrolled a n j := by
    intro j
    obtain ⟨t, ht, m, hm⟩ := unrolled_mem a hn0 j
    obtain ⟨k, hk⟩ := mem_unrolled a (show t < n + 1 by omega) m
    exact ⟨k, by rw [hk, hm]⟩
  obtain ⟨K, hK⟩ := mem_unrolled a (show n < n + 1 by omega) r
  have hKr : r ≤ K := by
    by_contra h
    have h1 := unrolled_lt a hn1 K
    have h2 : (K : ℝ) + 1 ≤ r := by exact_mod_cast (show K + 1 ≤ r by omega)
    have h3 := Int.fract_nonneg (a n)
    linarith
  obtain ⟨A, hA⟩ : ∃ A, A = K - r := ⟨_, rfl⟩
  have hAK : K = A + r := by omega
  have hnew : ∀ j, unrolled a n j ≠ unrolled a (n + 1) K := by
    intro j hj
    obtain ⟨t, ht, m, hm⟩ := unrolled_mem a hn0 j
    rw [hm, hK] at hj
    have := ha (fract_eq_of_add hj)
    omega
  have hold : ∀ k, A ≤ k → k ≤ A + 2 * r → k ≠ K → ∃ j, unrolled a n j = unrolled a (n + 1) k := by
    intro k hk1 hk2 hkK
    obtain ⟨t, ht, m, hm⟩ := unrolled_mem a hn1 k
    by_cases htn : t < n
    · obtain ⟨j, hj⟩ := mem_unrolled a htn m
      exact ⟨j, by rw [hj, hm]⟩
    · exfalso
      have htn' : t = n := by omega
      rw [htn'] at hm
      rcases le_or_gt r m with hmr | hmr
      · have e := unrolled_add_mul a hn1 K (m - r)
        rw [hK, Nat.cast_sub hmr] at e
        have e2 : unrolled a (n + 1) (K + (m - r) * (n + 1)) = unrolled a (n + 1) k := by
          rw [e, hm]; ring
        have := hv.injective e2
        rcases Nat.eq_zero_or_pos (m - r) with h0 | h0
        · rw [h0] at this; omega
        · have : (n + 1) ≤ (m - r) * (n + 1) := Nat.le_mul_of_pos_left _ h0
          omega
      · have e := unrolled_add_mul a hn1 k (r - m)
        rw [hm, Nat.cast_sub hmr.le] at e
        have e2 : unrolled a (n + 1) (k + (r - m) * (n + 1)) = unrolled a (n + 1) K := by
          rw [e, hK]; ring
        have := hv.injective e2
        have h0 : 0 < r - m := by omega
        have : (n + 1) ≤ (r - m) * (n + 1) := Nat.le_mul_of_pos_left _ h0
        omega
  obtain ⟨j0, hj0⟩ := hold A le_rfl (by omega) (by omega)
  have h1 : ∀ w, w ≤ r - 1 → unrolled a (n + 1) (A + w) = unrolled a n (j0 + w) := fun w hw =>
    lift hu hv hsub hj0.symm w (fun k hk1 hk2 => hold k (by omega) (by omega) (by omega))
  have h2 : unrolled a (n + 1) (A + r + 1) = unrolled a n (j0 + r) := by
    have e1 := h1 (r - 1) le_rfl
    rw [show A + (r - 1) = A + r - 1 by omega] at e1
    have e := skip hu hv hsub e1 (by rw [show A + r - 1 + 1 = K by omega]; exact hnew)
      (hold (A + r - 1 + 2) (by omega) (by omega) (by omega))
    rw [show A + r - 1 + 2 = A + r + 1 by omega, show j0 + (r - 1) + 1 = j0 + r by omega] at e
    exact e
  have h3 : ∀ w, w ≤ r - 1 →
      unrolled a (n + 1) (A + r + 1 + w) = unrolled a n (j0 + r + w) := fun w hw =>
    lift hu hv hsub h2 w (fun k hk1 hk2 => hold k (by omega) (by omega) (by omega))
  -- the sum of the r + 1 new spans
  have hS : ∑ w ∈ Finset.range (r + 1), rSpan a (n + 1) r (A + w) =
      ∑ w ∈ Finset.range r, rSpan a n r (j0 + w) := by
    unfold rSpan
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have e1 : ∑ w ∈ Finset.range (r + 1), unrolled a (n + 1) (A + w + r) =
        ∑ w ∈ Finset.range r, unrolled a n (j0 + w + r) + unrolled a (n + 1) K := by
      rw [Finset.sum_range_succ']
      congr 1
      · apply Finset.sum_congr rfl
        intro w hw
        rw [Finset.mem_range] at hw
        rw [show A + (w + 1) + r = A + r + 1 + w by ring, h3 w (by omega),
          show j0 + r + w = j0 + w + r by ring]
      · rw [hAK]; ring_nf
    have e2 : ∑ w ∈ Finset.range (r + 1), unrolled a (n + 1) (A + w) =
        ∑ w ∈ Finset.range r, unrolled a n (j0 + w) + unrolled a (n + 1) K := by
      rw [Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro w hw
        rw [Finset.mem_range] at hw
        exact h1 w (by omega)
      · rw [hAK]
    rw [e1, e2]; ring
  have hlow : ((r : ℝ) + 1) * minSpan a (n + 1) r ≤
      ∑ w ∈ Finset.range (r + 1), rSpan a (n + 1) r (A + w) := by
    calc ((r : ℝ) + 1) * minSpan a (n + 1) r =
        ∑ w ∈ Finset.range (r + 1), minSpan a (n + 1) r := by simp
      _ ≤ _ := Finset.sum_le_sum (fun w _ => minSpan_le_rSpan a hn1 r (A + w))
  have hup : ∑ w ∈ Finset.range r, rSpan a n r (j0 + w) ≤ r * maxSpan a n r := by
    calc ∑ w ∈ Finset.range r, rSpan a n r (j0 + w) ≤
        ∑ w ∈ Finset.range r, maxSpan a n r :=
          Finset.sum_le_sum (fun w _ => rSpan_le_maxSpan a hn0 r (j0 + w))
      _ = r * maxSpan a n r := by simp
  linarith

end E1221W3

theorem OMA.solution : type_of% @Erdos1221.erdos_1221.variants.mu_ge := by
  intro r hr
  unfold mu
  apply le_iInf₂
  intro a ha
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx1, hx2⟩ := exists_between hcon
  have hxtop : x ≠ ⊤ := ne_top_of_lt hx2
  set c := x.toReal
  have hxc : x = ENNReal.ofReal c := (ENNReal.ofReal_toReal hxtop).symm
  rw [hxc] at hx1 hx2
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hc1 : c < 1 + 1 / (r : ℝ) := (ENNReal.ofReal_lt_ofReal_iff'.mp hx2).1
  have hev := Filter.eventually_lt_of_limsup_lt hx1
  rw [Filter.eventually_atTop] at hev
  obtain ⟨n0, hn0⟩ := hev
  have hratio : ∀ n, max n0 1 ≤ n → maxSpan a n r < c * minSpan a n r := by
    intro n hn
    have hnpos : 0 < n := by omega
    have hmpos := E1221W3.minSpan_pos a ha hnpos hr
    have h := hn0 n (by omega)
    rw [← ENNReal.ofReal_div_of_pos hmpos] at h
    have h' := (ENNReal.ofReal_lt_ofReal_iff'.mp h).1
    rwa [div_lt_iff₀ hmpos] at h'
  obtain ⟨n1, hn1⟩ : ∃ n1, n1 = max (max n0 1) (2 * r) := ⟨_, rfl⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = c * r / (r + 1) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one (by positivity)]
    have h := mul_lt_mul_of_pos_right hc1 hr0
    have e : (1 + 1 / (r : ℝ)) * r = r + 1 := by field_simp
    linarith
  have hdecay : ∀ n, n1 ≤ n → maxSpan a (n + 1) r ≤ ρ * maxSpan a n r := by
    intro n hn
    have h1 := hratio (n + 1) (by omega)
    have h2 := E1221W3.step a ha hr (show 2 * r ≤ n by omega)
    have h3 : c * minSpan a (n + 1) r ≤ ρ * maxSpan a n r := by
      rw [hρ, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hiter : ∀ k, maxSpan a (n1 + k) r ≤ ρ ^ k * maxSpan a n1 r := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc maxSpan a (n1 + (k + 1)) r = maxSpan a ((n1 + k) + 1) r := by rw [add_assoc]
        _ ≤ ρ * maxSpan a (n1 + k) r := hdecay _ (by omega)
        _ ≤ ρ * (ρ ^ k * maxSpan a n1 r) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (k + 1) * maxSpan a n1 r := by ring
  have ht : Tendsto (fun k : ℕ => ((n1 : ℝ) + k) * ρ ^ k * maxSpan a n1 r) atTop
      (nhds 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have h3 := ((h2.const_mul (n1 : ℝ)).add h1).mul_const (maxSpan a n1 r)
    simp only [mul_zero, zero_add, zero_mul] at h3
    refine h3.congr (fun k => by ring)
  have hev2 := ht.eventually (gt_mem_nhds hr0)
  rw [Filter.eventually_atTop] at hev2
  obtain ⟨k, hk⟩ := hev2
  have h4 := hk k le_rfl
  have h5 := E1221W3.le_N_maxSpan a (show 0 < n1 + k by omega) r
  have h6 := hiter k
  have hpos : (0 : ℝ) ≤ ((n1 + k : ℕ) : ℝ) := Nat.cast_nonneg _
  have h7 := mul_le_mul_of_nonneg_left h6 hpos
  push_cast at h5 h7
  nlinarith
