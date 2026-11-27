import FormalConjectures.ErdosProblems.«1221»

-- Problem: Erdős Problem 1221 — bigLambda ge
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1221.lean:194 (declaration Erdos1221.erdos_1221.variants.bigLambda_ge)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Proof of the de Bruijn--Erdos lower bound for `bigLambda` (arc-survival argument). -/

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

theorem span_transfer {u v : ℕ → ℝ} (hu : StrictMono u) (hv : StrictMono v)
    (hsub : ∀ j, ∃ k, v k = u j) {i i' r : ℕ} (hii : v i' = u i)
    (hin : ∀ k, u i < v k → v k < u (i + r) → ∃ j, u j = v k) :
    v (i' + r) = u (i + r) := by
  obtain ⟨i'', hi''⟩ := hsub (i + r)
  have hle : i' ≤ i'' := by
    rw [← hv.le_iff_le, hii, hi'']; exact hu.monotone (by omega)
  have key : (Finset.Icc i' i'').image v = (Finset.Icc i (i + r)).image u := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      have l1 : u i ≤ v k := hii ▸ hv.monotone hk1
      have l2 : v k ≤ u (i + r) := hi'' ▸ hv.monotone hk2
      obtain ⟨j, hj⟩ : ∃ j, u j = v k := by
        rcases l1.lt_or_eq with l1 | l1
        · rcases l2.lt_or_eq with l2 | l2
          · exact hin k l1 l2
          · exact ⟨_, l2.symm⟩
        · exact ⟨_, l1⟩
      refine ⟨j, ⟨?_, ?_⟩, hj⟩
      · rw [← hu.le_iff_le, hj]; exact l1
      · rw [← hu.le_iff_le, hj]; exact l2
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      obtain ⟨k, hk⟩ := hsub j
      refine ⟨k, ⟨?_, ?_⟩, hk⟩
      · rw [← hv.le_iff_le, hk, hii]; exact hu.monotone hj1
      · rw [← hv.le_iff_le, hk, hi'']; exact hu.monotone hj2
  have hc := congrArg Finset.card key
  rw [Finset.card_image_of_injective _ hv.injective,
    Finset.card_image_of_injective _ hu.injective] at hc
  simp only [Nat.card_Icc] at hc
  have : i'' = i' + r := by omega
  rw [this] at hi''; exact hi''

/-- A new point `t` lies strictly inside the `r`-arc of index `i` at time `n`. -/
def Inside (a : ℕ → ℝ) (n r i t : ℕ) : Prop :=
  ∃ m : ℤ, unrolled a n i < Int.fract (a t) + m ∧ Int.fract (a t) + m < unrolled a n (i + r)

theorem card_inside_le (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    {n : ℕ} (hn : 0 < n) (r t : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range n)
    (hin : ∀ i ∈ S, Inside a n r i t) : S.card ≤ r := by
  set z := Int.fract (a t)
  set f : ℕ → ℤ := fun j => ⌈unrolled a n j - z⌉ with hf
  have hper : ∀ j, f (j + n) = f j + 1 := by
    intro j
    simp only [hf]
    rw [unrolled_add a hn, show unrolled a n j + 1 - z = (unrolled a n j - z) + 1 by ring,
      Int.ceil_add_one]
  have htel := sum_shift_telescope f 1 n hper r
  have hmono : StrictMono (unrolled a n) := unrolled_strictMono a ha hn
  have hnn : ∀ i, 0 ≤ f (i + r) - f i := by
    intro i
    have : f i ≤ f (i + r) := by
      simp only [hf]
      apply Int.ceil_mono
      have := hmono.monotone (show i ≤ i + r by omega)
      linarith
    omega
  have h1 : ∀ i ∈ S, (1 : ℤ) ≤ f (i + r) - f i := by
    intro i hi
    obtain ⟨m, hm1, hm2⟩ := hin i hi
    have e1 : f i ≤ m := by
      simp only [hf]; rw [Int.ceil_le]; linarith
    have e2 : m < f (i + r) := by
      simp only [hf]; rw [Int.lt_ceil]; linarith
    omega
  have : (S.card : ℤ) ≤ r := by
    calc (S.card : ℤ) = ∑ i ∈ S, (1 : ℤ) := by simp
      _ ≤ ∑ i ∈ S, (f (i + r) - f i) := Finset.sum_le_sum h1
      _ ≤ ∑ i ∈ Finset.range n, (f (i + r) - f i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hS (fun i _ _ => hnn i)
      _ = r := by rw [htel]; simp
  exact_mod_cast this

theorem unrolled_add_mul (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j m : ℕ) :
    unrolled a n (j + m * n) = unrolled a n j + m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show j + (k + 1) * n = (j + k * n) + n by ring, unrolled_add a hn, ih]
    push_cast; ring

theorem rSpan_le_maxSpan (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (r i : ℕ) :
    rSpan a N r i ≤ maxSpan a N r := by
  have e : rSpan a N r i = rSpan a N r (i % N) := by
    unfold rSpan
    have hi : i = i % N + (i / N) * N := by
      have := Nat.mod_add_div i N; rw [mul_comm] at this; omega
    conv_lhs => rw [hi, show i % N + i / N * N + r = (i % N + r) + i / N * N by ring]
    rw [unrolled_add_mul a hN, unrolled_add_mul a hN]
    ring
  rw [e]
  unfold maxSpan
  exact le_ciSup (Set.finite_range (fun j : Fin N => rSpan a N r j)).bddAbove (⟨i % N, Nat.mod_lt _ hN⟩ : Fin N)

theorem survive (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    {n N r i : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (hno : ∀ t, n ≤ t → t < N → ¬ Inside a n r i t) :
    rSpan a n r i ≤ maxSpan a N r := by
  have hN : 0 < N := by omega
  have hu := unrolled_strictMono a ha hn
  have hv := unrolled_strictMono a ha hN
  have hsub : ∀ j, ∃ k, unrolled a N k = unrolled a n j := by
    intro j
    obtain ⟨t, ht, m, hm⟩ := unrolled_mem a hn j
    obtain ⟨k, hk⟩ := mem_unrolled a (show t < N by omega) m
    exact ⟨k, by rw [hk, hm]⟩
  obtain ⟨i', hi'⟩ := hsub i
  have hin : ∀ k, unrolled a n i < unrolled a N k → unrolled a N k < unrolled a n (i + r) →
      ∃ j, unrolled a n j = unrolled a N k := by
    intro k h1 h2
    obtain ⟨t, ht, m, hm⟩ := unrolled_mem a hN k
    by_cases htn : t < n
    · obtain ⟨j, hj⟩ := mem_unrolled a htn m
      exact ⟨j, by rw [hj, hm]⟩
    · exfalso
      apply hno t (by omega) ht
      refine ⟨(m : ℤ), ?_, ?_⟩
      · push_cast; rw [← hm]; exact h1
      · push_cast; rw [← hm]; exact h2
  have key := span_transfer hu hv hsub hi' hin
  have : rSpan a n r i = rSpan a N r i' := by
    unfold rSpan; rw [key, hi']
  rw [this]
  exact rSpan_le_maxSpan a hN r i'

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

theorem one_div_le_log_sub {x : ℝ} (hx : 1 < x) : 1 / x ≤ Real.log x - Real.log (x - 1) := by
  have hx0 : 0 < x := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < (x - 1) / x by apply div_pos <;> linarith)
  rw [Real.log_div (by linarith) hx0.ne'] at h
  have : (x - 1) / x - 1 = -(1 / x) := by rw [sub_div, div_self hx0.ne']; ring
  linarith

theorem harmonic_bound {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    ∑ j ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + ((j / r : ℕ) : ℝ)) ≤
      r * (Real.log (1 + 1 / (r : ℝ)) + 1 / ((n : ℝ) - 1)) := by
  set B : ℝ := (r : ℝ) * ((n : ℝ) - 1) with hB
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hB0 : 0 < B := by rw [hB]; apply mul_pos <;> linarith
  have step1 : ∀ j ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + ((j / r : ℕ) : ℝ)) ≤
      r * ((fun j : ℕ => Real.log (B + j)) (j + 1) - (fun j : ℕ => Real.log (B + j)) j) := by
    intro j _
    simp only
    push_cast
    have hj : j + 1 ≤ r * (j / r) + r := by
      have := Nat.div_add_mod j r; have := Nat.mod_lt j (show 0 < r by omega); omega
    have hj' : (j : ℝ) + 1 ≤ r * ((j / r : ℕ) : ℝ) + r := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hq0 : (0 : ℝ) ≤ ((j / r : ℕ) : ℝ) := Nat.cast_nonneg _
    have hpos : 0 < (n : ℝ) + ((j / r : ℕ) : ℝ) := by linarith
    have hx : 1 < B + ((j : ℝ) + 1) := by linarith
    have h2 := one_div_le_log_sub hx
    rw [show B + ((j : ℝ) + 1) - 1 = B + j by ring] at h2
    have h3 : (1 : ℝ) / ((n : ℝ) + ((j / r : ℕ) : ℝ)) ≤ r * (1 / (B + ((j : ℝ) + 1))) := by
      rw [mul_one_div, div_le_div_iff₀ hpos (by linarith)]
      rw [hB]; nlinarith
    calc _ ≤ r * (1 / (B + ((j : ℝ) + 1))) := h3
      _ ≤ _ := by apply mul_le_mul_of_nonneg_left h2; linarith
  have hsum := Finset.sum_range_sub (fun j : ℕ => Real.log (B + j)) n
  simp only [Nat.cast_zero, add_zero] at hsum
  have hn1 : (n : ℝ) - 1 ≠ 0 := by intro h; linarith
  have hr0 : (r : ℝ) ≠ 0 := by intro h; linarith
  have hR : (1 + 1 / ((n : ℝ) - 1)) * (B * (1 + 1 / (r : ℝ))) = n * (r + 1) := by
    rw [hB]; field_simp; ring
  have hy0 : 0 < (B + n) / (B * (1 + 1 / (r : ℝ))) := by
    apply div_pos (by linarith); apply mul_pos hB0; positivity
  have hlog := Real.log_le_sub_one_of_pos hy0
  rw [Real.log_div (by linarith) (by positivity), Real.log_mul hB0.ne' (by positivity)] at hlog
  have hy1 : (B + n) / (B * (1 + 1 / (r : ℝ))) ≤ 1 + 1 / ((n : ℝ) - 1) := by
    rw [div_le_iff₀ (by positivity), hR, hB]; nlinarith
  calc _ ≤ ∑ j ∈ Finset.range n,
        r * ((fun j : ℕ => Real.log (B + j)) (j + 1) - (fun j : ℕ => Real.log (B + j)) j) :=
        Finset.sum_le_sum step1
    _ = r * (Real.log (B + n) - Real.log B) := by rw [← Finset.mul_sum, hsum]
    _ ≤ _ := by apply mul_le_mul_of_nonneg_left _ (by linarith); linarith

theorem main (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k)) {r : ℕ} (hr : 1 ≤ r)
    {L : ℝ} (hL : 0 < L) {n0 : ℕ} (hM : ∀ N, n0 ≤ N → (N : ℝ) * maxSpan a N r < L)
    {n : ℕ} (hn : 2 ≤ n) (hn0 : n0 ≤ n) :
    1 ≤ L * (Real.log (1 + 1 / (r : ℝ)) + 1 / ((n : ℝ) - 1)) := by
  classical
  have hn1 : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  let P : ℕ → ℕ → Prop := fun i s => ∀ t, n ≤ t → t < n + s → ¬ Inside a n r i t
  let s : ℕ → ℕ := fun i => Nat.findGreatest (P i) n
  have hP : ∀ i, P i (s i) := fun i =>
    Nat.findGreatest_spec (Nat.zero_le n) (fun t h1 h2 => absurd h2 (by omega))
  have hlen : ∀ i, rSpan a n r i ≤ L / ((n : ℝ) + (s i : ℝ)) := by
    intro i
    have h1 := survive a ha hn1 (show n ≤ n + s i by omega) (hP i)
    have h2 := hM (n + s i) (by omega)
    push_cast at h2
    have hpos : (0 : ℝ) < (n : ℝ) + (s i : ℝ) :=
      add_pos_of_pos_of_nonneg hnpos (Nat.cast_nonneg _)
    rw [le_div_iff₀ hpos]
    calc rSpan a n r i * ((n : ℝ) + (s i : ℝ)) ≤ maxSpan a (n + s i) r * ((n : ℝ) + (s i : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 hpos.le
      _ = ((n : ℝ) + (s i : ℝ)) * maxSpan a (n + s i) r := mul_comm _ _
      _ ≤ L := h2.le
  have hcount : ∀ k, ((Finset.range n).filter (fun i => s i < k)).card ≤ r * k := by
    intro k
    by_cases hk : n < k
    · calc _ ≤ (Finset.range n).card := Finset.card_filter_le _ _
        _ = n := Finset.card_range n
        _ ≤ r * k := by nlinarith
    · push Not at hk
      have hsub : (Finset.range n).filter (fun i => s i < k) ⊆
          (Finset.range k).biUnion
            (fun d => (Finset.range n).filter (fun i => Inside a n r i (n + d))) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
        refine ⟨s i, hi.2, hi.1, ?_⟩
        have hnot := Nat.findGreatest_is_greatest (P := P i)
          (show s i < s i + 1 by omega) (show s i + 1 ≤ n by omega)
        by_contra hcon
        apply hnot
        intro t ht1 ht2
        by_cases htt : t < n + s i
        · exact hP i t ht1 htt
        · have : t = n + s i := by omega
          rw [this]; exact hcon
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ ∑ d ∈ Finset.range k,
            ((Finset.range n).filter (fun i => Inside a n r i (n + d))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ d ∈ Finset.range k, r := Finset.sum_le_sum (fun d _ =>
            card_inside_le a ha hn1 r (n + d) _ (Finset.filter_subset _ _)
              (fun i hi => (Finset.mem_filter.mp hi).2))
        _ = r * k := by simp [mul_comm]
  have hsum := sum_rSpan a hn1 r
  have hh : Antitone (fun k : ℕ => L / ((n : ℝ) + k)) := by
    intro x y hxy
    apply div_le_div_of_nonneg_left hL.le (add_pos_of_pos_of_nonneg hnpos (Nat.cast_nonneg _))
    simp only [add_le_add_iff_left, Nat.cast_le]; exact hxy
  have hre := rearrange _ hh r s (Finset.range n) hcount
  rw [Finset.card_range] at hre
  have hhar := harmonic_bound hn hr
  have e : ∑ j ∈ Finset.range n, L / ((n : ℝ) + ((j / r : ℕ) : ℝ)) =
      L * ∑ j ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + ((j / r : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [mul_one_div]
  have h1 : (r : ℝ) ≤ ∑ i ∈ Finset.range n, L / ((n : ℝ) + (s i : ℝ)) := by
    rw [← hsum]; apply Finset.sum_le_sum; intro i _; exact hlen i
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h2 : (r : ℝ) ≤ L * (r * (Real.log (1 + 1 / (r : ℝ)) + 1 / ((n : ℝ) - 1))) := by
    calc (r : ℝ) ≤ _ := h1
      _ ≤ _ := hre
      _ = _ := e
      _ ≤ _ := mul_le_mul_of_nonneg_left hhar hL.le
  have h3 : (r : ℝ) * 1 ≤ r * (L * (Real.log (1 + 1 / (r : ℝ)) + 1 / ((n : ℝ) - 1))) := by
    linarith [show L * (r * (Real.log (1 + 1 / (r : ℝ)) + 1 / ((n : ℝ) - 1))) =
      r * (L * (Real.log (1 + 1 / (r : ℝ)) + 1 / ((n : ℝ) - 1))) by ring]
  exact le_of_mul_le_mul_left h3 hr'

end E1221W3

theorem OMA.solution : type_of% @Erdos1221.erdos_1221.variants.bigLambda_ge := by
  intro r hr
  unfold bigLambda
  apply le_iInf₂
  intro a ha
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx1, hx2⟩ := exists_between hcon
  have hxtop : x ≠ ⊤ := ne_top_of_lt hx2
  set L := x.toReal
  have hxL : x = ENNReal.ofReal L := (ENNReal.ofReal_toReal hxtop).symm
  rw [hxL] at hx1 hx2
  have hL : 0 < L := by
    have := lt_of_le_of_lt zero_le hx1
    exact ENNReal.ofReal_pos.mp this
  have hLc : L < 1 / Real.log (1 + 1 / (r : ℝ)) := (ENNReal.ofReal_lt_ofReal_iff'.mp hx2).1
  have hev := Filter.eventually_lt_of_limsup_lt hx1
  rw [Filter.eventually_atTop] at hev
  obtain ⟨n0, hn0⟩ := hev
  have hM : ∀ N, n0 ≤ N → (N : ℝ) * maxSpan a N r < L := fun N hN =>
    (ENNReal.ofReal_lt_ofReal_iff hL).mp (hn0 N hN)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogpos : 0 < Real.log (1 + 1 / (r : ℝ)) := by
    apply Real.log_pos; have := one_div_pos.mpr hr0; linarith
  have hgap : 0 < 1 - L * Real.log (1 + 1 / (r : ℝ)) := by
    rw [lt_div_iff₀ hlogpos] at hLc; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (L / (1 - L * Real.log (1 + 1 / (r : ℝ))))
  obtain ⟨n, hn⟩ : ∃ n, n = max (max n0 2) (m + 2) := ⟨_, rfl⟩
  have hn2 : 2 ≤ n := by omega
  have hnn0 : n0 ≤ n := by omega
  have hnm : m + 2 ≤ n := by omega
  have key := E1221W3.main a ha hr hL hM hn2 hnn0
  have hn1 : (m : ℝ) + 1 ≤ (n : ℝ) - 1 := by
    have : ((m + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
    rw [Nat.cast_add] at this
    norm_num at this
    linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h5 : L * (1 / ((n : ℝ) - 1)) <
      1 - L * Real.log (1 + 1 / (r : ℝ)) := by
    rw [mul_one_div, div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hgap] at hm
    nlinarith [mul_le_mul_of_nonneg_left hn1 hgap.le]
  rw [mul_add] at key
  linarith
