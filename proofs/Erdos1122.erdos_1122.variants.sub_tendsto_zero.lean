import FormalConjectures.ErdosProblems.«1122»

/-!
# Erdős Problem 1122: vanishing differences

The difference hypothesis implies complete additivity. Binary logarithm estimates
then determine the function on powers of every positive integer.
-/

open Filter
open scoped BigOperators Topology

-- A fixed translation changes f by an amount tending to zero.
lemma OMA.fixedShift (f : ℕ → ℝ)
    (hdiff : Tendsto (fun n ↦ f (n + 1) - f n) atTop (𝓝 0)) (r : ℕ) :
    Tendsto (fun n ↦ f (n + r) - f n) atTop (𝓝 0) := by
  induction r with
  | zero =>
    simp only [Nat.add_zero, sub_self]
    exact tendsto_const_nhds
  | succ r ih =>
    have htop : Tendsto (fun n : ℕ ↦ n + r) atTop atTop :=
      tendsto_atTop_atTop.2 fun B ↦ ⟨B, fun n hn ↦ by omega⟩
    have hsum : Tendsto (fun n : ℕ ↦ (f (n + r + 1) - f (n + r)) +
        (f (n + r) - f n)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, add_zero] using (hdiff.comp htop).add ih
    refine hsum.congr fun n ↦ ?_
    change (f (n + r + 1) - f (n + r)) + (f (n + r) - f n) = f (n + r + 1) - f n
    ring

-- Comparing nearby products lets us remove the coprimality hypothesis.
lemma OMA.completeAdditivity (f : ℕ → ℝ)
    (hf : ∀ a > 0, ∀ b > 0, a.Coprime b → f (a * b) = f a + f b)
    (hdiff : Tendsto (fun n ↦ f (n + 1) - f n) atTop (𝓝 0))
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : f (a * b) = f a + f b := by
  let n : ℕ → ℕ := fun j ↦ 1 + (a * b) * j
  let r : ℕ := a * b + 1 - b
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have hn (j : ℕ) : 0 < n j := by dsimp [n]; omega
  have hr : r + b = a * b + 1 := by
    exact Nat.sub_add_cancel (Nat.le_succ_of_le (Nat.le_mul_of_pos_left b ha))
  have hnear (j : ℕ) : b * n j + r = 1 + a * (b * (b * j + 1)) := by
    calc
      b * n j + r = b + b * ((a * b) * j) + r := by simp [n, Nat.mul_add]
      _ = r + b + b * ((a * b) * j) := by ac_rfl
      _ = 1 + a * (b * (b * j + 1)) := by rw [hr]; ring
  have habn (j : ℕ) : f ((a * b) * n j) = f (a * b) + f (n j) :=
    hf (a * b) hab (n j) (hn j) (by simp [n])
  have hbn (j : ℕ) : f (b * n j) = f b + f (n j) := by
    apply hf b hb (n j) (hn j)
    change b.Coprime (1 + (a * b) * j)
    rw [show (a * b) * j = b * (a * j) by ac_rfl]
    simp
  have han (j : ℕ) : f (a * (b * n j + r)) = f a + f (b * n j + r) := by
    rw [hnear]
    exact hf a ha _ (by omega) (by simp)
  have hnle (j : ℕ) : j ≤ n j :=
    (Nat.le_mul_of_pos_left j hab).trans (by dsimp [n]; omega)
  have htop (m : ℕ) (hm : 0 < m) : Tendsto (fun j ↦ m * n j) atTop atTop :=
    tendsto_atTop_atTop.2 fun B ↦ ⟨B, fun j hj ↦
      hj.trans ((hnle j).trans (Nat.le_mul_of_pos_left (n j) hm))⟩
  have hfirst : Tendsto (fun j ↦ f (a * (b * n j + r)) - f ((a * b) * n j)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.mul_add, Nat.mul_assoc] using
      (OMA.fixedShift f hdiff (a * r)).comp (htop (a * b) hab)
  have hsecond := (OMA.fixedShift f hdiff r).comp (htop b hb)
  have hconstant : Tendsto (fun _ : ℕ ↦ f a + f b - f (a * b)) atTop (𝓝 0) := by
    have h := (hfirst.sub hsecond)
    rw [sub_self] at h
    refine h.congr fun j ↦ ?_
    simp only [Function.comp_apply, han, habn, hbn]
    ring
  have heq := tendsto_nhds_unique tendsto_const_nhds hconstant
  linarith

-- Each binary digit contributes at most ε to the error after finitely many initial values.
lemma OMA.binaryEstimate (f : ℕ → ℝ)
    (hf : ∀ a b : ℕ, 0 < a → 0 < b → f (a * b) = f a + f b)
    (hdiff : Tendsto (fun n ↦ f (n + 1) - f n) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, |f n - f 2 * (Nat.log 2 n : ℝ)| ≤ C + ε * (Nat.log 2 n : ℝ) := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hdiff ε hε)
  let C : ℝ := ∑ n ∈ Finset.range (T + 2), |f n - f 2 * (Nat.log 2 n : ℝ)|
  refine ⟨C, fun n ↦ ?_⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < T + 2
    · have hterm : |f n - f 2 * (Nat.log 2 n : ℝ)| ≤ C :=
        Finset.single_le_sum (f := fun m ↦ |f m - f 2 * (Nat.log 2 m : ℝ)|)
          (fun m _ ↦ abs_nonneg _) (Finset.mem_range.2 hn)
      exact hterm.trans (le_add_of_nonneg_right (by positivity))
    · let q := n / 2
      have hq : 0 < q := by dsimp [q]; omega
      have hq_lt : q < n := Nat.div_lt_self (by omega) (by decide)
      have hrem : n = 2 * q ∨ n = 2 * q + 1 := by dsimp [q]; omega
      have herr : |f n - f (2 * q)| ≤ ε := by
        rcases hrem with he | ho
        · rw [he, sub_self, abs_zero]
          exact hε.le
        · have hbig : T ≤ 2 * q := by omega
          have hstep := hT _ hbig
          rw [Real.dist_eq, sub_zero] at hstep
          calc
            |f n - f (2 * q)| = |f (2 * q + 1) - f (2 * q)| := by rw [← ho]
            _ ≤ ε := hstep.le
      have hlog : Nat.log 2 n = Nat.log 2 q + 1 :=
        Nat.log_of_one_lt_of_le (by decide) (by omega)
      have hprod := hf 2 q (by decide) hq
      calc
        |f n - f 2 * (Nat.log 2 n : ℝ)| =
            |(f n - f (2 * q)) + (f q - f 2 * (Nat.log 2 q : ℝ))| := by
          rw [hlog, Nat.cast_add, Nat.cast_one, hprod]
          congr 1
          ring
        _ ≤ |f n - f (2 * q)| + |f q - f 2 * (Nat.log 2 q : ℝ)| := abs_add_le _ _
        _ ≤ ε + (C + ε * (Nat.log 2 q : ℝ)) := add_le_add herr (ih q hq_lt)
        _ = C + ε * (Nat.log 2 n : ℝ) := by rw [hlog, Nat.cast_add, Nat.cast_one]; ring

lemma OMA.binaryLogBounds (n : ℕ) (hn : 0 < n) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 ∧
      Real.log n / Real.log 2 < (Nat.log 2 n : ℝ) + 1 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · apply (le_div_iff₀ hlog).2
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  · apply (div_lt_iff₀ hlog).2
    have hlt : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using
      Real.log_lt_log (by exact_mod_cast hn) hlt

theorem OMA.solution : type_of% @Erdos1122.erdos_1122.variants.sub_tendsto_zero := by
  intro f hf hdiff
  have hadd (a b : ℕ) (ha : 0 < a) (hb : 0 < b) := OMA.completeAdditivity f hf hdiff a b ha hb
  have hf1 : f 1 = 0 := by
    have h := hadd 1 1 (by decide) (by decide)
    norm_num only [one_mul] at h
    linarith
  refine ⟨f 2 / Real.log 2, fun m hm ↦ ?_⟩
  by_cases hm1 : m = 1
  · simp [hm1, hf1]
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let α := Real.log (m : ℝ) / Real.log 2
  have hα : 0 < α := by
    apply div_pos (Real.log_pos ?_) hlogtwo
    exact_mod_cast (show 1 < m by omega)
  rw [show f 2 / Real.log 2 * Real.log (m : ℝ) = f 2 * α by dsimp [α]; ring]
  by_contra hne
  let δ := |f m - f 2 * α|
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  let ε := (δ / 2) / α
  have hε : 0 < ε := div_pos (by positivity) hα
  have hεα : ε * α = δ / 2 := div_mul_cancel₀ _ hα.ne'
  obtain ⟨C, hC⟩ := OMA.binaryEstimate f hadd hdiff ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt ((C + |f 2|) / (δ / 2))
  have hklarge := (div_lt_iff₀ (by positivity : 0 < δ / 2)).1 hk
  let N := m ^ k
  have hN : 0 < N := pow_pos hm k
  have hpow (exponent : ℕ) : f (m ^ exponent) = (exponent : ℝ) * f m := by
    induction exponent with
    | zero => simp [hf1]
    | succ exponent ih =>
      rw [pow_succ, hadd (m ^ exponent) m (pow_pos hm exponent) hm, ih, Nat.cast_succ]
      ring
  have hlogN : Real.log (N : ℝ) / Real.log 2 = (k : ℝ) * α := by
    dsimp [N, α]
    rw [Nat.cast_pow, Real.log_pow]
    ring
  obtain ⟨hlo, hhi⟩ := OMA.binaryLogBounds N hN
  rw [hlogN] at hlo hhi
  have hgap : |(Nat.log 2 N : ℝ) - (k : ℝ) * α| ≤ 1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hscaled : |f 2 * ((Nat.log 2 N : ℝ) - (k : ℝ) * α)| ≤ |f 2| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hgap (abs_nonneg (f 2))
  have hbound : |(k : ℝ) * (f m - f 2 * α)| ≤ C + |f 2| + (k : ℝ) * (δ / 2) := by
    calc
      |(k : ℝ) * (f m - f 2 * α)| =
          |(f N - f 2 * (Nat.log 2 N : ℝ)) + f 2 * ((Nat.log 2 N : ℝ) - (k : ℝ) * α)| := by
        rw [show f N = (k : ℝ) * f m from hpow k]
        congr 1
        ring
      _ ≤ |f N - f 2 * (Nat.log 2 N : ℝ)| +
            |f 2 * ((Nat.log 2 N : ℝ) - (k : ℝ) * α)| := abs_add_le _ _
      _ ≤ (C + ε * (Nat.log 2 N : ℝ)) + |f 2| := add_le_add (hC N) hscaled
      _ ≤ (C + ε * ((k : ℝ) * α)) + |f 2| := by gcongr
      _ = C + |f 2| + (k : ℝ) * (δ / 2) := by rw [← hεα]; ring
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)] at hbound
  change (k : ℝ) * δ ≤ _ at hbound
  nlinarith only [hbound, hklarge]
