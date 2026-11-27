import FormalConjectures.ErdosProblems.«1195»

-- Problem: Erdős Problem 1195 — exists set
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1195.lean:96 (declaration Erdos1195.erdos_1195.variants.exists_set)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open MeasureTheory

namespace OMA

noncomputable def L (x : ℝ) : ℝ := Real.logb 2 x

def F1 (θ q M : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ M → ∃ k : ℤ, |(θ : ℝ) * L m - k| < 1 / (q : ℝ)

lemma dirichlet (M : ℕ) : ∀ T : ℕ, 0 < T → ∀ q : ℕ, 0 < q →
    ∃ θ : ℕ, 0 < θ ∧ T ∣ θ ∧ F1 θ q M := by
  induction M with
  | zero =>
    intro T hT q hq
    refine ⟨T, hT, dvd_rfl, ?_⟩
    intro m h1 h2
    omega
  | succ M ih =>
    intro T hT q hq
    obtain ⟨θ', hθ', hdvd, hF⟩ := ih T hT (q * q) (Nat.mul_pos hq hq)
    obtain ⟨t, ht0, htq, ht⟩ :=
      Real.exists_nat_abs_mul_sub_round_le ((θ' : ℝ) * L ((M + 1 : ℕ) : ℝ)) hq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have htR : (0 : ℝ) < t := by exact_mod_cast ht0
    have htqR : (t : ℝ) ≤ q := by exact_mod_cast htq
    refine ⟨t * θ', Nat.mul_pos ht0 hθ', Dvd.dvd.mul_left hdvd t, ?_⟩
    intro m h1 h2
    rcases Nat.lt_or_ge M m with h | h
    · have hm : m = M + 1 := by omega
      subst hm
      refine ⟨round ((t : ℝ) * ((θ' : ℝ) * L ((M + 1 : ℕ) : ℝ))), ?_⟩
      have h3 : (1 : ℝ) / (q + 1) < 1 / q := by
        apply one_div_lt_one_div_of_lt hqR
        linarith
      have h4 : (((t * θ' : ℕ) : ℝ)) * L ((M + 1 : ℕ) : ℝ) =
          (t : ℝ) * ((θ' : ℝ) * L ((M + 1 : ℕ) : ℝ)) := by
        push_cast
        ring
      rw [h4]
      exact lt_of_le_of_lt ht h3
    · obtain ⟨k, hk⟩ := hF m h1 h
      refine ⟨t * k, ?_⟩
      have h4 : (((t * θ' : ℕ) : ℝ)) * L m - ((t * k : ℤ) : ℝ) =
          (t : ℝ) * ((θ' : ℝ) * L m - k) := by
        push_cast
        ring
      rw [h4, abs_mul, abs_of_pos htR]
      have h5 : ((1 : ℝ) / ((q * q : ℕ) : ℝ)) = 1 / q / q := by
        push_cast
        field_simp
      rw [h5] at hk
      calc (t : ℝ) * |(θ' : ℝ) * L m - k| ≤ q * |(θ' : ℝ) * L m - k| :=
            mul_le_mul_of_nonneg_right htqR (abs_nonneg _)
        _ < q * (1 / q / q) := mul_lt_mul_of_pos_left hk hqR
        _ = 1 / q := by field_simp

def Dset (θ q i : ℕ) : Set ℝ :=
  {x | 0 < x ∧ ⌊L x⌋ = (i : ℤ) ∧ ⌊((q : ℝ) * θ) * L x⌋ = (q : ℤ) * ⌊(θ : ℝ) * L x⌋}

def Bset (θ q : ℕ) : Set ℝ :=
  {x | 0 < x ∧ Int.fract ((θ : ℝ) * L x + 1 / (q : ℝ)) < 3 / (q : ℝ)}

lemma key_d {θ q j : ℕ} (hq : 3 ≤ q) (hF : F1 θ q (2 ^ (j + 1)))
    {x : ℝ} (hx : 1 ≤ x) {m : ℕ} (hm : 1 ≤ m) (hy : (m : ℝ) * x ∈ Dset θ q j) :
    x ∈ Bset θ q := by
  obtain ⟨hy0, hy1, hy2⟩ := hy
  have hx0 : 0 < x := by linarith
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  -- m ≤ 2^(j+1)
  have hm2 : m ≤ 2 ^ (j + 1) := by
    have h1 : L ((m : ℝ) * x) < (j : ℝ) + 1 := by
      have := Int.lt_floor_add_one (L ((m : ℝ) * x))
      rw [hy1] at this
      exact_mod_cast this
    have h2 : (m : ℝ) * x < (2 : ℝ) ^ ((j : ℝ) + 1) := by
      unfold L at h1
      exact (Real.logb_lt_iff_lt_rpow (by norm_num) hy0).1 h1
    have h3 : (m : ℝ) < (2 : ℝ) ^ (j + 1) := by
      have h4 : (2 : ℝ) ^ ((j : ℝ) + 1) = (2 : ℝ) ^ (j + 1) := by
        rw [← Real.rpow_natCast]
        push_cast
        rfl
      rw [h4] at h2
      nlinarith
    have h5 : m < 2 ^ (j + 1) := by exact_mod_cast h3
    omega
  obtain ⟨k, hk⟩ := hF m hm hm2
  have hLmul : L ((m : ℝ) * x) = L m + L x := by
    unfold L
    exact Real.logb_mul (by positivity) (by positivity)
  set n := ⌊(θ : ℝ) * L ((m : ℝ) * x)⌋ with hn
  have hf0 : (n : ℝ) ≤ (θ : ℝ) * L ((m : ℝ) * x) := Int.floor_le _
  have hf1 : (θ : ℝ) * L ((m : ℝ) * x) - n < 1 / q := by
    have h1 := Int.lt_floor_add_one (((q : ℝ) * θ) * L ((m : ℝ) * x))
    rw [hy2] at h1
    push_cast at h1
    rw [lt_div_iff₀ hq0] at *
    nlinarith
  rw [abs_lt] at hk
  refine ⟨hx0, ?_⟩
  have hfr : Int.fract ((θ : ℝ) * L x + 1 / (q : ℝ)) =
      (θ : ℝ) * L x + 1 / (q : ℝ) - ((n - k : ℤ) : ℝ) := by
    rw [Int.fract_eq_iff]
    have h3q : (3 : ℝ) / q ≤ 1 := by
      rw [div_le_one hq0]
      exact hqR
    have e3 : (3 : ℝ) / q = 1 / q + 1 / q + 1 / q := by ring
    refine ⟨?_, ?_, ⟨n - k, by push_cast; ring⟩⟩
    · push_cast
      rw [hLmul] at hf0 hf1
      nlinarith [hk.1, hk.2]
    · push_cast
      rw [hLmul] at hf0 hf1
      nlinarith [hk.1, hk.2]
  rw [hfr]
  push_cast
  rw [hLmul] at hf0 hf1
  have e3 : (3 : ℝ) / q = 1 / q + 1 / q + 1 / q := by ring
  rw [e3]
  nlinarith [hk.1, hk.2]

lemma hL : Measurable L := by
  unfold L Real.logb
  exact Real.measurable_log.div_const _

def atom (T : ℕ) (a : ℤ) : Set ℝ := {x | 0 < x ∧ ⌊(T : ℝ) * L x⌋ = a}

lemma meas_atom (T : ℕ) (a : ℤ) : MeasurableSet (atom T a) :=
  (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_eq_fun (hL.const_mul _).floor measurable_const)

lemma meas_D (θ q i : ℕ) : MeasurableSet (Dset θ q i) :=
  (measurableSet_lt measurable_const measurable_id).inter
    ((measurableSet_eq_fun hL.floor measurable_const).inter
      (measurableSet_eq_fun (hL.const_mul _).floor
        (measurable_from_top.comp (hL.const_mul _).floor)))

lemma meas_B (θ q : ℕ) : MeasurableSet (Bset θ q) :=
  (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_lt (measurable_fract.comp ((hL.const_mul _).add_const _)) measurable_const)

lemma cmp (T : ℕ) (X Y : Set ℝ) (hY : MeasurableSet Y) (hX : X ⊆ Set.Ioi 0) (c : ENNReal)
    (h : ∀ a : ℤ, volume (X ∩ atom T a) ≤ c * volume (Y ∩ atom T a)) :
    volume X ≤ c * volume Y := by
  have hXU : X ⊆ ⋃ a, X ∩ atom T a :=
    fun x hx => Set.mem_iUnion.2 ⟨⌊(T : ℝ) * L x⌋, hx, hX hx, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun a => Y ∩ atom T a) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    exact hab (hxa.2.2.symm.trans hxb.2.2)
  calc volume X ≤ volume (⋃ a, X ∩ atom T a) := measure_mono hXU
    _ ≤ ∑' a, volume (X ∩ atom T a) := measure_iUnion_le _
    _ ≤ ∑' a, c * volume (Y ∩ atom T a) := ENNReal.tsum_le_tsum h
    _ = c * ∑' a, volume (Y ∩ atom T a) := ENNReal.tsum_mul_left
    _ = c * volume (⋃ a, Y ∩ atom T a) := by
        rw [measure_iUnion hdisj (fun a => hY.inter (meas_atom T a))]
    _ ≤ c * volume Y := by
        gcongr
        exact Set.iUnion_subset fun a => Set.inter_subset_left

lemma pw (u w : ℝ) (k : ℕ) : (2 : ℝ) ^ (u + k * w) = 2 ^ u * ((2 : ℝ) ^ w) ^ k := by
  rw [Real.rpow_add two_pos, mul_comm (k : ℝ) w, Real.rpow_mul_natCast (by norm_num)]

lemma volE (u w : ℝ) (k l : ℕ) :
    volume {x | 0 < x ∧ u + k * w ≤ L x ∧ L x < u + l * w} =
      ENNReal.ofReal (2 ^ u * ((2 : ℝ) ^ w) ^ l - 2 ^ u * ((2 : ℝ) ^ w) ^ k) := by
  have : {x | 0 < x ∧ u + k * w ≤ L x ∧ L x < u + l * w} =
      Set.Ico ((2 : ℝ) ^ (u + k * w)) ((2 : ℝ) ^ (u + l * w)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨h0, h1, h2⟩
      exact ⟨(Real.le_logb_iff_rpow_le (by norm_num) h0).1 h1,
        (Real.logb_lt_iff_lt_rpow (by norm_num) h0).1 h2⟩
    · rintro ⟨h1, h2⟩
      have h0 : 0 < x := lt_of_lt_of_le (Real.rpow_pos_of_pos two_pos _) h1
      exact ⟨h0, (Real.le_logb_iff_rpow_le (by norm_num) h0).2 h1,
        (Real.logb_lt_iff_lt_rpow (by norm_num) h0).2 h2⟩
  rw [this, Real.volume_Ico, pw, pw]

lemma atom_eq {T q : ℕ} (hT : 0 < T) (hq : 0 < q) (a : ℤ) :
    atom T a = {x | 0 < x ∧ (a : ℝ) / T + (0 : ℕ) * (1 / ((q : ℝ) * T)) ≤ L x ∧
      L x < (a : ℝ) / T + (q : ℕ) * (1 / ((q : ℝ) * T))} := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have e : (a : ℝ) / T + (q : ℕ) * (1 / ((q : ℝ) * T)) = (a + 1) / T := by
    field_simp
  ext x
  simp only [atom, Set.mem_setOf_eq, Nat.cast_zero, zero_mul, add_zero]
  rw [e, Int.floor_eq_iff, div_le_iff₀ hTR, lt_div_iff₀ hTR, mul_comm (L x)]

lemma mu_bounds {T q : ℕ} (hT : 0 < T) (hq : 0 < q) :
    1 ≤ (2 : ℝ) ^ (1 / ((q : ℝ) * T)) ∧ ((2 : ℝ) ^ (1 / ((q : ℝ) * T))) ^ q ≤ 2 := by
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · apply Real.one_le_rpow (by norm_num)
    positivity
  · rw [← Real.rpow_mul_natCast (by norm_num)]
    have e : 1 / ((q : ℝ) * T) * q = 1 / T := by field_simp
    rw [e]
    calc (2 : ℝ) ^ (1 / (T : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          rw [div_le_one (by linarith)]
          exact hTR
      _ = 2 := Real.rpow_one 2

lemma geo (μ : ℝ) (hμ : 1 ≤ μ) (n : ℕ) : μ ^ n - 1 ≤ n * μ ^ n * (μ - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (1 : ℝ) ≤ μ ^ n := one_le_pow₀ hμ
    have h2 : (0 : ℝ) ≤ (n : ℝ) * μ ^ n * (μ - 1) := by
      apply mul_nonneg (by positivity)
      linarith
    push_cast
    rw [pow_succ]
    nlinarith [mul_nonneg h2 (by linarith : (0 : ℝ) ≤ μ - 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ μ ^ n) (by linarith : (0 : ℝ) ≤ μ - 1),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ μ ^ n) (by linarith : (0 : ℝ) ≤ μ - 1))
        (by linarith : (0 : ℝ) ≤ μ - 1)]

lemma atomB {T q : ℕ} (hT : 0 < T) (hq : 3 ≤ q) (a : ℤ) :
    volume (Bset T q ∩ atom T a) ≤ ENNReal.ofReal (5 / (q : ℝ)) * volume (atom T a) := by
  have hq0 : 0 < q := by omega
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  obtain ⟨p, hp⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have hpR : (q : ℝ) = p + 1 := by rw [hp]; push_cast; rfl
  obtain ⟨hμ1, hμ2⟩ := mu_bounds hT hq0
  set w : ℝ := 1 / ((q : ℝ) * T) with hw
  set u : ℝ := (a : ℝ) / T with hu
  set μ : ℝ := (2 : ℝ) ^ w with hμ
  set c : ℝ := (2 : ℝ) ^ u with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos two_pos _
  have hTu : (T : ℝ) * u = a := by rw [hu]; field_simp
  have hTw : (T : ℝ) * w = 1 / q := by rw [hw]; field_simp
  have hsub : Bset T q ∩ atom T a ⊆
      {x | 0 < x ∧ u + (0 : ℕ) * w ≤ L x ∧ L x < u + (2 : ℕ) * w} ∪
      {x | 0 < x ∧ u + (p : ℕ) * w ≤ L x ∧ L x < u + (q : ℕ) * w} := by
    rintro x ⟨⟨hx0, hB⟩, hA⟩
    rw [atom_eq hT hq0] at hA
    obtain ⟨-, h1, h2⟩ := hA
    by_cases h : L x < u + (2 : ℕ) * w
    · left
      exact ⟨hx0, h1, h⟩
    · right
      refine ⟨hx0, ?_, h2⟩
      by_contra hcon
      rw [not_lt] at h
      rw [not_le] at hcon
      have k1 : (T : ℝ) * (u + (2 : ℕ) * w) ≤ T * L x := mul_le_mul_of_nonneg_left h hTR.le
      have k2 : (T : ℝ) * L x < T * (u + (p : ℕ) * w) := mul_lt_mul_of_pos_left hcon hTR
      have k3 : (a : ℝ) + 2 / q ≤ T * L x := by
        have : (T : ℝ) * (u + (2 : ℕ) * w) = a + 2 / q := by
          rw [mul_add, hTu, mul_left_comm, hTw]; push_cast; ring
        rw [this] at k1
        exact k1
      have k4 : (T : ℝ) * L x < a + p / q := by
        have : (T : ℝ) * (u + (p : ℕ) * w) = a + p / q := by
          rw [mul_add, hTu, mul_left_comm, hTw]; ring
        rw [this] at k2
        exact k2
      have hfr : Int.fract ((T : ℝ) * L x + 1 / (q : ℝ)) = (T : ℝ) * L x + 1 / (q : ℝ) - a := by
        rw [Int.fract_eq_iff]
        have e1 : (p : ℝ) / q + 1 / q = 1 := by rw [hpR]; field_simp
        have e2 : (0 : ℝ) < 2 / q := by positivity
        have e3 : (0 : ℝ) < 1 / q := by positivity
        refine ⟨by linarith, by linarith, ⟨a, by ring⟩⟩
      rw [hfr] at hB
      have e3 : (3 : ℝ) / q = 2 / q + 1 / q := by ring
      linarith
  have hp1 : (1 : ℝ) ≤ μ ^ p := one_le_pow₀ hμ1
  have hμq : μ ^ q = μ ^ p * μ := by rw [hp, pow_succ]
  have hbern : 1 + (q : ℝ) * (μ - 1) ≤ μ ^ q := by
    have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ μ - 1) q
    simpa using this
  have n1 : (0 : ℝ) ≤ c * μ ^ 2 - c * μ ^ 0 := by
    have h2 : (1 : ℝ) ≤ μ ^ 2 := one_le_pow₀ hμ1
    have h3 := mul_le_mul_of_nonneg_left h2 hc0.le
    simp only [pow_zero]
    linarith
  have n2 : (0 : ℝ) ≤ c * μ ^ q - c * μ ^ p := by
    rw [hμq]; nlinarith
  have I1 : c * μ ^ 2 - c * μ ^ 0 + (c * μ ^ q - c * μ ^ p) ≤
      5 / (q : ℝ) * (c * μ ^ q - c * μ ^ 0) := by
    have s1 : c * μ ^ 2 - c * μ ^ 0 + (c * μ ^ q - c * μ ^ p) = c * (μ - 1) * (μ + 1 + μ ^ p) := by
      rw [hμq]; ring
    have s2 : c * (μ - 1) * (μ + 1 + μ ^ p) ≤ c * (μ - 1) * 5 := by
      apply mul_le_mul_of_nonneg_left
      · rw [hμq] at hμ2
        nlinarith
      · exact mul_nonneg hc0.le (by linarith)
    have s3 : c * (μ - 1) * 5 = c * (5 / (q : ℝ)) * ((q : ℝ) * (μ - 1)) := by field_simp
    have s4 : c * (5 / (q : ℝ)) * ((q : ℝ) * (μ - 1)) ≤ c * (5 / (q : ℝ)) * (μ ^ q - 1) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      positivity
    rw [s1]
    calc c * (μ - 1) * (μ + 1 + μ ^ p) ≤ c * (5 / (q : ℝ)) * (μ ^ q - 1) := by linarith
      _ = 5 / (q : ℝ) * (c * μ ^ q - c * μ ^ 0) := by ring
  calc volume (Bset T q ∩ atom T a)
      ≤ volume ({x | 0 < x ∧ u + (0 : ℕ) * w ≤ L x ∧ L x < u + (2 : ℕ) * w} ∪
          {x | 0 < x ∧ u + (p : ℕ) * w ≤ L x ∧ L x < u + (q : ℕ) * w}) := measure_mono hsub
    _ ≤ volume {x | 0 < x ∧ u + (0 : ℕ) * w ≤ L x ∧ L x < u + (2 : ℕ) * w} +
          volume {x | 0 < x ∧ u + (p : ℕ) * w ≤ L x ∧ L x < u + (q : ℕ) * w} :=
        measure_union_le _ _
    _ = ENNReal.ofReal (c * μ ^ 2 - c * μ ^ 0 + (c * μ ^ q - c * μ ^ p)) := by
        rw [volE, volE, ENNReal.ofReal_add n1 n2]
    _ ≤ ENNReal.ofReal (5 / (q : ℝ) * (c * μ ^ q - c * μ ^ 0)) := ENNReal.ofReal_le_ofReal I1
    _ = ENNReal.ofReal (5 / (q : ℝ)) * volume (atom T a) := by
        rw [ENNReal.ofReal_mul (by positivity), atom_eq hT hq0 a, volE]

lemma floors {T K : ℕ} (hK : 0 < K) {x : ℝ} {a : ℤ} (r : ℝ)
    (hr : r * K = (T : ℝ) * L x) (hxa : ⌊(T : ℝ) * L x⌋ = a) : ⌊r⌋ = a / (K : ℤ) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have : r = (T : ℝ) * L x / (K : ℕ) := by
    rw [← hr]; field_simp
  rw [this, Int.floor_div_natCast, hxa]

lemma lem_c {θ q i T Q : ℕ} (hθ : 0 < θ) (hq : 0 < q) (hT : 0 < T) (hQ : 3 ≤ Q)
    (hdvd : θ * q ∣ T) :
    volume (Dset θ q i ∩ Bset T Q) ≤ ENNReal.ofReal (5 / (Q : ℝ)) * volume (Dset θ q i) := by
  obtain ⟨K, hK⟩ := hdvd
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; omega
    · exact h
  have hTR : (T : ℝ) = θ * q * K := by rw [hK]; push_cast; ring
  have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK0
  apply cmp T _ _ (meas_D θ q i) (fun x hx => hx.1.1)
  intro a
  have fl : ∀ x : ℝ, ⌊(T : ℝ) * L x⌋ = a →
      ⌊L x⌋ = a / (T : ℤ) ∧ ⌊((q : ℝ) * θ) * L x⌋ = a / (K : ℤ) ∧
        ⌊(θ : ℝ) * L x⌋ = a / ((q * K : ℕ) : ℤ) := by
    intro x hxa
    refine ⟨floors hT _ (by ring) hxa, floors hK0 _ (by rw [hTR]; ring) hxa,
      floors (Nat.mul_pos hq hK0) _ (by rw [hTR]; push_cast; ring) hxa⟩
  by_cases hP : a / (T : ℤ) = i ∧ a / (K : ℤ) = (q : ℤ) * (a / ((q * K : ℕ) : ℤ))
  · have hsub : atom T a ⊆ Dset θ q i := by
      rintro x ⟨hx0, hxa⟩
      obtain ⟨f1, f2, f3⟩ := fl x hxa
      exact ⟨hx0, by rw [f1]; exact hP.1, by rw [f2, f3]; exact hP.2⟩
    calc volume (Dset θ q i ∩ Bset T Q ∩ atom T a) ≤ volume (Bset T Q ∩ atom T a) :=
          measure_mono (fun x hx => ⟨hx.1.2, hx.2⟩)
      _ ≤ ENNReal.ofReal (5 / (Q : ℝ)) * volume (atom T a) := atomB hT hQ a
      _ = ENNReal.ofReal (5 / (Q : ℝ)) * volume (Dset θ q i ∩ atom T a) := by
          rw [Set.inter_eq_right.2 hsub]
  · have hemp : Dset θ q i ∩ Bset T Q ∩ atom T a = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨⟨hx0, d1, d2⟩, -⟩, -, hxa⟩
      obtain ⟨f1, f2, f3⟩ := fl x hxa
      exact hP ⟨by rw [← f1]; exact d1, by rw [← f2, ← f3]; exact d2⟩
    rw [hemp]
    simp

lemma lem_b {θ q i : ℕ} (hθ : 0 < θ) (hq : 0 < q) :
    ENNReal.ofReal ((2 : ℝ) ^ i) ≤ ENNReal.ofReal (2 * (q : ℝ)) * volume (Dset θ q i) := by
  have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hX : volume {x : ℝ | 0 < x ∧ ⌊L x⌋ = (i : ℤ)} = ENNReal.ofReal ((2 : ℝ) ^ i) := by
    have : {x : ℝ | 0 < x ∧ ⌊L x⌋ = (i : ℤ)} =
        {x | 0 < x ∧ (i : ℝ) + (0 : ℕ) * 1 ≤ L x ∧ L x < (i : ℝ) + (1 : ℕ) * 1} := by
      ext x
      simp only [Set.mem_setOf_eq, Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul]
      rw [Int.floor_eq_iff]
      simp
    rw [this, volE]
    congr 1
    rw [Real.rpow_natCast]
    simp
    ring
  rw [← hX]
  apply cmp θ _ _ (meas_D θ q i) (fun x hx => hx.1)
  intro a
  by_cases ha : a / (θ : ℤ) = i
  · obtain ⟨hμ1, hμ2⟩ := mu_bounds hθ hq
    set w : ℝ := 1 / ((q : ℝ) * θ) with hw
    set u : ℝ := (a : ℝ) / θ with hu
    set μ : ℝ := (2 : ℝ) ^ w with hμ
    set c : ℝ := (2 : ℝ) ^ u with hc
    have hc0 : 0 < c := Real.rpow_pos_of_pos two_pos _
    have hTu : (θ : ℝ) * u = a := by rw [hu]; field_simp
    have hTw : (θ : ℝ) * w = 1 / q := by rw [hw]; field_simp
    have hsub : {x | 0 < x ∧ u + (0 : ℕ) * w ≤ L x ∧ L x < u + (1 : ℕ) * w} ⊆
        Dset θ q i ∩ atom θ a := by
      rintro x ⟨hx0, h1, h2⟩
      have k1 : (θ : ℝ) * (u + (0 : ℕ) * w) ≤ θ * L x := mul_le_mul_of_nonneg_left h1 hθR.le
      have k2 : (θ : ℝ) * L x < θ * (u + (1 : ℕ) * w) := mul_lt_mul_of_pos_left h2 hθR
      have k3 : (a : ℝ) ≤ θ * L x := by
        have : (θ : ℝ) * (u + (0 : ℕ) * w) = a := by
          rw [mul_add, hTu]; simp
        rw [this] at k1
        exact k1
      have k4 : (θ : ℝ) * L x < a + 1 / q := by
        have : (θ : ℝ) * (u + (1 : ℕ) * w) = a + 1 / q := by
          rw [mul_add, hTu, mul_left_comm, hTw]; simp
        rw [this] at k2
        exact k2
      have e3 : (1 : ℝ) / q ≤ 1 := by
        rw [div_le_one hqR]
        exact_mod_cast hq
      have hxa : ⌊(θ : ℝ) * L x⌋ = a := by
        rw [Int.floor_eq_iff]
        exact ⟨k3, by linarith⟩
      refine ⟨⟨hx0, ?_, ?_⟩, hx0, hxa⟩
      · rw [floors hθ (L x) (by ring) hxa]
        exact ha
      · rw [hxa, Int.floor_eq_iff]
        push_cast
        have e4 : (q : ℝ) * (1 / q) = 1 := by field_simp
        constructor
        · nlinarith
        · nlinarith
    have hg := geo μ hμ1 q
    have I2 : c * μ ^ q - c * μ ^ 0 ≤ 2 * (q : ℝ) * (c * μ ^ 1 - c * μ ^ 0) := by
      have s1 : (q : ℝ) * μ ^ q * (μ - 1) ≤ (q : ℝ) * 2 * (μ - 1) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left hμ2 hqR.le
      have s2 : c * (μ ^ q - 1) ≤ c * ((q : ℝ) * 2 * (μ - 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0.le
      calc c * μ ^ q - c * μ ^ 0 = c * (μ ^ q - 1) := by ring
        _ ≤ c * ((q : ℝ) * 2 * (μ - 1)) := s2
        _ = 2 * (q : ℝ) * (c * μ ^ 1 - c * μ ^ 0) := by ring
    calc volume ({x : ℝ | 0 < x ∧ ⌊L x⌋ = (i : ℤ)} ∩ atom θ a) ≤ volume (atom θ a) :=
          measure_mono Set.inter_subset_right
      _ = ENNReal.ofReal (c * μ ^ q - c * μ ^ 0) := by rw [atom_eq hθ hq a, volE]
      _ ≤ ENNReal.ofReal (2 * (q : ℝ) * (c * μ ^ 1 - c * μ ^ 0)) := ENNReal.ofReal_le_ofReal I2
      _ = ENNReal.ofReal (2 * (q : ℝ)) *
            volume {x | 0 < x ∧ u + (0 : ℕ) * w ≤ L x ∧ L x < u + (1 : ℕ) * w} := by
          rw [ENNReal.ofReal_mul (by positivity), volE]
      _ ≤ ENNReal.ofReal (2 * (q : ℝ)) * volume (Dset θ q i ∩ atom θ a) := by
          gcongr
  · have hemp : {x : ℝ | 0 < x ∧ ⌊L x⌋ = (i : ℤ)} ∩ atom θ a = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨hx0, d1⟩, -, hxa⟩
      apply ha
      rw [← floors hθ (L x) (by ring) hxa]
      exact d1
    rw [hemp]
    simp

def qq (i : ℕ) : ℕ := 2 ^ (i + 4)

lemma qq_pos (i : ℕ) : 0 < qq i := by unfold qq; positivity

lemma qq_three (i : ℕ) : 3 ≤ qq i := by
  have : 2 ^ 4 ≤ 2 ^ (i + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold qq
  omega

lemma dir2 (j T : ℕ) (hT : 0 < T) :
    ∃ θ : ℕ, 0 < θ ∧ T ∣ θ ∧ F1 θ (qq j) (2 ^ (j + 1)) :=
  dirichlet _ T hT _ (qq_pos j)

noncomputable def th : ℕ → ℕ
  | 0 => Classical.choose (dir2 0 1 one_pos)
  | j + 1 => if h : 0 < th j * qq j then Classical.choose (dir2 (j + 1) (th j * qq j) h) else 1

lemma th_pos : ∀ j, 0 < th j := by
  intro j
  cases j with
  | zero =>
    rw [th]
    exact (Classical.choose_spec (dir2 0 1 one_pos)).1
  | succ j =>
    rw [th]
    split_ifs with h
    · exact (Classical.choose_spec (dir2 (j + 1) (th j * qq j) h)).1
    · exact one_pos

lemma th_F1 : ∀ j, F1 (th j) (qq j) (2 ^ (j + 1)) := by
  intro j
  cases j with
  | zero =>
    rw [th]
    exact (Classical.choose_spec (dir2 0 1 one_pos)).2.2
  | succ j =>
    have h : 0 < th j * qq j := Nat.mul_pos (th_pos j) (qq_pos j)
    rw [th, dif_pos h]
    exact (Classical.choose_spec (dir2 (j + 1) (th j * qq j) h)).2.2

lemma th_dvd (j : ℕ) : th j * qq j ∣ th (j + 1) := by
  have h : 0 < th j * qq j := Nat.mul_pos (th_pos j) (qq_pos j)
  rw [th, dif_pos h]
  exact (Classical.choose_spec (dir2 (j + 1) (th j * qq j) h)).2.1

lemma th_dvd_lt {i j : ℕ} (hij : i < j) : th i * qq i ∣ th j := by
  induction j, hij using Nat.le_induction with
  | base => exact th_dvd i
  | succ j _ ih => exact (ih.trans (Dvd.intro _ rfl)).trans (th_dvd j)

def Uset (i : ℕ) : Set ℝ := ⋃ j, ⋃ (_ : i < j), Bset (th j) (qq j)

def Sset (i : ℕ) : Set ℝ := Dset (th i) (qq i) i \ Uset i

lemma meas_S (i : ℕ) : MeasurableSet (Sset i) :=
  (meas_D _ _ _).diff (MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => meas_B _ _)

lemma volX (i : ℕ) :
    volume {x : ℝ | 0 < x ∧ ⌊L x⌋ = (i : ℤ)} = ENNReal.ofReal ((2 : ℝ) ^ i) := by
  have : {x : ℝ | 0 < x ∧ ⌊L x⌋ = (i : ℤ)} =
      {x | 0 < x ∧ (i : ℝ) + (0 : ℕ) * 1 ≤ L x ∧ L x < (i : ℝ) + (1 : ℕ) * 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul]
    rw [Int.floor_eq_iff]
    simp
  rw [this, volE]
  congr 1
  rw [Real.rpow_natCast]
  simp
  ring

lemma sum_eps : ∑' j : ℕ, ENNReal.ofReal (5 / ((qq j : ℕ) : ℝ)) = ENNReal.ofReal (5 / 8) := by
  have hf : (fun j : ℕ => 5 / ((qq j : ℕ) : ℝ)) = fun j : ℕ => 5 / 16 * (1 / 2 : ℝ) ^ j := by
    funext j
    unfold qq
    push_cast
    rw [pow_add, one_div_pow]
    field_simp
    norm_num
  have hs : HasSum (fun j : ℕ => 5 / 16 * (1 / 2 : ℝ) ^ j) (5 / 16 * 2) :=
    hasSum_geometric_two.mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) (by rw [hf]; exact hs.summable),
    hf, hs.tsum_eq]
  norm_num

lemma vol_S (i : ℕ) : ENNReal.ofReal (3 / 256) ≤ volume (Sset i) := by
  set D := Dset (th i) (qq i) i with hD
  have hDfin : volume D ≠ ⊤ := by
    have : volume D ≤ ENNReal.ofReal ((2 : ℝ) ^ i) := by
      rw [← volX i]
      exact measure_mono (fun x hx => ⟨hx.1, hx.2.1⟩)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
  have hSfin : volume (Sset i) ≠ ⊤ :=
    ne_top_of_le_ne_top hDfin (measure_mono Set.diff_subset)
  have hU : volume (D ∩ Uset i) ≤ ENNReal.ofReal (5 / 8) * volume D := by
    calc volume (D ∩ Uset i)
        = volume (⋃ j, D ∩ ⋃ (_ : i < j), Bset (th j) (qq j)) := by
          rw [Uset, Set.inter_iUnion]
      _ ≤ ∑' j, volume (D ∩ ⋃ (_ : i < j), Bset (th j) (qq j)) := measure_iUnion_le _
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (5 / ((qq j : ℕ) : ℝ)) * volume D := by
          apply ENNReal.tsum_le_tsum
          intro j
          by_cases hij : i < j
          · simp only [hij, Set.iUnion_true]
            exact lem_c (th_pos i) (qq_pos i) (th_pos j) (qq_three j) (th_dvd_lt hij)
          · simp [hij]
      _ = ENNReal.ofReal (5 / 8) * volume D := by
          rw [ENNReal.tsum_mul_right, sum_eps]
  have h1 : volume D ≤ volume (Sset i) + volume (D ∩ Uset i) := by
    have : D ⊆ Sset i ∪ (D ∩ Uset i) := by
      intro x hx
      by_cases hxu : x ∈ Uset i
      · exact Or.inr ⟨hx, hxu⟩
      · exact Or.inl ⟨hx, hxu⟩
    exact (measure_mono this).trans (measure_union_le _ _)
  have h2 := lem_b (i := i) (th_pos i) (qq_pos i)
  rw [← hD] at h2
  set d := (volume D).toReal with hd
  set s := (volume (Sset i)).toReal with hs
  have ed : volume D = ENNReal.ofReal d := (ENNReal.ofReal_toReal hDfin).symm
  have es : volume (Sset i) = ENNReal.ofReal s := (ENNReal.ofReal_toReal hSfin).symm
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have r1 : d ≤ s + 5 / 8 * d := by
    have h3 : volume D ≤ volume (Sset i) + ENNReal.ofReal (5 / 8) * volume D :=
      h1.trans (by gcongr)
    rw [ed, es, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add hs0 (by positivity)] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  have r2 : (2 : ℝ) ^ i ≤ 2 * ((qq i : ℕ) : ℝ) * d := by
    rw [ed, ← ENNReal.ofReal_mul (by positivity)] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
  have r3 : (1 : ℝ) / 32 ≤ d := by
    have e : 2 * ((qq i : ℕ) : ℝ) = 32 * (2 : ℝ) ^ i := by
      unfold qq
      push_cast
      rw [pow_add]
      ring
    rw [e] at r2
    have hp : (0 : ℝ) < 2 ^ i := by positivity
    have : (2 : ℝ) ^ i * 1 ≤ 2 ^ i * (32 * d) := by linarith
    have := le_of_mul_le_mul_left this hp
    linarith
  rw [es]
  apply ENNReal.ofReal_le_ofReal
  linarith

lemma mem_D_ge_one {θ q i : ℕ} {x : ℝ} (hx : x ∈ Dset θ q i) : 1 ≤ x := by
  obtain ⟨hx0, h1, -⟩ := hx
  have h2 : (0 : ℝ) ≤ L x := by
    have := Int.floor_le (L x)
    rw [h1] at this
    have h3 : (0 : ℝ) ≤ ((i : ℤ) : ℝ) := by positivity
    linarith
  have := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hx0).1 h2
  simpa using this

end OMA

theorem OMA.solution : type_of% @Erdos1195.erdos_1195.variants.exists_set := by
  refine ⟨⋃ i, OMA.Sset i, MeasurableSet.iUnion OMA.meas_S, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact hi.1.1
  · have hdisj : Pairwise (Function.onFun Disjoint OMA.Sset) := by
      intro a b hab
      rw [Function.onFun, Set.disjoint_left]
      intro x hxa hxb
      apply hab
      have := hxa.1.2.1.symm.trans hxb.1.2.1
      exact_mod_cast this
    rw [measure_iUnion hdisj OMA.meas_S, eq_top_iff]
    calc (⊤ : ENNReal) = ∑' _ : ℕ, ENNReal.ofReal (3 / 256) :=
          (ENNReal.tsum_const_eq_top_of_ne_zero (by simp)).symm
      _ ≤ ∑' i, volume (OMA.Sset i) := ENNReal.tsum_le_tsum OMA.vol_S
  · intro x hx y hy hxy z hz
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.1 hy
    have hx0 : 0 < x := hxi.1.1
    have hy0 : 0 < y := hyj.1.1
    have hy1 : 1 ≤ y := OMA.mem_D_ge_one hyj.1
    have hxz : x = z * y := by
      rw [← hz]
      field_simp
    have hz0 : (0 : ℝ) < z := by
      by_contra h
      rw [not_lt] at h
      have : (z : ℝ) * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hy0.le
      linarith
    have hz1 : 1 ≤ z := by exact_mod_cast hz0
    have hmz : ((z.toNat : ℕ) : ℝ) = z := by
      have : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have hyB : y ∈ OMA.Bset (OMA.th i) (OMA.qq i) := by
      apply OMA.key_d (OMA.qq_three i) (OMA.th_F1 i) hy1 (m := z.toNat) (by omega)
      rw [hmz, ← hxz]
      exact hxi.1
    have hji : ¬ j < i := by
      intro hji
      exact hyj.2 (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hji, hyB⟩⟩)
    rcases eq_or_lt_of_le hz1 with h | h
    · apply hxy
      rw [hxz, ← h]
      simp
    · have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast h
      have hL : OMA.L x = OMA.L z + OMA.L y := by
        rw [hxz]
        unfold OMA.L
        exact Real.logb_mul (by positivity) (by positivity)
      have hLz : (1 : ℝ) ≤ OMA.L z := by
        unfold OMA.L
        rw [Real.le_logb_iff_rpow_le (by norm_num) hz0]
        simpa using hz2
      have hfl : ⌊OMA.L y + 1⌋ ≤ ⌊OMA.L x⌋ := Int.floor_le_floor (by linarith)
      rw [Int.floor_add_one, hxi.1.2.1, hyj.1.2.1] at hfl
      omega
