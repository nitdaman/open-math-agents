import OMAReductions.R_Erdos1166_erdos_1166_variants_erdos_taylor_R1

-- Step Erdos1166.erdos_1166.variants.erdos_taylor.R1.H1: hypothesis H1 of reduction Erdos1166.erdos_1166.variants.erdos_taylor.R1
-- Credit: @koolkao
--
-- Proof (fully elementary; Dvoretzky and Erdős 1951, Erdős and Taylor 1960, Lawler and Limic,
-- Random Walk: A Modern Introduction, Section 4.4):
-- (1) Block independence plus the fixed-time Markov property: if A depends on the first t steps
--     and B on the first s steps, P(A and (shift by t) in B) = P(A) P(B).
-- (2) Return probabilities: P(S_t = (a, b)) 4^t <= c_t(a + b) c_t(a - b), where c counts the
--     paths of a +-1 walk (the 45 degree rotation). Hence u_{2j} <= (C(2j, j) / 4^j)^2 <= 1/(pi j)
--     by Wallis' product, and u_{2j+1} = 0.
-- (3) Renewal at the first return: P(L_n >= k + 2) <= (1 - q_n) P(L_n >= k + 1), where q_n is
--     the probability of no return in steps 1..n, so P(L_n >= k + 1) <= (1 - q_n)^k.
-- (4) Last exit: 1 <= sum_{t <= n} u_t q_{n - t}. Splitting at n - m with n = m L gives
--     q_m (pi + 1 + log L + log m) >= (1 - 2/(pi (L - 1))) pi for all m >= 1.
-- (5) (1 - q)^k <= exp(-q k), and the arithmetic with L large in terms of delta gives
--     C n^(-(1 + delta/2)) with C = exp((1 + delta)(pi + 1 + log L) + 1), for every n >= 2.
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Erdos1165 Erdos1166

namespace OMA.H1Proof

/-- Partial sums of a step sequence. -/
def pos (y : ℕ → ℤ × ℤ) (t : ℕ) : ℤ × ℤ := ∑ i ∈ Finset.range t, y i

/-- Number of visits to the origin at times `0, …, n`. -/
def visits (y : ℕ → ℤ × ℤ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun t ↦ pos y t = 0).card

def sh (t : ℕ) (y : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ y (t + i)

def path {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) : ℕ → ℤ × ℤ := fun i ↦ X i ω

/-- `A` depends only on the first `m` coordinates. -/
def Det (m : ℕ) (A : Set (ℕ → ℤ × ℤ)) : Prop :=
  ∀ y y' : ℕ → ℤ × ℤ, (∀ i < m, y i = y' i) → y ∈ A → y' ∈ A

lemma pos_shift (y : ℕ → ℤ × ℤ) (t s : ℕ) : pos y (t + s) = pos y t + pos (sh t y) s :=
  Finset.sum_range_add _ _ _

lemma pos_congr {y y' : ℕ → ℤ × ℤ} {m t : ℕ} (h : ∀ i < m, y i = y' i) (ht : t ≤ m) :
    pos y t = pos y' t :=
  Finset.sum_congr rfl fun i hi ↦ h i (by rw [Finset.mem_range] at hi; omega)

lemma visits_congr {y y' : ℕ → ℤ × ℤ} {n : ℕ} (h : ∀ i < n, y i = y' i) :
    visits y n = visits y' n := by
  unfold visits
  congr 1
  refine Finset.filter_congr fun m hm ↦ ?_
  rw [Finset.mem_range] at hm
  rw [pos_congr h (by omega)]

/-- extension by zero of a finite window -/
def ext (m : ℕ) (z : Fin m → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ if h : i < m then z ⟨i, h⟩ else 0

lemma map_window {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (n j : ℕ) :
    Measure.map (fun ω (i : Fin n) ↦ X (j + i) ω) ℙ =
      Measure.pi (fun _ : Fin n ↦ Measure.map (X 0) ℙ) := by
  have hind : ProbabilityTheory.iIndepFun (fun i : Fin n ↦ X (j + i)) ℙ :=
    hX.indep.precomp (g := fun i : Fin n ↦ j + (i : ℕ)) fun a b h ↦ Fin.ext (by simpa using h)
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    fun i ↦ (hX.measurable _).aemeasurable).mp hind]
  congr 1
  funext i
  exact Eq.trans (hX.isUniform (j + i)) (Eq.symm (hX.isUniform 0))

lemma det_pre {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A)
    (j : ℕ) : {ω | sh j (path X ω) ∈ A} =
      (fun ω (i : Fin m) ↦ X (j + i) ω) ⁻¹' {z | ext m z ∈ A} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]

lemma meas_window {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (m j : ℕ) :
    Measurable (fun ω (i : Fin m) ↦ X (j + i) ω) :=
  measurable_pi_iff.mpr fun _ ↦ hX.measurable _

lemma det_meas {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A) (j : ℕ) :
    MeasurableSet {ω | sh j (path X ω) ∈ A} := by
  rw [det_pre X hA j]
  exact meas_window hX m j (Set.to_countable _).measurableSet

lemma sh_zero (y : ℕ → ℤ × ℤ) : sh 0 y = y := funext fun i ↦ by simp [sh]

lemma path_eq {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (A : Set (ℕ → ℤ × ℤ)) :
    {ω | path X ω ∈ A} = {ω | sh 0 (path X ω) ∈ A} := by
  simp only [sh_zero]

/-- fixed-time Markov property: shifting does not change probabilities -/
lemma prob_shift {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)}
    (hA : Det m A) (j : ℕ) :
    ℙ {ω | sh j (path X ω) ∈ A} = ℙ {ω | path X ω ∈ A} := by
  have hT : MeasurableSet {z : Fin m → ℤ × ℤ | ext m z ∈ A} := (Set.to_countable _).measurableSet
  rw [path_eq, det_pre X hA, det_pre X hA, ← Measure.map_apply (meas_window hX m j) hT,
    ← Measure.map_apply (meas_window hX m 0) hT, map_window hX, map_window hX]

end OMA.H1Proof

namespace OMA.H1Proof

lemma preA {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det t A) :
    {ω | path X ω ∈ A} = (fun ω (i : Finset.range t) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : i ∈ Finset.range t then z ⟨i, h⟩ else 0) ∈ A} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [hi, path]
  · exact hA _ _ fun i hi ↦ by simp [hi, path]

lemma preB {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t s : ℕ} {B : Set (ℕ → ℤ × ℤ)} (hB : Det s B) :
    {ω | sh t (path X ω) ∈ B} = (fun ω (i : Finset.Ico t (t + s)) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then z ⟨t + i, h⟩ else 0) ∈ B} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  have key : ∀ i < s, sh t (path X ω) i =
      (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then
        (fun (i : Finset.Ico t (t + s)) ↦ X i ω) ⟨t + i, h⟩ else 0) i := by
    intro i hi
    have hm : t + i ∈ Finset.Ico t (t + s) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    simp [hm, sh, path]
  constructor
  · exact hB _ _ key
  · exact hB _ _ fun i hi ↦ (key i hi).symm

/-- independence of disjoint blocks, combined with the Markov property -/
lemma prob_block {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {t s : ℕ}
    {A B : Set (ℕ → ℤ × ℤ)} (hA : Det t A) (hB : Det s B) :
    ℙ {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      ℙ {ω | path X ω ∈ A} * ℙ {ω | path X ω ∈ B} := by
  have hdisj : Disjoint (Finset.range t) (Finset.Ico t (t + s)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Ico] at hb
    omega
  have hind := hX.indep.indepFun_finset (Finset.range t) (Finset.Ico t (t + s)) hdisj
    hX.measurable
  have hset : {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      {ω | path X ω ∈ A} ∩ {ω | sh t (path X ω) ∈ B} := rfl
  rw [hset, ← prob_shift hX hB t, preA X hA, preB X hB]
  exact hind.measure_inter_preimage_eq_mul _ _ (Set.to_countable _).measurableSet
    (Set.to_countable _).measurableSet

end OMA.H1Proof

namespace OMA.H1Proof

/-- number of `±1` paths of length `t` ending at `u` -/
def c : ℕ → ℤ → ℕ
  | 0, u => if u = 0 then 1 else 0
  | t + 1, u => c t (u - 1) + c t (u + 1)

lemma c_neg : ∀ (t : ℕ) (u : ℤ), u < -(t : ℤ) → c t u = 0
  | 0, u, h => by simp [c]; omega
  | t + 1, u, h => by
    simp only [c]
    rw [c_neg t (u - 1) (by push_cast at h; omega), c_neg t (u + 1) (by push_cast at h; omega)]

lemma c_odd : ∀ (t : ℕ) (u : ℤ), ((t : ℤ) + u) % 2 = 1 → c t u = 0
  | 0, u, h => by simp [c]; omega
  | t + 1, u, h => by
    simp only [c]
    rw [c_odd t (u - 1) (by push_cast at h; omega), c_odd t (u + 1) (by push_cast at h; omega)]

lemma c_choose : ∀ (t i : ℕ), c t (2 * (i : ℤ) - t) = t.choose i
  | 0, i => by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp [c]
    · simp [c, Nat.choose_eq_zero_of_lt h]; omega
  | t + 1, 0 => by
    simp only [c, Nat.choose_zero_right]
    rw [c_neg t _ (by push_cast; omega)]
    have := c_choose t 0
    simp only [Nat.choose_zero_right] at this
    rw [show (2 * ((0 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) + 1) = 2 * ((0 : ℕ) : ℤ) - (t : ℤ) by
      push_cast; ring, this]
  | t + 1, i + 1 => by
    simp only [c, Nat.choose_succ_succ]
    have h1 := c_choose t i
    have h2 := c_choose t (i + 1)
    rw [show (2 * ((i + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) - 1) = 2 * (i : ℤ) - t by push_cast; ring,
      show (2 * ((i + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) + 1) = 2 * ((i + 1 : ℕ) : ℤ) - t by
        push_cast; ring, h1, h2]

lemma c_even (j : ℕ) : c (2 * j) 0 = j.centralBinom := by
  have := c_choose (2 * j) j
  rw [show (2 * (j : ℤ) - ((2 * j : ℕ) : ℤ)) = 0 by push_cast; ring] at this
  rw [this, Nat.centralBinom_eq_two_mul_choose]

lemma c_odd0 (j : ℕ) : c (2 * j + 1) 0 = 0 := c_odd _ _ (by push_cast; omega)

/-- the 2D count factorizes after the 45 degree rotation -/
lemma c_step (t : ℕ) (a b : ℤ) :
    c (t + 1) (a + b) * c (t + 1) (a - b) =
      c t ((a - 1) + b) * c t ((a - 1) - b) + c t ((a + 1) + b) * c t ((a + 1) - b) +
      c t (a + (b - 1)) * c t (a - (b - 1)) + c t (a + (b + 1)) * c t (a - (b + 1)) := by
  simp only [c]
  rw [show a - 1 + b = a + b - 1 by ring, show a - 1 - b = a - b - 1 by ring,
    show a + 1 + b = a + b + 1 by ring, show a + 1 - b = a - b + 1 by ring,
    show a + (b - 1) = a + b - 1 by ring, show a - (b - 1) = a - b + 1 by ring,
    show a + (b + 1) = a + b + 1 by ring, show a - (b + 1) = a - b - 1 by ring]
  ring

end OMA.H1Proof

namespace OMA.H1Proof

def stepsF : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

lemma steps_eq : steps = (stepsF : Set (ℤ × ℤ)) := by
  simp [steps, stepsF]

lemma prob_step {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) (S : Set (ℤ × ℤ)) :
    ℙ (X k ⁻¹' S) = (4 : ℝ≥0∞)⁻¹ * Measure.count (steps ∩ S) := by
  have hu : Measure.map (X k) ℙ = ProbabilityTheory.cond Measure.count steps := hX.isUniform k
  rw [← Measure.map_apply (hX.measurable k) (Set.to_countable S).measurableSet, hu,
    ProbabilityTheory.cond_apply (Set.to_countable _).measurableSet, steps_eq,
    Measure.count_apply_finset]
  rfl

lemma prob_step_eq {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) {e : ℤ × ℤ} (he : e ∈ steps) :
    ℙ (X k ⁻¹' {e}) = (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_step hX, Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr he),
    Measure.count_singleton, mul_one]

lemma prob_step_bad {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) : ℙ (X k ⁻¹' stepsᶜ) = 0 := by
  rw [prob_step hX, Set.inter_compl_self, measure_empty, mul_zero]

lemma det_pos (t : ℕ) (z : ℤ × ℤ) : Det t {y | pos y t = z} := fun y y' h hy ↦ by
  simp only [Set.mem_setOf_eq] at hy ⊢
  rw [← pos_congr h le_rfl, hy]

lemma det_zero (e : ℤ × ℤ) : Det 1 {y | y 0 = e} := fun y y' h hy ↦ by
  simp only [Set.mem_setOf_eq] at hy ⊢
  rw [← h 0 one_pos, hy]

lemma prob_pos_step {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (x e : ℤ × ℤ)
    (he : e ∈ steps) :
    ℙ {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}} =
      ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_block hX (det_pos t (x - e)) (det_zero e)]
  congr 1
  exact prob_step_eq hX 0 he

lemma pos_succ (y : ℕ → ℤ × ℤ) (t : ℕ) : pos y (t + 1) = pos y t + y t :=
  Finset.sum_range_succ _ _

/-- the return probability bound, in counting form -/
lemma prob_pos_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ (t : ℕ) (a b : ℤ), ℙ {ω | pos (path X ω) t = (a, b)} * 4 ^ t ≤
      ((c t (a + b) * c t (a - b) : ℕ) : ℝ≥0∞)
  | 0, a, b => by
    simp only [pow_zero, mul_one]
    by_cases h : (a, b) = 0
    · have ha : a = 0 := congrArg Prod.fst h
      have hb : b = 0 := congrArg Prod.snd h
      subst ha hb
      simp only [c, add_zero, sub_self, if_true, mul_one, Nat.cast_one]
      exact prob_le_one
    · have : {ω | pos (path X ω) 0 = (a, b)} = ∅ := by
        ext ω
        simp only [pos, Finset.range_zero, Finset.sum_empty, Set.mem_setOf_eq,
          Set.mem_empty_iff_false, iff_false]
        exact fun h' ↦ h h'.symm
      rw [this, measure_empty]
      simp
  | t + 1, a, b => by
    set x : ℤ × ℤ := (a, b)
    have h1 : ((1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h2 : ((-1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h3 : ((0 : ℤ), (1 : ℤ)) ∈ steps := by simp [steps]
    have h4 : ((0 : ℤ), (-1 : ℤ)) ∈ steps := by simp [steps]
    let E : ℤ × ℤ → Set Ω := fun e ↦
      {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}}
    have hsub : {ω | pos (path X ω) (t + 1) = x} ⊆
        (((E (1, 0) ∪ E (-1, 0)) ∪ E (0, 1)) ∪ E (0, -1)) ∪ X t ⁻¹' stepsᶜ := by
      intro ω hω
      simp only [Set.mem_setOf_eq, pos_succ] at hω
      by_cases hs : X t ω ∈ steps
      · have hx : pos (path X ω) t = x - X t ω := by rw [← hω]; simp [path]
        have hE : ω ∈ E (X t ω) := ⟨hx, rfl⟩
        simp only [steps, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with h | h | h | h <;> rw [h] at hE <;> simp [hE]
      · exact Or.inr hs
    have hE : ∀ e ∈ steps, ℙ (E e) * 4 ^ (t + 1) ≤
        ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
      intro e he
      apply le_of_eq
      rw [prob_pos_step hX t x e he, pow_succ]
      calc ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ * (4 ^ t * 4)
          = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t * (4 * (4 : ℝ≥0∞)⁻¹) := by ring
        _ = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    have hm : ℙ {ω | pos (path X ω) (t + 1) = x} ≤
        ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1)) := by
      refine (measure_mono hsub).trans ?_
      refine (measure_union_le _ _).trans ?_
      rw [prob_step_bad hX t, add_zero]
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      exact measure_union_le _ _
    calc ℙ {ω | pos (path X ω) (t + 1) = x} * 4 ^ (t + 1)
        ≤ (ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1))) * 4 ^ (t + 1) :=
          by gcongr
      _ = ℙ (E (1, 0)) * 4 ^ (t + 1) + ℙ (E (-1, 0)) * 4 ^ (t + 1) +
          ℙ (E (0, 1)) * 4 ^ (t + 1) + ℙ (E (0, -1)) * 4 ^ (t + 1) := by ring
      _ ≤ ((c t ((a - 1) + b) * c t ((a - 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t ((a + 1) + b) * c t ((a + 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b - 1)) * c t (a - (b - 1)) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b + 1)) * c t (a - (b + 1)) : ℕ) : ℝ≥0∞) := by
        gcongr
        · refine (hE _ h1).trans ?_
          have : x - (1, 0) = (a - 1, b) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h2).trans ?_
          have : x - (-1, 0) = (a + 1, b) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h3).trans ?_
          have : x - (0, 1) = (a, b - 1) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h4).trans ?_
          have : x - (0, -1) = (a, b + 1) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
      _ = ((c (t + 1) (a + b) * c (t + 1) (a - b) : ℕ) : ℝ≥0∞) := by
        rw [c_step]; push_cast; ring

end OMA.H1Proof

namespace OMA.H1Proof

lemma cb_sq_le (j : ℕ) (hj : 1 ≤ j) :
    ((j.centralBinom : ℝ)) ^ 2 / 16 ^ j ≤ 1 / (Real.pi * j) := by
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfac : ((2 * j).factorial : ℝ) = (j.centralBinom : ℝ) * (j.factorial : ℝ) ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
    rw [show 2 * j - j = j by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← h]
    push_cast; ring
  have hcb : (0 : ℝ) < (j.centralBinom : ℝ) := by exact_mod_cast Nat.centralBinom_pos j
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hW := Real.Wallis.W_eq_factorial_ratio j
  rw [hfac] at hW
  have hW2 : Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) = 16 ^ j := by
    rw [hW, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    rw [show (16 : ℝ) ^ j = 2 ^ (4 * j) by rw [pow_mul]; norm_num]
    ring
  have hle := Real.Wallis.le_W j
  have h1 : Real.pi * j / (2 * j + 1) ≤ (2 * (j : ℝ) + 1) / (2 * j + 2) * (Real.pi / 2) := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * (j : ℝ) + 1) * Real.pi * (2 * j + 1) =
        Real.pi * j * ((2 * j + 2) * 2) + Real.pi := by ring
    rw [this]
    linarith [Real.pi_pos]
  have h2 : Real.pi * j ≤ Real.Wallis.W j * (2 * j + 1) := by
    have := h1.trans hle
    rwa [div_le_iff₀ (by positivity)] at this
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← hW2]
  calc (j.centralBinom : ℝ) ^ 2 * (Real.pi * j)
      ≤ (j.centralBinom : ℝ) ^ 2 * (Real.Wallis.W j * (2 * j + 1)) := by gcongr
    _ = Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) := by ring

/-- return probability, as a real number -/
noncomputable def u {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : ℝ :=
  (ℙ {ω | pos (path X ω) t = 0}).toReal

lemma prob_zero_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) :
    u X t * 4 ^ t ≤ (c t 0 : ℝ) ^ 2 := by
  have h := prob_pos_le hX t 0 0
  simp only [add_zero, sub_zero] at h
  change ℙ {ω | pos (path X ω) t = 0} * 4 ^ t ≤ _ at h
  have h' : (ℙ {ω | pos (path X ω) t = 0} * 4 ^ t).toReal ≤ ((c t 0 * c t 0 : ℕ) : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono (ENNReal.natCast_ne_top _) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h'
  simp only [ENNReal.toReal_natCast] at h'
  unfold u
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4] at h'
  calc (ℙ {ω | pos (path X ω) t = 0}).toReal * 4 ^ t ≤ ((c t 0 * c t 0 : ℕ) : ℝ) := h'
    _ = (c t 0 : ℝ) ^ 2 := by push_cast; ring

lemma u_nonneg {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : 0 ≤ u X t :=
  ENNReal.toReal_nonneg

lemma u_le_one {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : u X t ≤ 1 := by
  unfold u
  have : ℙ {ω | pos (path X ω) t = 0} ≤ 1 := prob_le_one
  calc (ℙ {ω | pos (path X ω) t = 0}).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp) this
    _ = 1 := by simp

lemma u_odd {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) : u X (2 * j + 1) = 0 := by
  have h := prob_zero_le hX (2 * j + 1)
  rw [c_odd0] at h
  have h0 := u_nonneg X (2 * j + 1)
  have hp : (0 : ℝ) < 4 ^ (2 * j + 1) := by positivity
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  nlinarith

lemma u_even {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) (hj : 1 ≤ j) :
    u X (2 * j) ≤ 1 / (Real.pi * j) := by
  have h := prob_zero_le hX (2 * j)
  rw [c_even, pow_mul] at h
  norm_num at h
  refine le_trans ?_ (cb_sq_le j hj)
  rw [le_div_iff₀ (by positivity)]
  exact h

lemma u_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (ht : 1 ≤ t) :
    u X t ≤ 2 / (Real.pi * t) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' t
  · have hj : 1 ≤ j := by omega
    refine (u_even hX j hj).trans (le_of_eq ?_)
    have : (j : ℝ) ≠ 0 := by positivity
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  · rw [u_odd hX]
    positivity

lemma u_pair {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) :
    u X (2 * j + 1) + u X (2 * j + 2) ≤ 1 / (Real.pi * ((j : ℝ) + 1)) := by
  rw [u_odd hX, zero_add, show 2 * j + 2 = 2 * (j + 1) by ring]
  have := u_even hX (j + 1) (by omega)
  push_cast at this
  exact this

end OMA.H1Proof

namespace OMA.H1Proof

def NoRet (m : ℕ) : Set (ℕ → ℤ × ℤ) := {y | ∀ s, 1 ≤ s → s ≤ m → pos y s ≠ 0}

def FR (t : ℕ) : Set (ℕ → ℤ × ℤ) := {y | pos y t = 0 ∧ ∀ s, 1 ≤ s → s < t → pos y s ≠ 0}

def Vis (n k : ℕ) : Set (ℕ → ℤ × ℤ) := {y | k ≤ visits y n}

lemma det_noRet (m : ℕ) : Det m (NoRet m) := fun y y' h hy s h1 h2 ↦ by
  rw [← pos_congr h h2]; exact hy s h1 h2

lemma det_FR (t : ℕ) : Det t (FR t) := fun y y' h hy ↦
  ⟨by rw [← pos_congr h le_rfl]; exact hy.1,
   fun s h1 h2 ↦ by rw [← pos_congr h h2.le]; exact hy.2 s h1 h2⟩

lemma det_vis (n k : ℕ) : Det n (Vis n k) := fun y y' h hy ↦ by
  simp only [Vis, Set.mem_setOf_eq] at hy ⊢
  rw [← visits_congr h]; exact hy

lemma visits_mono (y : ℕ → ℤ × ℤ) {m n : ℕ} (h : m ≤ n) : visits y m ≤ visits y n :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))

lemma pos_zero (y : ℕ → ℤ × ℤ) : pos y 0 = 0 := by simp [pos]

lemma pos_sh (y : ℕ → ℤ × ℤ) {t : ℕ} (ht : pos y t = 0) (s : ℕ) :
    pos (sh t y) s = pos y (t + s) := by
  rw [pos_shift, ht, zero_add]

lemma renewal_subset (n k : ℕ) (hk : 1 ≤ k) :
    Vis n (k + 1) ⊆ {y | ∃ t ∈ Finset.Icc 1 n, y ∈ FR t ∧ sh t y ∈ Vis (n - t) k} := by
  intro y hy
  simp only [Vis, Set.mem_setOf_eq, visits] at hy
  set V := (Finset.range (n + 1)).filter fun t ↦ pos y t = 0 with hV
  have h0 : 0 ∈ V := Finset.mem_filter.mpr ⟨by simp, pos_zero y⟩
  have hcard : k ≤ (V.erase 0).card := by rw [Finset.card_erase_of_mem h0]; omega
  have hne : (V.erase 0).Nonempty := Finset.card_pos.mp (by omega)
  set t := (V.erase 0).min' hne with ht
  have htm : t ∈ V.erase 0 := Finset.min'_mem _ hne
  have htm' := Finset.mem_erase.mp htm
  have htV := Finset.mem_filter.mp htm'.2
  have htn : t < n + 1 := Finset.mem_range.mp htV.1
  refine ⟨t, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ⟨htV.2, fun s h1 h2 hs ↦ ?_⟩, ?_⟩
  · have hsV : s ∈ V.erase 0 :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs⟩⟩
    have := Finset.min'_le (V.erase 0) s hsV
    omega
  · simp only [Vis, Set.mem_setOf_eq, visits]
    refine hcard.trans (Finset.card_le_card_of_injOn (fun a ↦ a - t) ?_ ?_)
    · intro a ha
      have ha' := Finset.mem_erase.mp ha
      have haV := Finset.mem_filter.mp ha'.2
      have hta : t ≤ a := Finset.min'_le (V.erase 0) a ha
      have han : a < n + 1 := Finset.mem_range.mp haV.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (show a - t < n - t + 1 by omega), ?_⟩
      rw [pos_sh y htV.2, show t + (a - t) = a by omega]
      exact haV.2
    · intro a ha b hb hab
      have hta : t ≤ a := Finset.min'_le (V.erase 0) a ha
      have htb : t ≤ b := Finset.min'_le (V.erase 0) b hb
      have hab' : a - t = b - t := hab
      omega

lemma lastexit_subset (n : ℕ) :
    Set.univ ⊆ {y | ∃ t ∈ Finset.range (n + 1), y ∈ {y | pos y t = 0} ∧ sh t y ∈ NoRet (n - t)} := by
  intro y _
  set V := (Finset.range (n + 1)).filter fun t ↦ pos y t = 0 with hV
  have h0 : 0 ∈ V := Finset.mem_filter.mpr ⟨by simp, pos_zero y⟩
  have hne : V.Nonempty := ⟨0, h0⟩
  set t := V.max' hne with ht
  have htV := Finset.mem_filter.mp (Finset.max'_mem V hne)
  refine ⟨t, htV.1, htV.2, fun s h1 h2 hs ↦ ?_⟩
  rw [pos_sh y htV.2] at hs
  have htn : t < n + 1 := Finset.mem_range.mp htV.1
  have hsV : t + s ∈ V := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs⟩
  have := Finset.le_max' V (t + s) hsV
  omega

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma renewal_step (hX : IsSimpleRandomWalkSteps X) (n k : ℕ) (hk : 1 ≤ k) :
    ℙ {ω | path X ω ∈ Vis n (k + 1)} ≤
      ℙ {ω | path X ω ∈ NoRet n}ᶜ * ℙ {ω | path X ω ∈ Vis n k} := by
  have hU : {ω | path X ω ∈ NoRet n}ᶜ = ⋃ t ∈ Finset.Icc 1 n, {ω | path X ω ∈ FR t} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, NoRet, Set.mem_iUnion, FR,
      Finset.mem_Icc, exists_prop, not_forall, not_not]
    constructor
    · rintro ⟨s, h1, h2, hs⟩
      classical
      let P : ℕ → Prop := fun s ↦ 1 ≤ s ∧ s ≤ n ∧ pos (path X ω) s = 0
      have hex : ∃ s, P s := ⟨s, h1, h2, hs⟩
      refine ⟨Nat.find hex, ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2.1⟩,
        (Nat.find_spec hex).2.2, fun r hr1 hr2 hr ↦ ?_⟩
      exact Nat.find_min hex hr2 ⟨hr1, by have := (Nat.find_spec hex).2.1; omega, hr⟩
    · rintro ⟨t, ⟨h1, h2⟩, ht, -⟩
      exact ⟨t, h1, h2, ht⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 n)) fun t ↦ {ω | path X ω ∈ FR t} := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_setOf_eq, FR] at h1 h2
    rcases lt_or_gt_of_ne hab with h | h
    · exact h2.2 a (Finset.mem_Icc.mp ha).1 h h1.1
    · exact h1.2 b (Finset.mem_Icc.mp hb).1 h h2.1
  have hmeasFR : ∀ t, MeasurableSet {ω | path X ω ∈ FR t} := fun t ↦ by
    rw [path_eq]; exact det_meas hX (det_FR t) 0
  have hsum : ℙ {ω | path X ω ∈ NoRet n}ᶜ = ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t} := by
    rw [hU, measure_biUnion_finset hdisj fun t _ ↦ hmeasFR t]
  calc ℙ {ω | path X ω ∈ Vis n (k + 1)}
      ≤ ℙ (⋃ t ∈ Finset.Icc 1 n, {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (n - t) k}) := by
        refine measure_mono fun ω hω ↦ ?_
        obtain ⟨t, ht, h⟩ := renewal_subset n k hk hω
        exact Set.mem_iUnion₂.mpr ⟨t, ht, h⟩
    _ ≤ ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (n - t) k} :=
        measure_biUnion_finset_le _ _
    _ = ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t} * ℙ {ω | path X ω ∈ Vis (n - t) k} :=
        Finset.sum_congr rfl fun t _ ↦ prob_block hX (det_FR t) (det_vis (n - t) k)
    _ ≤ ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t} * ℙ {ω | path X ω ∈ Vis n k} := by
        gcongr with t ht
        intro ω hω
        simp only [Set.mem_setOf_eq, Vis] at hω ⊢
        exact hω.trans (visits_mono _ (Nat.sub_le n t))
    _ = ℙ {ω | path X ω ∈ NoRet n}ᶜ * ℙ {ω | path X ω ∈ Vis n k} := by
        rw [hsum, Finset.sum_mul]

lemma renewal (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    ∀ k : ℕ, ℙ {ω | path X ω ∈ Vis n (k + 1)} ≤ ℙ {ω | path X ω ∈ NoRet n}ᶜ ^ k
  | 0 => by rw [pow_zero]; exact prob_le_one
  | k + 1 => by
    rw [pow_succ']
    refine (renewal_step hX n (k + 1) (by omega)).trans ?_
    gcongr
    exact renewal hX n k

lemma lastexit (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    1 ≤ ∑ t ∈ Finset.range (n + 1),
      ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ NoRet (n - t)} := by
  calc (1 : ℝ≥0∞) = ℙ (Set.univ : Set Ω) := measure_univ.symm
    _ ≤ ℙ (⋃ t ∈ Finset.range (n + 1),
          {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)}) := by
        refine measure_mono fun ω _ ↦ ?_
        obtain ⟨t, ht, h⟩ := lastexit_subset n (Set.mem_univ (path X ω))
        exact Set.mem_iUnion₂.mpr ⟨t, ht, h⟩
    _ ≤ ∑ t ∈ Finset.range (n + 1),
          ℙ {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)} :=
        measure_biUnion_finset_le _ _
    _ = _ := Finset.sum_congr rfl fun t _ ↦ prob_block hX (det_pos t 0) (det_noRet (n - t))

end OMA.H1Proof

namespace OMA.H1Proof

open Real

lemma sum_pairs (u : ℕ → ℝ) (M : ℕ) :
    ∑ t ∈ Finset.range (2 * M + 1), u t =
      u 0 + ∑ j ∈ Finset.range M, (u (2 * j + 1) + u (2 * j + 2)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) + 1 = 2 * M + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring_nf

lemma green_le (u : ℕ → ℝ) (hu0 : ∀ t, 0 ≤ u t) (hu00 : u 0 ≤ 1)
    (hpair : ∀ j : ℕ, u (2 * j + 1) + u (2 * j + 2) ≤ 1 / (π * ((j : ℝ) + 1))) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), u t ≤ 1 + (1 + Real.log n) / π := by
  have hsub : ∑ t ∈ Finset.range (n + 1), u t ≤ ∑ t ∈ Finset.range (2 * n + 1), u t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun t _ _ ↦ hu0 t
  refine hsub.trans ?_
  rw [sum_pairs]
  have hh : ∑ j ∈ Finset.range n, (u (2 * j + 1) + u (2 * j + 2)) ≤ (harmonic n : ℝ) / π := by
    calc ∑ j ∈ Finset.range n, (u (2 * j + 1) + u (2 * j + 2))
        ≤ ∑ j ∈ Finset.range n, 1 / (π * ((j : ℝ) + 1)) := Finset.sum_le_sum fun j _ ↦ hpair j
      _ = (harmonic n : ℝ) / π := by
        rw [harmonic, Rat.cast_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        push_cast
        rw [one_div, mul_inv, div_eq_mul_inv, mul_comm]
  have hlog := harmonic_le_one_add_log n
  have : (harmonic n : ℝ) / π ≤ (1 + Real.log n) / π := by gcongr
  linarith

/-- the two-scale lower bound on the escape probability -/
lemma q_lower (u q : ℕ → ℝ) (hu0 : ∀ t, 0 ≤ u t) (hu00 : u 0 ≤ 1)
    (hut : ∀ t : ℕ, 1 ≤ t → u t ≤ 2 / (π * t))
    (hpair : ∀ j : ℕ, u (2 * j + 1) + u (2 * j + 2) ≤ 1 / (π * ((j : ℝ) + 1)))
    (hq0 : ∀ m, 0 ≤ q m) (hq1 : ∀ m, q m ≤ 1) (hqa : Antitone q)
    (hle : ∀ n, 1 ≤ ∑ t ∈ Finset.range (n + 1), u t * q (n - t))
    (L : ℕ) (hL : 2 ≤ L) (m : ℕ) (hm : 1 ≤ m) :
    (1 - 2 / (π * ((L : ℝ) - 1))) * π ≤ q m * (π + 1 + Real.log L + Real.log m) := by
  set n := m * L with hn
  have hmn : m ≤ n := by rw [hn]; nlinarith
  have hsplit := Finset.sum_range_add_sum_Ico (fun t ↦ u t * q (n - t))
    (show n - m + 1 ≤ n + 1 by omega)
  have hL1 : (1 : ℝ) ≤ (L : ℝ) - 1 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Real.pi_pos
  -- the near part
  have hnear : ∑ t ∈ Finset.Ico (n - m + 1) (n + 1), u t * q (n - t) ≤
      2 / (π * ((L : ℝ) - 1)) := by
    have hb : ∀ t ∈ Finset.Ico (n - m + 1) (n + 1), u t * q (n - t) ≤ 2 / (π * (m * ((L : ℝ) - 1))) := by
      intro t ht
      have ht' := Finset.mem_Ico.mp ht
      have hnat : m * (L - 1) ≤ t := by
        have : m * (L - 1) = n - m := by rw [hn, Nat.mul_sub_one]
        omega
      have hreal : (m : ℝ) * ((L : ℝ) - 1) ≤ t := by
        have := (Nat.cast_le (α := ℝ)).mpr hnat
        push_cast [Nat.cast_sub (show 1 ≤ L by omega)] at this
        exact this
      calc u t * q (n - t) ≤ u t * 1 := by gcongr; exact hu0 t; exact hq1 _
        _ = u t := mul_one _
        _ ≤ 2 / (π * t) := hut t (by
            have : 1 ≤ m * (L - 1) := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
            omega)
        _ ≤ 2 / (π * (m * ((L : ℝ) - 1))) := by gcongr
    refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
      show n + 1 - (n - m + 1) = m by omega]
    rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
    ring
  -- the far part
  have hfar : ∑ t ∈ Finset.range (n - m + 1), u t * q (n - t) ≤
      q m * (1 + (1 + Real.log n) / π) := by
    calc ∑ t ∈ Finset.range (n - m + 1), u t * q (n - t)
        ≤ ∑ t ∈ Finset.range (n - m + 1), u t * q m := by
          refine Finset.sum_le_sum fun t ht ↦ ?_
          have := Finset.mem_range.mp ht
          gcongr
          · exact hu0 t
          · exact hqa (by omega)
      _ ≤ ∑ t ∈ Finset.range (n + 1), u t * q m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
            fun t _ _ ↦ mul_nonneg (hu0 t) (hq0 m)
      _ = q m * ∑ t ∈ Finset.range (n + 1), u t := by rw [Finset.mul_sum]; simp [mul_comm]
      _ ≤ q m * (1 + (1 + Real.log n) / π) := by
          gcongr
          · exact hq0 m
          · exact green_le u hu0 hu00 hpair n
  have h1 := hle n
  rw [← hsplit] at h1
  have hlogn : Real.log n = Real.log m + Real.log L := by
    rw [hn, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  rw [hlogn] at hfar
  have key : 1 - 2 / (π * ((L : ℝ) - 1)) ≤
      q m * (1 + (1 + (Real.log m + Real.log L)) / π) := by linarith
  have e : q m * (1 + (1 + (Real.log m + Real.log L)) / π) * π =
      q m * (π + 1 + Real.log L + Real.log m) := by
    rw [mul_assoc, add_mul, div_mul_cancel₀ _ hpi.ne']; ring
  rw [← e]
  exact mul_le_mul_of_nonneg_right key hpi.le

end OMA.H1Proof

namespace OMA.H1Proof

open Real

noncomputable def q {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (m : ℕ) : ℝ :=
  (ℙ {ω | path X ω ∈ NoRet m}).toReal

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma q_nonneg (m : ℕ) : 0 ≤ q X m := ENNReal.toReal_nonneg

lemma q_le_one (m : ℕ) : q X m ≤ 1 := by
  unfold q
  calc (ℙ {ω | path X ω ∈ NoRet m}).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp) prob_le_one
    _ = 1 := by simp

lemma q_anti : Antitone (q X) := by
  intro a b hab
  unfold q
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω s h1 h2 ↦ ?_)
  exact hω s h1 (h2.trans hab)

lemma q_lastexit (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    1 ≤ ∑ t ∈ Finset.range (n + 1), u X t * q X (n - t) := by
  have h := lastexit hX n
  have hne : ∑ t ∈ Finset.range (n + 1),
      ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ NoRet (n - t)} ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun t _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have h' := ENNReal.toReal_mono hne h
  rw [ENNReal.toReal_sum fun t _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
    at h'
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul] at h'
  exact h'

lemma tail (hX : IsSimpleRandomWalkSteps X) (n j : ℕ) :
    ℙ {ω | path X ω ∈ Vis n (j + 1)} ≤ ENNReal.ofReal ((1 - q X n) ^ j) := by
  refine (renewal hX n j).trans (le_of_eq ?_)
  have hmeas : MeasurableSet {ω | path X ω ∈ NoRet n} := by
    rw [path_eq]; exact det_meas hX (det_noRet n) 0
  rw [prob_compl_eq_one_sub hmeas, ENNReal.ofReal_pow (by linarith [q_le_one (X := X) n])]
  congr 1
  unfold q
  rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem h1 : OMA.R_Erdos1166_erdos_1166_variants_erdos_taylor_R1.H1 := by
  intro Ω _ _ X hX δ hδ
  have hpi := Real.pi_pos
  set L : ℕ := ⌈4 * (1 + δ) / δ⌉₊ + 2 with hLdef
  have hL : 2 ≤ L := by omega
  set a : ℝ := 2 / (π * ((L : ℝ) - 1)) with ha
  set b : ℝ := π + 1 + Real.log L with hb
  have hLr : 4 * (1 + δ) / δ + 1 ≤ (L : ℝ) - 1 := by
    have h1 : 4 * (1 + δ) / δ ≤ (⌈4 * (1 + δ) / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (L : ℝ) = (⌈4 * (1 + δ) / δ⌉₊ : ℝ) + 2 := by rw [hLdef]; push_cast; ring
    linarith
  have hL1 : (0 : ℝ) < (L : ℝ) - 1 := by
    have : 0 ≤ 4 * (1 + δ) / δ := by positivity
    linarith
  have hdL : 4 * (1 + δ) ≤ δ * ((L : ℝ) - 1) := by
    have := (div_le_iff₀' hδ).mp (show 4 * (1 + δ) / δ ≤ (L : ℝ) - 1 by linarith)
    linarith
  have haδ : a * (1 + δ) ≤ δ / 2 := by
    rw [ha, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hb0 : 0 ≤ b := by
    have : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ L by omega))
    rw [hb]; linarith
  refine ⟨Real.exp ((1 + δ) * b + 1), fun n hn k hk ↦ ?_⟩
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set ℓ := Real.log n with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos hn1
  have hk1 : 1 ≤ k := by
    have : 0 < (k : ℝ) := lt_of_lt_of_le (by positivity) hk
    exact_mod_cast this
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hset : {ω | j + 1 ≤ localTime X n ω 0} = {ω | path X ω ∈ Vis n (j + 1)} := rfl
  rw [hset]
  refine (tail hX n j).trans (ENNReal.ofReal_le_ofReal ?_)
  -- the escape bound
  set Q := q X n with hQ
  have hQ0 : 0 ≤ Q := q_nonneg n
  have hQ1 : Q ≤ 1 := q_le_one n
  have hqb : (1 - a) * π ≤ Q * (ℓ + b) := by
    have := q_lower (u X) (q X) (u_nonneg X) (by rw [show (0:ℕ) = 0 from rfl]; exact u_le_one X 0)
      (u_le hX) (u_pair hX) q_nonneg q_le_one q_anti (q_lastexit hX) L hL n (by omega)
    rw [hQ, hb]; linarith
  have hj : (1 + δ) * ℓ ^ 2 / π - 1 ≤ (j : ℝ) := by push_cast at hk; linarith
  -- (1 - a)(1 + δ) ℓ² ≤ Q (1 + δ) ℓ² / π · (ℓ + b)
  set K := (1 - a) * (1 + δ) with hK
  have hK1 : 1 + δ / 2 ≤ K := by rw [hK]; nlinarith
  have hK2 : K ≤ 1 + δ := by
    have : 0 ≤ a := by rw [ha]; positivity
    rw [hK]; nlinarith
  have hmain : K * (ℓ - b) ≤ Q * (1 + δ) * ℓ ^ 2 / π := by
    have hlb : 0 < ℓ + b := by linarith
    have e1 : K * ℓ ^ 2 ≤ Q * (1 + δ) * ℓ ^ 2 / π * (ℓ + b) := by
      have : (1 - a) * π * ((1 + δ) * ℓ ^ 2) ≤ Q * (ℓ + b) * ((1 + δ) * ℓ ^ 2) := by
        gcongr
      have e0 : Q * (1 + δ) * ℓ ^ 2 / π * π = Q * (1 + δ) * ℓ ^ 2 := div_mul_cancel₀ _ hpi.ne'
      have e : Q * (1 + δ) * ℓ ^ 2 / π * (ℓ + b) * π = Q * (ℓ + b) * ((1 + δ) * ℓ ^ 2) := by
        calc Q * (1 + δ) * ℓ ^ 2 / π * (ℓ + b) * π = (Q * (1 + δ) * ℓ ^ 2 / π * π) * (ℓ + b) := by
              ring
          _ = Q * (ℓ + b) * ((1 + δ) * ℓ ^ 2) := by rw [e0]; ring
      have e2 : K * ℓ ^ 2 * π = (1 - a) * π * ((1 + δ) * ℓ ^ 2) := by rw [hK]; ring
      have : K * ℓ ^ 2 * π ≤ Q * (1 + δ) * ℓ ^ 2 / π * (ℓ + b) * π := by rw [e, e2]; exact this
      exact le_of_mul_le_mul_right this hpi
    have e3 : K * (ℓ - b) * (ℓ + b) ≤ K * ℓ ^ 2 := by
      have hK0 : 0 ≤ K := by linarith
      have e4 : K * (ℓ - b) * (ℓ + b) = K * ℓ ^ 2 - K * b ^ 2 := by ring
      have e5 : 0 ≤ K * b ^ 2 := mul_nonneg hK0 (sq_nonneg b)
      rw [e4]; linarith
    exact le_of_mul_le_mul_right (e3.trans e1) hlb
  have hexp : -(Q * j) ≤ (1 + δ) * b + 1 + ℓ * (-(1 + δ / 2)) := by
    have hQj : Q * ((1 + δ) * ℓ ^ 2 / π - 1) ≤ Q * j := by gcongr
    have : Q * ((1 + δ) * ℓ ^ 2 / π - 1) = Q * (1 + δ) * ℓ ^ 2 / π - Q := by ring
    rw [this] at hQj
    have : (1 + δ / 2) * ℓ - (1 + δ) * b ≤ K * (ℓ - b) := by nlinarith
    linarith
  calc (1 - Q) ^ j ≤ Real.exp (-Q) ^ j :=
        pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg Q) j
    _ = Real.exp (-(Q * j)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp ((1 + δ) * b + 1 + ℓ * (-(1 + δ / 2))) := Real.exp_le_exp.mpr hexp
    _ = Real.exp ((1 + δ) * b + 1) * (n : ℝ) ^ (-(1 + δ / 2)) := by
        rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]

end OMA.H1Proof

theorem OMA.solution : OMA.R_Erdos1166_erdos_1166_variants_erdos_taylor_R1.H1 :=
  OMA.H1Proof.h1
