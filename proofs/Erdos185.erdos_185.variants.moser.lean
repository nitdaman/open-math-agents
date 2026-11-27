import FormalConjectures.ErdosProblems.«185»

-- Problem: Erdős Problem 185 — moser
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/185.lean (declaration Erdos185.erdos_185.variants.moser)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Asymptotics Filter Finset

namespace OMAMoser

/-- number of coordinates equal to `1` -/
def ones {n : ℕ} (v : Fin n → Fin 3) : ℕ := (univ.filter (fun i => v i = 1)).card

lemma mid (p q r : Fin 3) (h : (((q : ℕ) : ℝ) - p) * (((q : ℕ) : ℝ) - r) < 0) : q = 1 := by
  revert h
  fin_cases p <;> fin_cases q <;> fin_cases r <;> norm_num

lemma notmid (p q r : Fin 3) (hp : p = 1) (hqr : q ≠ r) :
    (((p : ℕ) : ℝ) - q) * (((p : ℕ) : ℝ) - r) ≤ 0 := by
  subst hp
  revert hqr
  fin_cases q <;> fin_cases r <;> norm_num

lemma cast_inj {p q : Fin 3} (h : ((p : ℕ) : ℝ) = ((q : ℕ) : ℝ)) : p = q := by
  apply Fin.ext; exact_mod_cast h

/-- the endpoint has fewer ones than the middle point -/
lemma key {n : ℕ} (x y z : Fin n → Fin 3) (B V : Fin n → ℝ) (a b c : ℝ)
    (hx : ∀ i, ((x i : ℕ) : ℝ) = B i + a * V i)
    (hy : ∀ i, ((y i : ℕ) : ℝ) = B i + b * V i)
    (hz : ∀ i, ((z i : ℕ) : ℝ) = B i + c * V i)
    (hneg : (b - a) * (b - c) < 0) (hxy : x ≠ y) : ones x < ones y := by
  have hpos : 0 < (a - b) * (a - c) := by nlinarith [sq_nonneg (a - b)]
  have hbc : b - c ≠ 0 := by intro h; rw [h, mul_zero] at hneg; exact lt_irrefl _ hneg
  -- moving coordinates
  have hmove : ∀ i, V i ≠ 0 → y i = 1 ∧ x i ≠ 1 := by
    intro i hV
    have hV2 : 0 < V i ^ 2 := by positivity
    have hyz : y i ≠ z i := by
      intro h
      have := congrArg (fun t : Fin 3 => ((t : ℕ) : ℝ)) h
      simp only [hy, hz] at this
      apply hbc
      have : (b - c) * V i = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact h1
      · exact absurd h1 hV
    refine ⟨mid (x i) (y i) (z i) ?_, ?_⟩
    · rw [hx, hy, hz]
      have : (B i + b * V i - (B i + a * V i)) * (B i + b * V i - (B i + c * V i))
          = (b - a) * (b - c) * V i ^ 2 := by ring
      rw [this]; exact mul_neg_of_neg_of_pos hneg hV2
    · intro h1
      have := notmid (x i) (y i) (z i) h1 hyz
      rw [hx, hy, hz] at this
      have e : (B i + a * V i - (B i + b * V i)) * (B i + a * V i - (B i + c * V i))
          = (a - b) * (a - c) * V i ^ 2 := by ring
      rw [e] at this
      have := mul_pos hpos hV2
      linarith
  have hfix : ∀ i, V i = 0 → x i = y i := by
    intro i hV
    apply cast_inj
    rw [hx, hy, hV]; ring
  unfold ones
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
    have hV : V i ≠ 0 := fun h => hi (hfix i h)
    obtain ⟨h1, h2⟩ := hmove i hV
    exact ⟨i, by simp [h1], by simp [h2]⟩
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    by_cases hV : V i = 0
    · rw [← hfix i hV]; exact hi
    · exact absurd hi (hmove i hV).2

lemma linefree {n m : ℕ} (x y z : Fin n → Fin 3) (hx : ones x = m) (hy : ones y = m)
    (hz : ones z = m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ¬ Collinear ℝ ({fun i => ((x i : ℕ) : ℝ), fun i => ((y i : ℕ) : ℝ),
        fun i => ((z i : ℕ) : ℝ)} : Set (Fin n → ℝ)) := by
  intro hcol
  obtain ⟨X, hX⟩ : ∃ X : Fin n → ℝ, X = fun i => ((x i : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hX] at hcol
  rw [collinear_iff_of_mem (p₀ := X) (Set.mem_insert _ _)] at hcol
  obtain ⟨V, hV⟩ := hcol
  obtain ⟨a, ha⟩ := hV X (Set.mem_insert _ _)
  obtain ⟨b, hb⟩ := hV (fun i => ((y i : ℕ) : ℝ)) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  obtain ⟨c, hc⟩ := hV (fun i => ((z i : ℕ) : ℝ))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have ex : ∀ i, ((x i : ℕ) : ℝ) = X i + a * V i := by
    intro i; have := congrFun ha i; have h0 := congrFun hX i
    simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this h0; linarith
  have ey : ∀ i, ((y i : ℕ) : ℝ) = X i + b * V i := by
    intro i; have := congrFun hb i; simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at this; linarith
  have ez : ∀ i, ((z i : ℕ) : ℝ) = X i + c * V i := by
    intro i; have := congrFun hc i; simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at this; linarith
  have neq : ∀ (u w : Fin n → Fin 3) (s t : ℝ), (∀ i, ((u i : ℕ) : ℝ) = X i + s * V i) →
      (∀ i, ((w i : ℕ) : ℝ) = X i + t * V i) → u ≠ w → s ≠ t := by
    intro u w s t hu hw huw hst
    apply huw; funext i; apply cast_inj; rw [hu, hw, hst]
  have hab := neq x y a b ex ey hxy
  have hac := neq x z a c ex ez hxz
  have hbc := neq y z b c ey ez hyz
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  have hac' : a - c ≠ 0 := sub_ne_zero.2 hac
  have hbc' : b - c ≠ 0 := sub_ne_zero.2 hbc
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
  · -- a < b < c : middle b
    have := key x y z X V a b c ex ey ez (by nlinarith) hxy; omega
  · -- a < c < b : middle c
    have := key x z y X V a c b ex ez ey (by nlinarith) hxz; omega
  · linarith
  · -- c < a < b : middle a
    have := key y x z X V b a c ey ex ez (by nlinarith) (Ne.symm hxy); omega
  · -- b < a < c : middle a
    have := key y x z X V b a c ey ex ez (by nlinarith) (Ne.symm hxy); omega
  · linarith
  · -- b < c < a : middle c
    have := key x z y X V a c b ex ez ey (by nlinarith) hxz; omega
  · -- c < b < a : middle b
    have := key x y z X V a b c ex ey ez (by nlinarith) hxy; omega

/-- the map from (S, T ⊆ Sᶜ) to strings -/
def g {n : ℕ} (p : Σ _ : Finset (Fin n), Finset (Fin n)) : Fin n → Fin 3 :=
  fun i => if i ∈ p.1 then 1 else if i ∈ p.2 then 2 else 0

lemma g_one {n : ℕ} (p : Σ _ : Finset (Fin n), Finset (Fin n)) (i : Fin n) :
    g p i = 1 ↔ i ∈ p.1 := by
  unfold g; split_ifs with h1 h2 <;> simp_all

lemma g_two {n : ℕ} (p : Σ _ : Finset (Fin n), Finset (Fin n)) (hp : Disjoint p.1 p.2)
    (i : Fin n) : g p i = 2 ↔ i ∈ p.2 := by
  unfold g; split_ifs with h1 h2
  · simp only [show (1 : Fin 3) ≠ 2 by decide, false_iff]
    exact Finset.disjoint_left.1 hp h1
  · simp [h2]
  · simp [h2]

lemma card_A (n m : ℕ) :
    n.choose m * 2 ^ (n - m) ≤ (univ.filter (fun v : Fin n → Fin 3 => ones v = m)).card := by
  classical
  let D := (powersetCard m (univ : Finset (Fin n))).sigma (fun S => (univ \ S).powerset)
  have hD : D.card = n.choose m * 2 ^ (n - m) := by
    simp only [D, card_sigma, card_powerset]
    rw [Finset.sum_congr rfl (g := fun _ => 2 ^ (n - m))]
    · simp
    · intro S hS
      rw [mem_powersetCard] at hS
      rw [Finset.card_sdiff_of_subset hS.1]
      simp [hS.2]
  have hdisj : ∀ p ∈ D, Disjoint p.1 p.2 := by
    intro p hp
    simp only [D, mem_sigma, mem_powerset] at hp
    exact Finset.disjoint_of_subset_right hp.2 Finset.disjoint_sdiff
  rw [← hD]
  apply Finset.card_le_card_of_injOn g
  · intro p hp
    refine Finset.mem_filter.2 ⟨mem_univ _, ?_⟩
    have : univ.filter (fun i => g p i = 1) = p.1 := by
      ext i; simp [g_one]
    unfold ones; rw [this]
    rw [Finset.mem_coe, Finset.mem_sigma, mem_powersetCard] at hp
    exact hp.1.2
  · intro p hp q hq hpq
    have hpq' : ∀ i, g p i = g q i := fun i => congrFun hpq i
    have h1 : p.1 = q.1 := by
      ext i; rw [← g_one, ← g_one, hpq']
    have h2 : p.2 = q.2 := by
      ext i; rw [← g_two p (hdisj p hp), ← g_two q (hdisj q hq), hpq']
    rcases p with ⟨S, T⟩
    rcases q with ⟨S', T'⟩
    simp only at h1 h2
    subst h1 h2
    rfl

lemma f3_ge (n m : ℕ) : n.choose m * 2 ^ (n - m) ≤ Erdos185.f3 n := by
  refine (card_A n m).trans ?_
  unfold Erdos185.f3
  apply le_csSup
  · refine ⟨3 ^ n, ?_⟩
    rintro k ⟨A, -, rfl⟩
    calc A.card ≤ (univ : Finset (Fin n → Fin 3)).card := Finset.card_le_univ A
      _ = 3 ^ n := by simp
  · refine ⟨_, ?_, rfl⟩
    intro x hx y hy z hz hxy hxz hyz
    simp only [mem_filter, mem_univ, true_and] at hx hy hz
    exact linefree x y z hx hy hz hxy hxz hyz

lemma choose_step (m : ℕ) :
    (3 * (m + 1)).choose (m + 1) * ((m + 1) * (2 * m + 2) * (2 * m + 1)) =
      (3 * m).choose m * ((3 * m + 3) * (3 * m + 2) * (3 * m + 1)) := by
  have e1 := Nat.choose_mul_factorial_mul_factorial (show m + 1 ≤ 3 * (m + 1) by omega)
  have e2 := Nat.choose_mul_factorial_mul_factorial (show m ≤ 3 * m by omega)
  rw [show 3 * (m + 1) - (m + 1) = 2 * m + 2 by omega] at e1
  rw [show 3 * m - m = 2 * m by omega] at e2
  rw [show 3 * (m + 1) = 3 * m + 2 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ, show 2 * m + 2 = 2 * m + 1 + 1 by ring, Nat.factorial_succ,
    Nat.factorial_succ, Nat.factorial_succ] at e1
  rw [show 3 * m + 2 + 1 = 3 * (m + 1) by ring] at e1
  have hpos : 0 < m.factorial * (2 * m).factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (3 * (m + 1)).choose (m + 1) * ((m + 1) * (2 * m + 2) * (2 * m + 1)) *
        (m.factorial * (2 * m).factorial)
      = (3 * (m + 1)).choose (m + 1) * ((m + 1) * m.factorial) *
          ((2 * m + 1 + 1) * ((2 * m + 1) * (2 * m).factorial)) := by ring
    _ = (3 * m + 2 + 1) * ((3 * m + 1 + 1) * ((3 * m + 1) * (3 * m).factorial)) := by
        rw [e1]; ring
    _ = (3 * m).choose m * ((3 * m + 3) * (3 * m + 2) * (3 * m + 1)) *
          (m.factorial * (2 * m).factorial) := by
        rw [← e2]; ring

lemma growth (m : ℕ) (hm : 1 ≤ m) :
    729 ^ m ≤ 6 * m * ((3 * m).choose m * 4 ^ m) ^ 2 := by
  induction m, hm using Nat.le_induction with
  | base => simp [Nat.choose]
  | succ m hm ih =>
    set c := (3 * m).choose m
    set c' := (3 * (m + 1)).choose (m + 1)
    set D := (m + 1) * (2 * m + 2) * (2 * m + 1)
    set E := (3 * m + 3) * (3 * m + 2) * (3 * m + 1)
    have hid : c' * D = c * E := choose_step m
    have hpoly : 729 * m * D ^ 2 ≤ 16 * (m + 1) * E ^ 2 := by
      have : 16 * (m + 1) * E ^ 2 = 729 * m * D ^ 2 +
          36 * (m + 1) ^ 3 * (63 * m ^ 2 + 63 * m + 16) := by
        simp only [D, E]; ring
      omega
    have hD : 0 < D ^ 2 := by positivity
    apply Nat.le_of_mul_le_mul_right _ hD
    calc 729 ^ (m + 1) * D ^ 2 = 729 * 729 ^ m * D ^ 2 := by ring
      _ ≤ 729 * (6 * m * (c * 4 ^ m) ^ 2) * D ^ 2 := by gcongr
      _ = 6 * c ^ 2 * 16 ^ m * (729 * m * D ^ 2) := by
          rw [show (16 : ℕ) ^ m = (4 ^ m) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
          ring
      _ ≤ 6 * c ^ 2 * 16 ^ m * (16 * (m + 1) * E ^ 2) := by gcongr
      _ = 6 * (m + 1) * (16 * 16 ^ m) * (c * E) ^ 2 := by ring
      _ = 6 * (m + 1) * (16 * 16 ^ m) * (c' * D) ^ 2 := by rw [hid]
      _ = 6 * (m + 1) * (c' * 4 ^ (m + 1)) ^ 2 * D ^ 2 := by
          rw [show (16 : ℕ) ^ m = (4 ^ m) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
          ring

lemma main_nat (n : ℕ) (hn : 3 ≤ n) : 9 ^ n ≤ 169 * n * (Erdos185.f3 n) ^ 2 := by
  set m := n / 3 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hm3 : 3 * m ≤ n := by omega
  have hn3 : n ≤ 3 * m + 2 := by omega
  have hT : (3 * m).choose m * 4 ^ m ≤ Erdos185.f3 n := by
    refine le_trans ?_ (f3_ge n m)
    apply Nat.mul_le_mul (Nat.choose_le_choose m hm3)
    rw [show (4 : ℕ) ^ m = 2 ^ (2 * m) by rw [pow_mul]; norm_num]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hg := growth m hm1
  calc 9 ^ n ≤ 9 ^ (3 * m + 2) := Nat.pow_le_pow_right (by norm_num) hn3
    _ = 81 * 729 ^ m := by rw [pow_add, pow_mul]; norm_num; ring
    _ ≤ 81 * (6 * m * ((3 * m).choose m * 4 ^ m) ^ 2) := by gcongr
    _ ≤ 81 * (6 * m * (Erdos185.f3 n) ^ 2) := by gcongr
    _ = 162 * (3 * m) * (Erdos185.f3 n) ^ 2 := by ring
    _ ≤ 169 * n * (Erdos185.f3 n) ^ 2 := by gcongr <;> omega

end OMAMoser

theorem OMA.solution : type_of% @Erdos185.erdos_185.variants.moser := by
  refine Asymptotics.IsBigO.of_bound 13 (eventually_atTop.2 ⟨3, fun n hn => ?_⟩)
  have h := OMAMoser.main_nat n hn
  have hR : (9 : ℝ) ^ n ≤ 169 * n * (Erdos185.f3 n : ℝ) ^ 2 := by exact_mod_cast h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hnpos.le
  have hF : (0 : ℝ) ≤ Erdos185.f3 n := by positivity
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hF, div_le_iff₀ hs]
  have h9 : (9 : ℝ) ^ n = ((3 : ℝ) ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  by_contra hcon
  push Not at hcon
  have h0 : 0 ≤ 13 * (Erdos185.f3 n : ℝ) * √(n : ℝ) := by positivity
  have := mul_self_lt_mul_self h0 hcon
  nlinarith [hsq]
