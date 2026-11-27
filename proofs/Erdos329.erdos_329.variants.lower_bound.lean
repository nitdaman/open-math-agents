import FormalConjectures.ErdosProblems.«329»

-- Problem: Erdős Problem 329: Maximum Density of Sidon Sets — lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/329.lean:64 (declaration Erdos329.erdos_329.variants.lower_bound)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter

namespace OMA329

def Sid (Q : ℕ → Prop) : Prop := ∀ a b c d, Q a → Q b → Q c → Q d → a + b = c + d →
  (a = c ∧ b = d) ∨ (a = d ∧ b = c)

lemma combine (p : ℕ) (hp : 1 ≤ p) (S B : ℕ → Prop) (hS : ∀ x, S x → x < p)
    (hB : ∀ x, B x → 2 * p ^ 2 ≤ x ∧ x + p + 1 ≤ 4 * p ^ 2)
    (hgap : ∀ x y, B x → B y → x < y + p → y < x + p → x = y)
    (sS : Sid S) (sB : Sid B) : Sid (fun x => S x ∨ B x) := by
  have hpp : p ≤ p ^ 2 := by nlinarith
  intro a b c d ha hb hc hd h
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    rcases hd with hd | hd
  all_goals first
    | exact sS _ _ _ _ ha hb hc hd h
    | exact sB _ _ _ _ ha hb hc hd h
    | skip
  all_goals
    try have ha' := hS _ ha
    try have ha' := hB _ ha
    try have hb' := hS _ hb
    try have hb' := hB _ hb
    try have hc' := hS _ hc
    try have hc' := hB _ hc
    try have hd' := hS _ hd
    try have hd' := hB _ hd
    try have e1 := hgap a c ha hc (by omega) (by omega)
    try have e2 := hgap a d ha hd (by omega) (by omega)
    try have e3 := hgap b c hb hc (by omega) (by omega)
    try have e4 := hgap b d hb hd (by omega) (by omega)
    generalize p ^ 2 = q at *
    omega

def blk (p : ℕ) (x : ℕ) : Prop := ∃ k < p, x = 2 * p ^ 2 + 2 * p * k + k ^ 2 % p

lemma blk_bounds (p : ℕ) (hp : 1 ≤ p) (x : ℕ) (h : blk p x) :
    2 * p ^ 2 ≤ x ∧ x + p + 1 ≤ 4 * p ^ 2 := by
  obtain ⟨k, hk, rfl⟩ := h
  have hr : k ^ 2 % p < p := Nat.mod_lt _ (by omega)
  have : p * (k + 1) ≤ p * p := Nat.mul_le_mul_left _ hk
  constructor
  · omega
  · nlinarith

lemma blk_gap (p : ℕ) (hp : 1 ≤ p) (x y : ℕ) (hx : blk p x) (hy : blk p y)
    (h1 : x < y + p) (h2 : y < x + p) : x = y := by
  obtain ⟨k, hk, rfl⟩ := hx
  obtain ⟨l, hl, rfl⟩ := hy
  have hr1 : k ^ 2 % p < p := Nat.mod_lt _ (by omega)
  have hr2 : l ^ 2 % p < p := Nat.mod_lt _ (by omega)
  rcases lt_trichotomy k l with h | rfl | h
  · have : 2 * p * (k + 1) ≤ 2 * p * l := Nat.mul_le_mul_left _ h
    simp only [mul_add, mul_one] at this
    generalize k ^ 2 % p = r1 at *
    generalize l ^ 2 % p = r2 at *
    omega
  · rfl
  · have : 2 * p * (l + 1) ≤ 2 * p * k := Nat.mul_le_mul_left _ h
    simp only [mul_add, mul_one] at this
    generalize k ^ 2 % p = r1 at *
    generalize l ^ 2 % p = r2 at *
    omega

lemma zmod_key {p : ℕ} [Fact p.Prime] {a b c d : ZMod p} (two : (2 : ZMod p) ≠ 0)
    (h1 : a + b = c + d) (h2 : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h3 : 2 * (a * b) = 2 * (c * d) := by linear_combination (a + b + c + d) * h1 - h2
  have hab : a * b = c * d := mul_left_cancel₀ two h3
  have h4 : (a - c) * (a - d) = 0 := by linear_combination a * h1 - hab
  rcases mul_eq_zero.1 h4 with h | h
  · left
    have : a = c := sub_eq_zero.1 h
    subst this
    exact ⟨rfl, add_left_cancel h1⟩
  · right
    have : a = d := sub_eq_zero.1 h
    subst this
    refine ⟨rfl, ?_⟩
    have : a + b = a + c := by rw [h1, add_comm]
    exact add_left_cancel this

lemma blk_sid (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : Sid (blk p) := by
  haveI := Fact.mk hp
  intro a b c d ⟨k1, hk1, ha⟩ ⟨k2, hk2, hb⟩ ⟨k3, hk3, hc⟩ ⟨k4, hk4, hd⟩ h
  subst ha hb hc hd
  have hp0 : 0 < p := hp.pos
  have r1 := Nat.mod_lt (k1 ^ 2) hp0
  have r2 := Nat.mod_lt (k2 ^ 2) hp0
  have r3 := Nat.mod_lt (k3 ^ 2) hp0
  have r4 := Nat.mod_lt (k4 ^ 2) hp0
  generalize hR1 : k1 ^ 2 % p = R1 at *
  generalize hR2 : k2 ^ 2 % p = R2 at *
  generalize hR3 : k3 ^ 2 % p = R3 at *
  generalize hR4 : k4 ^ 2 % p = R4 at *
  have hs : k1 + k2 = k3 + k4 := by
    rcases lt_trichotomy (k1 + k2) (k3 + k4) with hl | hl | hl
    · have := Nat.mul_le_mul_left (2 * p) (Nat.succ_le_of_lt hl)
      simp only [Nat.succ_eq_add_one, mul_add, mul_one] at this
      omega
    · exact hl
    · have := Nat.mul_le_mul_left (2 * p) (Nat.succ_le_of_lt hl)
      simp only [Nat.succ_eq_add_one, mul_add, mul_one] at this
      omega
  have hr : R1 + R2 = R3 + R4 := by
    have : 2 * p * (k1 + k2) = 2 * p * (k3 + k4) := by rw [hs]
    simp only [mul_add] at this
    omega
  subst hR1 hR2 hR3 hR4
  have e1 : ((k1 : ZMod p) + k2) = k3 + k4 := by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) hs
  have e2 : ((k1 : ZMod p) ^ 2 + k2 ^ 2) = k3 ^ 2 + k4 ^ 2 := by
    have := congrArg (Nat.cast : ℕ → ZMod p) hr
    simp only [Nat.cast_add, ZMod.natCast_mod, Nat.cast_pow] at this
    exact this
  have two : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    omega
  have inj : ∀ i j, i < p → j < p → (i : ZMod p) = j → i = j := fun i j hi hj e => by
    have := congrArg ZMod.val e
    rwa [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at this
  rcases zmod_key two e1 e2 with ⟨h13, _⟩ | ⟨h14, _⟩
  · have := inj _ _ hk1 hk3 h13
    subst this
    have : k2 = k4 := by omega
    subst this
    left; exact ⟨rfl, rfl⟩
  · have := inj _ _ hk1 hk4 h14
    subst this
    have : k2 = k3 := by omega
    subst this
    right; exact ⟨rfl, rfl⟩

noncomputable def P : ℕ → ℕ
  | 0 => 3
  | n + 1 => Classical.choose (Nat.exists_infinite_primes (4 * P n ^ 2 + 1))

lemma P_spec (n : ℕ) : 4 * P n ^ 2 + 1 ≤ P (n + 1) ∧ (P (n + 1)).Prime :=
  Classical.choose_spec (Nat.exists_infinite_primes _)

lemma P_prime : ∀ n, (P n).Prime
  | 0 => Nat.prime_three
  | n + 1 => (P_spec n).2

lemma P_ge3 : ∀ n, 3 ≤ P n
  | 0 => le_rfl
  | n + 1 => by have := (P_spec n).1; have := P_ge3 n; nlinarith

lemma P_mono : Monotone P :=
  monotone_nat_of_le_succ fun n => by have := (P_spec n).1; have := P_ge3 n; nlinarith

lemma P_lt (n m : ℕ) (h : n < m) : 4 * P n ^ 2 < P m :=
  lt_of_lt_of_le (by have := (P_spec n).1; omega) (P_mono (show n + 1 ≤ m from h))

lemma P_ge_n : ∀ n, n ≤ P n
  | 0 => Nat.zero_le _
  | n + 1 => by have := (P_spec n).1; have := P_ge_n n; nlinarith

lemma sid_le (m : ℕ) : Sid (fun x => ∃ n ≤ m, blk (P n) x) := by
  induction m with
  | zero =>
    have : (fun x => ∃ n ≤ 0, blk (P n) x) = blk (P 0) := by
      funext x; apply propext; constructor
      · rintro ⟨n, hn, h⟩
        obtain rfl : n = 0 := by omega
        exact h
      · intro h; exact ⟨0, le_rfl, h⟩
    rw [this]
    exact blk_sid _ (P_prime 0) (by have := P_ge3 0; omega)
  | succ m ih =>
    have h1 : 1 ≤ P (m + 1) := by have := P_ge3 (m + 1); omega
    have hc := combine (P (m + 1)) h1 _ _
      (fun x ⟨n, hn, hx⟩ => by
        have := (blk_bounds _ (by have := P_ge3 n; omega) x hx).2
        have := P_lt n (m + 1) (by omega)
        omega)
      (blk_bounds _ h1) (blk_gap _ h1) ih
      (blk_sid _ (P_prime _) (by have := P_ge3 (m + 1); omega))
    have conv : ∀ x, (∃ n ≤ m + 1, blk (P n) x) → (∃ n ≤ m, blk (P n) x) ∨ blk (P (m + 1)) x := by
      rintro x ⟨n, hn, h⟩
      by_cases hnm : n ≤ m
      · exact Or.inl ⟨n, hnm, h⟩
      · obtain rfl : n = m + 1 := by omega
        exact Or.inr h
    intro a b c d ha hb hc' hd h
    exact hc a b c d (conv _ ha) (conv _ hb) (conv _ hc') (conv _ hd) h

def A : Set ℕ := {x | ∃ n, blk (P n) x}

lemma A_sidon : IsSidon A := by
  intro i1 h1 j1 h2 i2 h3 j2 h4 h
  obtain ⟨n1, h1⟩ := h1
  obtain ⟨n2, h2⟩ := h2
  obtain ⟨n3, h3⟩ := h3
  obtain ⟨n4, h4⟩ := h4
  exact sid_le (max (max n1 n2) (max n3 n4)) i1 i2 j1 j2
    ⟨n1, by omega, h1⟩ ⟨n3, by omega, h3⟩ ⟨n2, by omega, h2⟩ ⟨n4, by omega, h4⟩ h

lemma sidon_bound (B : Set ℕ) (hB : IsSidon B) (N : ℕ) :
    Erdos329.sqrtPartialDensity B N ≤ 3 := by
  unfold Erdos329.sqrtPartialDensity
  have hfin : (B ∩ Set.Icc 1 N).Finite := (Set.finite_Icc 1 N).subset Set.inter_subset_right
  rw [Set.ncard_eq_toFinset_card _ hfin]
  set s := hfin.toFinset with hs
  have hmem : ∀ x, x ∈ s ↔ x ∈ B ∧ 1 ≤ x ∧ x ≤ N := by
    intro x; rw [hs, Set.Finite.mem_toFinset]; simp
  have hcard : s.offDiag.card ≤ (Finset.Icc (-(N : ℤ)) N).card := by
    apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ => (q.2 : ℤ) - q.1)
    · intro q hq
      rw [Finset.mem_coe, Finset.mem_offDiag] at hq
      simp only [Finset.mem_coe, Finset.mem_Icc]
      have := (hmem _).1 hq.1
      have := (hmem _).1 hq.2.1
      constructor <;> omega
    · intro q hq q' hq' e
      simp only [Finset.mem_coe, Finset.mem_offDiag] at hq hq'
      simp only at e
      have e' : q.2 + q'.1 = q'.2 + q.1 := by omega
      rcases hB q.2 ((hmem _).1 hq.2.1).1 q'.2 ((hmem _).1 hq'.2.1).1 q'.1
        ((hmem _).1 hq'.1).1 q.1 ((hmem _).1 hq.1).1 e' with ⟨x1, x2⟩ | ⟨x1, x2⟩
      · exact Prod.ext x2.symm x1
      · exact absurd x1.symm hq.2.2
  rw [Finset.offDiag_card, Int.card_Icc] at hcard
  have hk : s.card * s.card ≤ 2 * N + 1 + s.card := by omega
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hk2 : s.card ^ 2 ≤ 9 * N := by
    rcases le_or_gt s.card 3 with h3 | h3
    · nlinarith
    · nlinarith
  have hsq : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  rw [div_le_iff₀ hsq]
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have hk3 : ((s.card : ℝ)) ^ 2 ≤ 9 * (N : ℝ) := by exact_mod_cast hk2
  have hk0 : (0 : ℝ) ≤ s.card := by positivity
  nlinarith

lemma density (n : ℕ) : 1 / 2 ≤ Erdos329.sqrtPartialDensity A (4 * P n ^ 2) := by
  unfold Erdos329.sqrtPartialDensity
  set p := P n with hpdef
  have hp3 : 3 ≤ p := P_ge3 n
  let f : ℕ → ℕ := fun k => 2 * p ^ 2 + 2 * p * k + k ^ 2 % p
  have finj : Function.Injective f := by
    intro k l e
    simp only [f] at e
    have hr1 : k ^ 2 % p < p := Nat.mod_lt _ (by omega)
    have hr2 : l ^ 2 % p < p := Nat.mod_lt _ (by omega)
    rcases lt_trichotomy k l with h | h | h
    · have : 2 * p * (k + 1) ≤ 2 * p * l := Nat.mul_le_mul_left _ h
      simp only [mul_add, mul_one] at this
      generalize k ^ 2 % p = r1 at *
      generalize l ^ 2 % p = r2 at *
      omega
    · exact h
    · have : 2 * p * (l + 1) ≤ 2 * p * k := Nat.mul_le_mul_left _ h
      simp only [mul_add, mul_one] at this
      generalize k ^ 2 % p = r1 at *
      generalize l ^ 2 % p = r2 at *
      omega
  have hfin : (A ∩ Set.Icc 1 (4 * p ^ 2)).Finite :=
    (Set.finite_Icc _ _).subset Set.inter_subset_right
  have hsub : (((Finset.range p).image f : Finset ℕ) : Set ℕ) ⊆ A ∩ Set.Icc 1 (4 * p ^ 2) := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hb : blk p (f k) := ⟨k, hk, rfl⟩
    have := blk_bounds p (by omega) _ hb
    refine ⟨⟨n, hb⟩, ?_, ?_⟩
    · have : 1 ≤ p ^ 2 := by nlinarith
      omega
    · omega
  have hle := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ finj, Finset.card_range] at hle
  have hsq : Real.sqrt ((4 * p ^ 2 : ℕ) : ℝ) = 2 * p := by
    rw [show ((4 * p ^ 2 : ℕ) : ℝ) = (2 * p) ^ 2 by push_cast; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq, le_div_iff₀ (by positivity)]
  have : (p : ℝ) ≤ (A ∩ Set.Icc 1 (4 * p ^ 2)).ncard := by exact_mod_cast hle
  linarith

end OMA329

theorem OMA.solution : type_of% @Erdos329.erdos_329.variants.lower_bound := by
  refine ⟨OMA329.A, OMA329.A_sidon, ?_⟩
  unfold Erdos329.sidonUpperDensity
  apply le_limsup_of_frequently_le
  · rw [Filter.frequently_atTop]
    intro a
    refine ⟨4 * OMA329.P a ^ 2, ?_, OMA329.density a⟩
    have := OMA329.P_ge_n a
    nlinarith
  · exact isBoundedUnder_of ⟨3, fun N => OMA329.sidon_bound _ OMA329.A_sidon N⟩
