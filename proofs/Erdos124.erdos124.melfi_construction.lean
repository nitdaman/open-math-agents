import FormalConjectures.ErdosProblems.«124»

-- Problem: Erdős Problem 124 — melfi construction
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/124.lean:108 (declaration Erdos124.erdos124.melfi_construction)
-- Credit: @Rahul-007afk (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- Brown's criterion: if each term is at most one more than the sum of the earlier ones, every
number up to an initial sum is a sum of distinct earlier terms. -/
lemma OMA.brown (u : ℕ → ℕ) (hu : ∀ T, u T ≤ 1 + ∑ s ∈ Finset.range T, u s) :
    ∀ T n, n ≤ ∑ s ∈ Finset.range T, u s →
      ∃ S : Finset ℕ, S ⊆ Finset.range T ∧ ∑ s ∈ S, u s = n := by
  intro T
  induction T with
  | zero =>
    intro n hn
    rw [Finset.sum_range_zero] at hn
    have hn0 : n = 0 := by omega
    exact ⟨∅, Finset.empty_subset _, by rw [Finset.sum_empty, hn0]⟩
  | succ T ih =>
    intro n hn
    rw [Finset.sum_range_succ] at hn
    by_cases hle : n ≤ ∑ s ∈ Finset.range T, u s
    · obtain ⟨S, hS, hsum⟩ := ih n hle
      refine ⟨S, fun x hx => ?_, hsum⟩
      have := hS hx
      rw [Finset.mem_range] at this ⊢
      omega
    · have h1 := hu T
      obtain ⟨S, hS, hsum⟩ := ih (n - u T) (by omega)
      have hT : T ∉ S := fun h => by
        have := hS h
        rw [Finset.mem_range] at this
        omega
      refine ⟨insert T S, fun x hx => ?_, ?_⟩
      · rw [Finset.mem_insert] at hx
        rw [Finset.mem_range]
        rcases hx with rfl | hx
        · omega
        · have := hS hx
          rw [Finset.mem_range] at this
          omega
      · rw [Finset.sum_insert hT, hsum]
        omega

lemma OMA.pow_succ_le (K t : ℕ) :
    (t + 1) ^ (K + 1) ≤ t ^ (K + 1) + (K + 1) * (t + 1) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h1 : t ^ (K + 1) ≤ (t + 1) ^ (K + 1) := Nat.pow_le_pow_left (Nat.le_succ t) _
    have h2 : (t + 1) ^ (K + 1 + 1) = (t + 1) ^ (K + 1) * (t + 1) := pow_succ _ _
    have h3 := Nat.mul_le_mul_right (t + 1) ih
    have h4 : (t ^ (K + 1) + (K + 1) * (t + 1) ^ K) * (t + 1) =
        t ^ (K + 1 + 1) + t ^ (K + 1) + (K + 1) * (t + 1) ^ (K + 1) := by ring
    have h5 : (K + 1 + 1) * (t + 1) ^ (K + 1) =
        (K + 1) * (t + 1) ^ (K + 1) + (t + 1) ^ (K + 1) := by ring
    omega

/-- Consecutive `K`-th powers at most double once the base is at least `2 K`. -/
lemma OMA.doubling (K t : ℕ) (h : 2 * (K + 1) ≤ t + 1) :
    (t + 1) ^ (K + 1) ≤ 2 * t ^ (K + 1) := by
  have h1 := OMA.pow_succ_le K t
  have h2 : 2 * ((K + 1) * (t + 1) ^ K) ≤ (t + 1) * (t + 1) ^ K := by
    rw [← mul_assoc]
    exact Nat.mul_le_mul_right _ h
  have h3 : (t + 1) ^ (K + 1) = (t + 1) * (t + 1) ^ K := by ring
  omega

lemma OMA.claimA (K' μ : ℕ) (hμ : (2 * (K' + 1) + 1) ^ (K' + 1) ≤ μ) :
    ∀ t, (t + 2) ^ (K' + 1) ≤ 1 + μ + ∑ s ∈ Finset.range t, (s + 2) ^ (K' + 1) := by
  intro t
  induction t with
  | zero =>
    have h : 2 ^ (K' + 1) ≤ (2 * (K' + 1) + 1) ^ (K' + 1) := Nat.pow_le_pow_left (by omega) _
    have e : (0 + 2) ^ (K' + 1) = 2 ^ (K' + 1) := by norm_num
    rw [Finset.sum_range_zero, e]
    omega
  | succ t ih =>
    rw [Finset.sum_range_succ]
    by_cases h : t + 3 ≤ 2 * (K' + 1) + 1
    · have h1 : (t + 1 + 2) ^ (K' + 1) ≤ (2 * (K' + 1) + 1) ^ (K' + 1) :=
        Nat.pow_le_pow_left (by omega) _
      omega
    · have h1 := OMA.doubling K' (t + 2) (by omega)
      have h2 : t + 1 + 2 = t + 2 + 1 := by omega
      rw [h2]
      omega

/-- The normalised sequence: `μ` ones, followed by the `K`-th powers `2 ^ K, 3 ^ K, …`. -/
def OMA.u (K μ s : ℕ) : ℕ := if s < μ then 1 else (s - μ + 2) ^ K

lemma OMA.u_pos (K μ s : ℕ) : 1 ≤ OMA.u K μ s := by
  by_cases hs : s < μ
  · rw [OMA.u, if_pos hs]
  · rw [OMA.u, if_neg hs]
    have : 0 < (s - μ + 2) ^ K := Nat.pow_pos (by omega)
    omega

/-- With enough ones in front, the sequence satisfies Brown's criterion. -/
lemma OMA.crit (K' μ : ℕ) (hμ : (2 * (K' + 1) + 1) ^ (K' + 1) ≤ μ) :
    ∀ T, OMA.u (K' + 1) μ T ≤ 1 + ∑ s ∈ Finset.range T, OMA.u (K' + 1) μ s := by
  intro T
  by_cases hT : T < μ
  · rw [OMA.u, if_pos hT]
    omega
  · obtain ⟨t, rfl⟩ : ∃ t, T = μ + t := ⟨T - μ, by omega⟩
    rw [Finset.sum_range_add]
    have h0 : ∀ s ∈ Finset.range μ, OMA.u (K' + 1) μ s = 1 := fun s hs => by
      rw [OMA.u, if_pos (Finset.mem_range.1 hs)]
    have h1 : ∑ s ∈ Finset.range μ, OMA.u (K' + 1) μ s = μ := by
      rw [Finset.sum_congr rfl h0]
      simp
    have h2 : ∑ s ∈ Finset.range t, OMA.u (K' + 1) μ (μ + s) =
        ∑ s ∈ Finset.range t, (s + 2) ^ (K' + 1) :=
      Finset.sum_congr rfl (fun s _ => by
        rw [OMA.u, if_neg (by omega), Nat.add_sub_cancel_left])
    have h3 : OMA.u (K' + 1) μ (μ + t) = (t + 2) ^ (K' + 1) := by
      rw [OMA.u, if_neg (by omega), Nat.add_sub_cancel_left]
    rw [h1, h2, h3]
    have := OMA.claimA K' μ hμ t
    omega

/-- A large power of two all of whose `2 ^ s`-th roots, `s < μ`, are still at least `M`. -/
def OMA.gp (M μ : ℕ) : ℕ := 2 ^ (M * 2 ^ (μ - 1))

/-- The integers whose squares serve as bases: `μ` roots of `gp`, then the multiples of `gp`. -/
def OMA.iota (M μ s : ℕ) : ℕ :=
  if s < μ then 2 ^ (M * 2 ^ (μ - 1 - s)) else OMA.gp M μ * (s - μ + 2)

/-- The exponents used with those bases. -/
def OMA.expo (k μ s : ℕ) : ℕ := if s < μ then k * 2 ^ s else k

lemma OMA.iota_of_lt (M μ s : ℕ) (hs : s < μ) :
    OMA.iota M μ s = 2 ^ (M * 2 ^ (μ - 1 - s)) := by
  rw [OMA.iota, if_pos hs]

lemma OMA.iota_of_ge (M μ s : ℕ) (hs : ¬ s < μ) :
    OMA.iota M μ s = OMA.gp M μ * (s - μ + 2) := by
  rw [OMA.iota, if_neg hs]

lemma OMA.gp_gt (M μ : ℕ) : M < OMA.gp M μ := by
  have h1 : M < 2 ^ M := Nat.lt_two_pow_self
  have h2 : 2 ^ M ≤ 2 ^ (M * 2 ^ (μ - 1)) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right M (by positivity))
  rw [OMA.gp]
  omega

lemma OMA.iota_le (M μ s : ℕ) (hs : s < μ) : OMA.iota M μ s ≤ OMA.gp M μ := by
  rw [OMA.iota_of_lt M μ s hs, OMA.gp]
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_left M (Nat.pow_le_pow_right (by norm_num) (by omega)))

lemma OMA.iota_ge (M μ s : ℕ) : M ≤ OMA.iota M μ s := by
  by_cases hs : s < μ
  · rw [OMA.iota_of_lt M μ s hs]
    have h1 : M < 2 ^ M := Nat.lt_two_pow_self
    have h2 : 2 ^ M ≤ 2 ^ (M * 2 ^ (μ - 1 - s)) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right M (by positivity))
    omega
  · rw [OMA.iota_of_ge M μ s hs]
    have h1 := OMA.gp_gt M μ
    have h2 : OMA.gp M μ * 1 ≤ OMA.gp M μ * (s - μ + 2) := Nat.mul_le_mul_left _ (by omega)
    omega

lemma OMA.expo_ge (k μ s : ℕ) : k ≤ OMA.expo k μ s := by
  by_cases hs : s < μ
  · rw [OMA.expo, if_pos hs]
    exact Nat.le_mul_of_pos_right k (by positivity)
  · rw [OMA.expo, if_neg hs]

lemma OMA.iota_inj (M μ : ℕ) (hM : 1 ≤ M) : Function.Injective (OMA.iota M μ) := by
  intro s s' h
  have hgp : 0 < OMA.gp M μ := by
    have := OMA.gp_gt M μ
    omega
  by_cases hs : s < μ <;> by_cases hs' : s' < μ
  · rw [OMA.iota_of_lt M μ s hs, OMA.iota_of_lt M μ s' hs'] at h
    have h1 := Nat.pow_right_injective (le_refl 2) h
    have h2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < M) h1
    have h3 := Nat.pow_right_injective (le_refl 2) h2
    omega
  · have h1 := OMA.iota_le M μ s hs
    rw [h, OMA.iota_of_ge M μ s' hs'] at h1
    have h2 : OMA.gp M μ * 2 ≤ OMA.gp M μ * (s' - μ + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  · have h1 := OMA.iota_le M μ s' hs'
    rw [← h, OMA.iota_of_ge M μ s hs] at h1
    have h2 : OMA.gp M μ * 2 ≤ OMA.gp M μ * (s - μ + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [OMA.iota_of_ge M μ s hs, OMA.iota_of_ge M μ s' hs'] at h
    have h1 := Nat.eq_of_mul_eq_mul_left hgp h
    omega

/-- Every chosen power equals `gp ^ (2 k)` times the corresponding term of the normalised
sequence. -/
lemma OMA.value (M k μ s : ℕ) :
    (OMA.iota M μ s ^ 2) ^ OMA.expo k μ s = OMA.gp M μ ^ (2 * k) * OMA.u (2 * k) μ s := by
  by_cases hs : s < μ
  · rw [OMA.iota_of_lt M μ s hs, OMA.expo, if_pos hs, OMA.u, if_pos hs, OMA.gp, mul_one,
      ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    have h : 2 ^ (μ - 1 - s) * 2 ^ s = 2 ^ (μ - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← h]
    ring
  · rw [OMA.iota_of_ge M μ s hs, OMA.expo, if_neg hs, OMA.u, if_neg hs, ← pow_mul, mul_pow]

/-- The integers whose squares are used to fix the residue modulo `g`. -/
def OMA.fixIdx (g σ : ℕ) : ℕ := 1 + g * (σ + 1)

lemma OMA.fix_ne (M k μ σ s : ℕ) (hM : 1 ≤ M) (hk : k ≠ 0) :
    OMA.fixIdx (OMA.gp M μ ^ (2 * k)) σ ≠ OMA.iota M μ s := by
  have hgp := OMA.gp_gt M μ
  have hg : OMA.gp M μ ≤ OMA.gp M μ ^ (2 * k) := Nat.le_self_pow (by omega) _
  intro h
  rw [OMA.fixIdx] at h
  by_cases hs : s < μ
  · have h1 := OMA.iota_le M μ s hs
    have h2 : OMA.gp M μ ^ (2 * k) * 1 ≤ OMA.gp M μ ^ (2 * k) * (σ + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [OMA.iota_of_ge M μ s hs] at h
    have hd1 : OMA.gp M μ ∣ OMA.gp M μ ^ (2 * k) * (σ + 1) :=
      Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
    have hd2 : OMA.gp M μ ∣ 1 + OMA.gp M μ ^ (2 * k) * (σ + 1) := by
      rw [h]
      exact dvd_mul_right _ _
    have hd3 : OMA.gp M μ ∣ 1 := (Nat.dvd_add_left hd1).1 hd2
    have := Nat.le_of_dvd one_pos hd3
    omega

lemma OMA.fix_modEq (g k : ℕ) :
    ∀ ρ, (∑ σ ∈ Finset.range ρ, (OMA.fixIdx g σ ^ 2) ^ k) ≡ ρ [MOD g] := by
  intro ρ
  induction ρ with
  | zero => simp [Nat.ModEq]
  | succ ρ ih =>
    rw [Finset.sum_range_succ]
    have h0 : OMA.fixIdx g ρ ≡ 1 [MOD g] := by
      show (1 + g * (ρ + 1)) % g = 1 % g
      exact Nat.add_mul_mod_self_left 1 g (ρ + 1)
    have h1 : (OMA.fixIdx g ρ ^ 2) ^ k ≡ 1 [MOD g] := by
      have := (h0.pow 2).pow k
      simpa using this
    exact ih.add h1

/-- `n` is a sum of numbers `a i`, `i ∈ I`, where `a i` is a sum of distinct powers of
`(i + M) ^ 2` with exponents at least `k`. -/
def OMA.Rep (M k : ℕ) (I : Finset ℕ) (n : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, (∀ i ∈ I, a i ∈ Erdos124.sumsOfDistinctPowers ((i + M) ^ 2) k) ∧
    ∑ i ∈ I, a i = n

lemma OMA.Rep_union {M k : ℕ} {I₁ I₂ : Finset ℕ} {n₁ n₂ : ℕ} (hd : Disjoint I₁ I₂)
    (h₁ : OMA.Rep M k I₁ n₁) (h₂ : OMA.Rep M k I₂ n₂) :
    OMA.Rep M k (I₁ ∪ I₂) (n₁ + n₂) := by
  obtain ⟨a₁, ha₁, hs₁⟩ := h₁
  obtain ⟨a₂, ha₂, hs₂⟩ := h₂
  refine ⟨fun i => if i ∈ I₁ then a₁ i else a₂ i, ?_, ?_⟩
  · intro i hi
    by_cases h : i ∈ I₁
    · simp only [if_pos h]
      exact ha₁ i h
    · simp only [if_neg h]
      rcases Finset.mem_union.1 hi with h' | h'
      · exact absurd h' h
      · exact ha₂ i h'
  · rw [Finset.sum_union hd, ← hs₁, ← hs₂]
    congr 1
    · exact Finset.sum_congr rfl (fun i hi => by simp only [if_pos hi])
    · exact Finset.sum_congr rfl (fun i hi => by
        have hn : i ∉ I₁ := fun h => Finset.disjoint_left.1 hd h hi
        simp only [if_neg hn])

/-- An injective family of bases `ι s ^ 2` with exponents `J s ≥ k` represents the sum of the
corresponding powers. -/
lemma OMA.Rep_family {M k : ℕ} (ι J : ℕ → ℕ) (hM : ∀ s, M ≤ ι s) (hJ : ∀ s, k ≤ J s)
    (hinj : Function.Injective ι) (S : Finset ℕ) :
    OMA.Rep M k (S.image (fun s => ι s - M)) (∑ s ∈ S, (ι s ^ 2) ^ J s) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | insert s S hs ih =>
    rw [Finset.image_insert, Finset.sum_insert hs, Finset.insert_eq]
    refine OMA.Rep_union ?_ ?_ ih
    · rw [Finset.disjoint_singleton_left, Finset.mem_image]
      rintro ⟨s', hs', heq⟩
      have h1 := hM s
      have h2 := hM s'
      have h3 : ι s' = ι s := by omega
      exact hs (hinj h3 ▸ hs')
    · refine ⟨fun _ => (ι s ^ 2) ^ J s, ?_, by simp⟩
      intro i hi
      rw [Finset.mem_singleton] at hi
      subst hi
      refine ⟨{J s}, ?_, ?_⟩
      · intro j hj
        rw [Finset.mem_singleton] at hj
        rw [hj]
        exact hJ s
      · rw [Finset.sum_singleton, Nat.sub_add_cancel (hM s)]

/-- For each `k ≠ 0`, every sufficiently large integer is represented. -/
lemma OMA.complete (M k : ℕ) (hM : 2 ≤ M) (hk : k ≠ 0) :
    ∃ N₀, ∀ n, N₀ ≤ n → ∃ I, OMA.Rep M k I n := by
  obtain ⟨K', hK'⟩ : ∃ K', 2 * k = K' + 1 := ⟨2 * k - 1, by omega⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = (2 * (K' + 1) + 1) ^ (K' + 1) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = OMA.gp M μ ^ (2 * k) := ⟨_, rfl⟩
  have hgp := OMA.gp_gt M μ
  have hgg : OMA.gp M μ ≤ g := by
    rw [hg]
    exact Nat.le_self_pow (by omega) _
  have hgpos : 0 < g := by omega
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → ℕ,
      Φ = fun ρ => ∑ σ ∈ Finset.range ρ, (OMA.fixIdx g σ ^ 2) ^ k := ⟨_, rfl⟩
  refine ⟨Φ g, fun n hn => ?_⟩
  have hρ : n % g < g := Nat.mod_lt _ hgpos
  have hΦle : Φ (n % g) ≤ Φ g := by
    rw [hΦ]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hρ.le)
  have hmod : Φ (n % g) ≡ n [MOD g] := by
    have h1 := OMA.fix_modEq g k (n % g)
    have h2 : n % g ≡ n [MOD g] := Nat.mod_modEq n g
    rw [hΦ]
    exact h1.trans h2
  have hdvd : g ∣ n - Φ (n % g) := (Nat.modEq_iff_dvd' (by omega)).1 hmod
  obtain ⟨q, hq⟩ := hdvd
  -- the multiple `g * q` from Brown's criterion
  have hcrit := OMA.crit K' μ (le_of_eq hμ.symm)
  have hq' : q ≤ ∑ s ∈ Finset.range q, OMA.u (K' + 1) μ s := by
    have h1 : ∑ _s ∈ Finset.range q, 1 ≤ ∑ s ∈ Finset.range q, OMA.u (K' + 1) μ s :=
      Finset.sum_le_sum (fun s _ => OMA.u_pos (K' + 1) μ s)
    simpa using h1
  obtain ⟨S, -, hS⟩ := OMA.brown (OMA.u (K' + 1) μ) hcrit q q hq'
  have hval : ∑ s ∈ S, (OMA.iota M μ s ^ 2) ^ OMA.expo k μ s = g * q := by
    rw [← hS, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [OMA.value, hg, hK']
  have hrep1 : OMA.Rep M k (S.image (fun s => OMA.iota M μ s - M)) (g * q) := by
    rw [← hval]
    exact OMA.Rep_family (OMA.iota M μ) (OMA.expo k μ) (OMA.iota_ge M μ) (OMA.expo_ge k μ)
      (OMA.iota_inj M μ (by omega)) S
  -- the residue from the fixing terms
  have hfixM : ∀ σ, M ≤ OMA.fixIdx g σ := fun σ => by
    have h1 : g * 1 ≤ g * (σ + 1) := Nat.mul_le_mul_left _ (by omega)
    rw [OMA.fixIdx]
    omega
  have hfixinj : Function.Injective (OMA.fixIdx g) := by
    intro σ σ' h
    rw [OMA.fixIdx, OMA.fixIdx] at h
    have h1 : g * (σ + 1) = g * (σ' + 1) := by omega
    have h2 := Nat.eq_of_mul_eq_mul_left hgpos h1
    omega
  have hrep2 : OMA.Rep M k ((Finset.range (n % g)).image (fun σ => OMA.fixIdx g σ - M))
      (Φ (n % g)) := by
    rw [hΦ]
    exact OMA.Rep_family (OMA.fixIdx g) (fun _ => k) hfixM (fun _ => le_refl k) hfixinj
      (Finset.range (n % g))
  have hdisj : Disjoint ((Finset.range (n % g)).image (fun σ => OMA.fixIdx g σ - M))
      (S.image (fun s => OMA.iota M μ s - M)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hi1
    obtain ⟨s, -, hs⟩ := Finset.mem_image.1 hi2
    have h1 := hfixM σ
    have h2 := OMA.iota_ge M μ s
    have h3 : OMA.fixIdx g σ = OMA.iota M μ s := by omega
    rw [hg] at h3
    exact OMA.fix_ne M k μ σ s (by omega) hk h3
  have hfinal := OMA.Rep_union hdisj hrep2 hrep1
  have hn' : Φ (n % g) + g * q = n := by omega
  rw [hn'] at hfinal
  exact ⟨_, hfinal⟩

/-- The finite sums of `1 / ((i + M) ^ 2 - 1)` telescope. -/
lemma OMA.psum (M : ℕ) (hM : 2 ≤ M) :
    ∀ n : ℕ, ∑ i ∈ Finset.range n, ((((i + M) ^ 2 : ℕ) : ℝ) - 1)⁻¹ ≤
      1 / ((M : ℝ) - 1) - 1 / ((n : ℝ) + M - 1) := by
  intro n
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hx1 : (0 : ℝ) < (n : ℝ) + M - 1 := by linarith
    have hx0 : (0 : ℝ) < (n : ℝ) + M := by linarith
    have key : 1 / ((n : ℝ) + M - 1) - 1 / ((n : ℝ) + M) =
        1 / (((n : ℝ) + M - 1) * ((n : ℝ) + M)) := by
      rw [div_sub_div _ _ hx1.ne' hx0.ne']
      congr 1
      ring
    have hstep : ((((n + M) ^ 2 : ℕ) : ℝ) - 1)⁻¹ ≤
        1 / ((n : ℝ) + M - 1) - 1 / ((n : ℝ) + M) := by
      rw [key, inv_eq_one_div]
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      nlinarith
    have e3 : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + M - 1) = 1 / ((n : ℝ) + M) := by
      congr 1
      push_cast
      ring
    rw [e3]
    linarith

theorem OMA.solution : type_of% @Erdos124.erdos124.melfi_construction := by
  intro ε hε
  obtain ⟨M, hM2, hMε⟩ : ∃ M : ℕ, 2 ≤ M ∧ 1 / ((M : ℝ) - 1) ≤ ε := by
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
    refine ⟨m + 2, by omega, ?_⟩
    have h1 : 1 < (m : ℝ) * ε := by
      rw [div_lt_iff₀ hε] at hm
      exact hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hpos : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) - 1 := by
      push_cast
      linarith
    rw [div_le_iff₀ hpos]
    push_cast
    nlinarith
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hnonneg : ∀ i : ℕ, 0 ≤ ((((i + M) ^ 2 : ℕ) : ℝ) - 1)⁻¹ := by
    intro i
    apply inv_nonneg.2
    have h1 : (1 : ℝ) ≤ (((i + M) ^ 2 : ℕ) : ℝ) := by
      have : 1 ≤ (i + M) ^ 2 := Nat.one_le_pow _ _ (by omega)
      exact_mod_cast this
    linarith
  have hbound : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((((i + M) ^ 2 : ℕ) : ℝ) - 1)⁻¹ ≤ ε := by
    intro n
    have h1 := OMA.psum M hM2 n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : (0 : ℝ) ≤ 1 / ((n : ℝ) + M - 1) := div_nonneg zero_le_one (by linarith)
    linarith
  refine ⟨fun i => (i + M) ^ 2, ?_, ?_, ?_, ?_, ?_⟩
  · exact strictMono_nat_of_lt_succ (fun i => Nat.pow_lt_pow_left (by omega) (by norm_num))
  · show 2 ≤ (0 + M) ^ 2
    have : M ≤ (0 + M) ^ 2 := by
      rw [Nat.zero_add]
      exact Nat.le_self_pow (by norm_num) M
    omega
  · exact summable_of_sum_range_le hnonneg hbound
  · exact Real.tsum_le_of_sum_range_le hnonneg hbound
  · intro k hk
    obtain ⟨N₀, h⟩ := OMA.complete M k hM2 hk
    rw [Filter.eventually_atTop]
    refine ⟨N₀, fun n hn => ?_⟩
    obtain ⟨I, a, ha, hs⟩ := h n hn
    exact ⟨I, a, ha, hs⟩
