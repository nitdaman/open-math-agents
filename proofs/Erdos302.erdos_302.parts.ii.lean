import FormalConjectures.ErdosProblems.«302»

-- Problem: Erdős Problem 302 — ii
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/302.lean:76 (declaration Erdos302.erdos_302.parts.ii)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Cambie's construction, for `N = 8 * m`. Let `A` consist of the odd numbers `1, 3, ..., 2 * m - 1`
together with all of `4 * m + 1, ..., 8 * m`. Then `A` has `5 * m` elements and contains no
solution of `1 / a = 1 / b + 1 / c`, that is, of `b * c = a * (c + b)`:

* if `4 * m + 1 ≤ a`, then `b, c ≤ 8 * m` give `b * c ≤ 4 * m * (c + b) < a * (c + b)`;
* if `a` is odd and one of `b`, `c` is odd, then the two sides have different parities;
* if `a < 2 * m` and `4 * m + 1 ≤ b, c`, then `2 * (b * c) ≥ (4 * m + 1) * (c + b) > 2 * a * (c + b)`.

Hence `5 * m ≤ f (8 * m)`, so `f N / N ≥ 5 / 8` along `N = 8 * m`, and the ratio cannot tend
to `1 / 2`. (Distinctness of `a`, `b`, `c` is not needed.)
-/

/-- There is no solution of `b * c = a * (c + b)` among the odd numbers below `2 * m` together
with the interval `[4 * m + 1, 8 * m]`. -/
theorem OMA.e302_core (m a b c : ℕ)
    (ha : (∃ x, x < m ∧ 2 * x + 1 = a) ∨ (4 * m + 1 ≤ a ∧ a ≤ 8 * m))
    (hb : (∃ x, x < m ∧ 2 * x + 1 = b) ∨ (4 * m + 1 ≤ b ∧ b ≤ 8 * m))
    (hc : (∃ x, x < m ∧ 2 * x + 1 = c) ∨ (4 * m + 1 ≤ c ∧ c ≤ 8 * m))
    (h : b * c = a * (c + b)) : False := by
  have hb8 : 1 ≤ b ∧ b ≤ 8 * m := by
    rcases hb with ⟨x, hx, rfl⟩ | ⟨h1, h2⟩ <;> omega
  have hc8 : 1 ≤ c ∧ c ≤ 8 * m := by
    rcases hc with ⟨x, hx, rfl⟩ | ⟨h1, h2⟩ <;> omega
  rcases ha with ⟨x, hx, rfl⟩ | ⟨ha1, ha2⟩
  · have hxm : x + 1 ≤ m := hx
    rcases hb with ⟨y, hy, rfl⟩ | ⟨hb1, hb2⟩
    · -- `a` and `b` are odd: the two sides have different parities.
      have h' : 2 * (y * c) + c = 2 * (x * c) + 2 * (x * (2 * y + 1)) + c + 2 * y + 1 := by
        linarith
      omega
    · rcases hc with ⟨z, hz, rfl⟩ | ⟨hc1, hc2⟩
      · -- `a` and `c` are odd: the two sides have different parities.
        have h' : 2 * (b * z) + b = 2 * (x * (2 * z + 1)) + 2 * (x * b) + 2 * z + 1 + b := by
          linarith
        omega
      · -- `a` is small while `b` and `c` are large.
        have h1 := Nat.mul_le_mul_right c hb1
        have h2 := Nat.mul_le_mul_left b hc1
        have h3 := Nat.mul_le_mul_right c hxm
        have h4 := Nat.mul_le_mul_right b hxm
        nlinarith
  · -- `a` is large while `b` and `c` are at most `8 * m`.
    have h1 := Nat.mul_le_mul_right c hb8.2
    have h2 := Nat.mul_le_mul_left b hc8.2
    have h3 := Nat.mul_le_mul_right (c + b) ha1
    nlinarith

/-- The construction gives `5 * m ≤ f (8 * m)`. -/
theorem OMA.e302_lower (f : ℕ → ℕ) (hf : ∀ N, Erdos302.IsMaxNoTripleCard N (f N)) (m : ℕ) :
    5 * m ≤ f (8 * m) := by
  have hdisj : Disjoint ((Finset.range m).image (fun x => 2 * x + 1))
      (Finset.Icc (4 * m + 1) (8 * m)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    rw [Finset.mem_range] at hx
    rw [Finset.mem_Icc] at hb
    omega
  have key : ∀ n ∈ (Finset.range m).image (fun x => 2 * x + 1) ∪ Finset.Icc (4 * m + 1) (8 * m),
      (∃ x, x < m ∧ 2 * x + 1 = n) ∨ (4 * m + 1 ≤ n ∧ n ≤ 8 * m) := by
    intro n hn
    rcases Finset.mem_union.1 hn with hn | hn
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hn
      exact Or.inl ⟨x, Finset.mem_range.1 hx, rfl⟩
    · exact Or.inr (Finset.mem_Icc.1 hn)
  have pos : ∀ n : ℕ, (∃ x, x < m ∧ 2 * x + 1 = n) ∨ (4 * m + 1 ≤ n ∧ n ≤ 8 * m) → 1 ≤ n := by
    rintro n (⟨x, hx, rfl⟩ | ⟨h1, h2⟩) <;> omega
  refine (hf (8 * m)).2 ⟨(Finset.range m).image (fun x => 2 * x + 1) ∪
    Finset.Icc (4 * m + 1) (8 * m), ?_, ?_, ?_⟩
  · intro a ha
    have h1 := pos a (key a ha)
    have h2 : a ≤ 8 * m := by
      rcases key a ha with ⟨x, hx, rfl⟩ | ⟨h3, h4⟩ <;> omega
    exact Finset.mem_Icc.2 ⟨h1, h2⟩
  · intro a ha b hb c hc _ _ _ h
    have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := pos a (key a ha); omega)
    have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := pos b (key b hb); omega)
    have hc0 : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := pos c (key c hc); omega)
    have hq : (b : ℚ) * c = a * (c + b) := by
      field_simp at h
      linarith
    exact OMA.e302_core m a b c (key a ha) (key b hb) (key c hc) (by exact_mod_cast hq)
  · rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun x y hxy => by simpa using hxy),
      Finset.card_range, Nat.card_Icc]
    omega

theorem OMA.solution : type_of% @Erdos302.erdos_302.parts.ii := by
  intro f hf ht
  have hev : ∀ᶠ N : ℕ in Filter.atTop, (f N : ℝ) / N < 5 / 8 :=
    (tendsto_order.1 ht).2 (5 / 8) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  have h1 := hN₀ (8 * (N₀ + 1)) (by omega)
  have h2 : ((5 * (N₀ + 1) : ℕ) : ℝ) ≤ (f (8 * (N₀ + 1)) : ℝ) := by
    exact_mod_cast OMA.e302_lower f hf (N₀ + 1)
  have hpos : (0 : ℝ) < ((8 * (N₀ + 1) : ℕ) : ℝ) := by positivity
  rw [div_lt_iff₀ hpos] at h1
  push_cast at h1 h2
  linarith
