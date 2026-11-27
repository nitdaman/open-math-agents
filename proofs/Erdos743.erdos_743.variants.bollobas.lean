import FormalConjectures.ErdosProblems.«743»

-- Problem: Erdős Problem 743 — bollobas
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/743.lean:152
-- Credit: @Masterlincs

namespace OMA

open Erdos743 SimpleGraph Sym2

/- The key numerical inequality -/

/-- Bollobás's numerical inequality: if `2 ≤ k ≤ m` and `2 * m ^ 2 ≤ n ^ 2` then the number of
edges left over after packing the trees `T_k, …, T_m` into `K_n` beats twice the bound that
guarantees a vertex set in which every vertex has at least `k - 1` unused neighbours. -/
theorem key_ineq {n m k : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m) (h2 : 2 * m ^ 2 ≤ n ^ 2) :
    m * (m - 1) + 2 * (n - k + 1) * (k - 2) + (k - 1) * (k - 2) < n * (n - 1) + k * (k - 1) := by
  have hsq : (0 : ℤ) ≤ (2 * (k : ℤ) - (n : ℤ) - 2) ^ 2 := sq_nonneg _
  have hmn : (m : ℤ) ≤ (n : ℤ) := by
    have h' : (2 * (m : ℤ) ^ 2) ≤ (n : ℤ) ^ 2 := by exact_mod_cast h2
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := by positivity
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := by positivity
    nlinarith [sq_nonneg ((n : ℤ) - (m : ℤ))]
  have hn2 : (0 : ℤ) ≤ (n : ℤ) ^ 2 - 2 * (m : ℤ) ^ 2 := by
    have h' : (2 * (m : ℤ) ^ 2) ≤ (n : ℤ) ^ 2 := by exact_mod_cast h2
    linarith
  have ident : (2 : ℤ) * ((n : ℤ) * (n - 1) + (k : ℤ) * (k - 1)
      - ((m : ℤ) * (m - 1) + 2 * ((n : ℤ) - k + 1) * ((k : ℤ) - 2)
      + ((k : ℤ) - 1) * ((k : ℤ) - 2)))
      = (2 * (k : ℤ) - (n : ℤ) - 2) ^ 2 + ((n : ℤ) ^ 2 - 2 * (m : ℤ) ^ 2) + 2 * (n : ℤ)
        + 2 * (m : ℤ) := by
    push_cast
    ring
  have hm2 : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast (hk.trans hkm)
  have hpos : (0 : ℤ) < (2 * (k : ℤ) - (n : ℤ) - 2) ^ 2 + ((n : ℤ) ^ 2 - 2 * (m : ℤ) ^ 2)
      + 2 * (n : ℤ) + 2 * (m : ℤ) := by
    have h' : (0 : ℤ) < 2 * (m : ℤ) := by linarith
    linarith
  have hF : (0 : ℤ) < (n : ℤ) * (n - 1) + (k : ℤ) * (k - 1)
      - ((m : ℤ) * (m - 1) + 2 * ((n : ℤ) - k + 1) * ((k : ℤ) - 2) + ((k : ℤ) - 1)
        * ((k : ℤ) - 2)) := by linarith
  have hnk : (k : ℤ) ≤ (n : ℤ) := by linarith
  have hgoal : (((m * (m - 1) + 2 * (n - k + 1) * (k - 2) + (k - 1) * (k - 2) : ℕ) : ℤ)
      < ((n * (n - 1) + k * (k - 1) : ℕ) : ℤ)) := by
    have h1 : (((k : ℕ) - 1 : ℕ) : ℤ) = ((k : ℤ) - 1) := by omega
    have h2' : (((k : ℕ) - 2 : ℕ) : ℤ) = ((k : ℤ) - 2) := by omega
    have h3 : (((n : ℕ) - (k : ℕ) : ℕ) : ℤ) = ((n : ℤ) - (k : ℤ)) := by omega
    have h4 : (((m : ℕ) - 1 : ℕ) : ℤ) = ((m : ℤ) - 1) := by omega
    have h5 : (((n : ℕ) - 1 : ℕ) : ℤ) = ((n : ℤ) - 1) := by omega
    push_cast
    simp only [h1, h2', h3, h4, h5]
    omega
  exact_mod_cast hgoal

/- The bound on the greedy parameter -/

/-- The greedy parameter `m = ⌊n / √2⌋` satisfies `m ≤ n` and `2 * m ^ 2 ≤ n ^ 2`. -/
theorem floor_bounds (n : ℕ) :
    ⌊(n : ℝ) / Real.sqrt 2⌋₊ ≤ n ∧ 2 * ⌊(n : ℝ) / Real.sqrt 2⌋₊ ^ 2 ≤ n ^ 2 := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt 2 := by positivity
  have hfl : ((⌊(n : ℝ) / Real.sqrt 2⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) / Real.sqrt 2 := Nat.floor_le h0
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_lt_sqrt_two.le
  have hnn : (n : ℝ) / Real.sqrt 2 ≤ (n : ℝ) := div_le_self (by positivity) hs
  have hle : ((⌊(n : ℝ) / Real.sqrt 2⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) := hfl.trans hnn
  constructor
  · exact_mod_cast hle
  · have hm0 : (0 : ℝ) ≤ ((⌊(n : ℝ) / Real.sqrt 2⌋₊ : ℕ) : ℝ) := by positivity
    have hd0 : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt 2 := by positivity
    have hsq : ((⌊(n : ℝ) / Real.sqrt 2⌋₊ : ℕ) : ℝ) ^ 2 ≤ ((n : ℝ) / Real.sqrt 2) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) / Real.sqrt 2 - ((⌊(n : ℝ) / Real.sqrt 2⌋₊ : ℕ) : ℝ))]
    have hd : ((n : ℝ) / Real.sqrt 2) ^ 2 = (n : ℝ) ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hhalf : (2 : ℝ) * ((n : ℝ) ^ 2 / 2) = (n : ℝ) ^ 2 := by ring
    have h3 : 2 * ((⌊(n : ℝ) / Real.sqrt 2⌋₊ : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      rw [hd] at hsq
      nlinarith [hsq, hhalf]
    exact_mod_cast h3

/- Ordered pairs and neighbourhoods modulo a set of used edges -/

open scoped Classical in
/-- Ordered pairs `(v, w)` of distinct elements of `S` whose edge is not used. -/
noncomputable def opair (n : ℕ) (W : Set (Sym2 (Fin n))) (S : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  S.offDiag.filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W))

open scoped Classical in
/-- The neighbours of `v` inside `S` reached by a non-used edge. -/
noncomputable def wnbr (n : ℕ) (W : Set (Sym2 (Fin n))) (S : Finset (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  S.filter (fun w => v ≠ w ∧ ¬ (Sym2.mk v w ∈ W))

/-- Deleting a vertex from `S` removes exactly two ordered pairs for each of its non-used
neighbours in the rest of `S`. -/
theorem opair_erase (n : ℕ) (W : Set (Sym2 (Fin n))) {S : Finset (Fin n)} {v : Fin n}
    (hv : v ∈ S) :
    (opair n W S).card = (opair n W (S.erase v)).card + 2 * (wnbr n W (S.erase v) v).card := by
  classical
  have hvE : v ∉ S.erase v := by simp
  have hoff : S.offDiag = (S.erase v).offDiag ∪ ({v} ×ˢ S.erase v ∪ S.erase v ×ˢ {v}) := by
    have h1 : S.offDiag = (insert v (S.erase v)).offDiag := by rw [Finset.insert_erase hv]
    simp only [h1, Finset.offDiag_insert hvE, Finset.union_assoc]
  have hsplit : opair n W S = opair n W (S.erase v)
      ∪ (({v} ×ˢ S.erase v).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W))
        ∪ (S.erase v ×ˢ {v}).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W))) := by
    simp only [opair, hoff, Finset.filter_union]
  have hoffE : ∀ p ∈ opair n W (S.erase v), p.1 ∈ S.erase v ∧ p.2 ∈ S.erase v := by
    intro p hp
    have h := Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1
    exact ⟨h.1, h.2.1⟩
  have hBv : ∀ p ∈ ({v} ×ˢ S.erase v).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W)), p.1 = v :=
    fun p hp => Finset.mem_singleton.mp
      (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hCv : ∀ p ∈ (S.erase v ×ˢ {v}).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W)), p.2 = v :=
    fun p hp => Finset.mem_singleton.mp
      (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  have hCw : ∀ p ∈ (S.erase v ×ˢ {v}).filter
      (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W)), p.1 ∈ S.erase v :=
    fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have i1 : (opair n W (S.erase v) ∩ (({v} ×ˢ S.erase v).filter
      (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W)) ∪ (S.erase v ×ˢ {v}).filter
      (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W)))) = ∅ := by
    ext p
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hA, hB | hC⟩
      · exact absurd (hBv p hB ▸ (hoffE p hA).1) hvE
      · exact absurd (hCv p hC ▸ (hoffE p hA).2) hvE
    · intro h
      exact absurd h (Finset.notMem_empty p)
  have i2 : (({v} ×ˢ S.erase v).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W)) ∩
      ((S.erase v ×ˢ {v}).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W)))) = ∅ := by
    ext p
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hB, hC⟩
      exact absurd (hBv p hB ▸ hCw p hC) hvE
    · intro h
      exact absurd h (Finset.notMem_empty p)
  have hB : ({v} ×ˢ S.erase v).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W))
      = (wnbr n W (S.erase v) v).image (fun w => (v, w)) := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
      wnbr]
    constructor
    · rintro ⟨⟨h1, hp2⟩, hp⟩
      rw [h1] at hp
      exact ⟨p.2, ⟨hp2, ⟨fun hh => hvE (hh ▸ hp2), hp⟩⟩, Prod.ext h1.symm rfl⟩
    · rintro ⟨w, ⟨hw, ⟨-, hp⟩⟩, hpeq⟩
      subst hpeq
      exact ⟨⟨rfl, hw⟩, hp⟩
  have hC : (S.erase v ×ˢ {v}).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W))
      = (wnbr n W (S.erase v) v).image (fun w => (w, v)) := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
      wnbr]
    constructor
    · rintro ⟨⟨hw, h2⟩, hp⟩
      rw [h2] at hp
      exact ⟨p.1, ⟨hw, ⟨fun hh => hvE (hh ▸ hw), by rw [Sym2.eq_swap]; exact hp⟩⟩,
        Prod.ext rfl h2.symm⟩
    · rintro ⟨w, ⟨hw, ⟨-, hp⟩⟩, hpeq⟩
      subst hpeq
      exact ⟨⟨hw, rfl⟩, by rw [Sym2.eq_swap]; exact hp⟩
  have hcB : (({v} ×ˢ S.erase v).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W))).card
      = (wnbr n W (S.erase v) v).card := by
    rw [hB, Finset.card_image_of_injOn]
    intro a _ b _ h
    simpa [Prod.mk.injEq] using h
  have hcC : ((S.erase v ×ˢ {v}).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W))).card
      = (wnbr n W (S.erase v) v).card := by
    rw [hC, Finset.card_image_of_injOn]
    intro a _ b _ h
    simpa [Prod.mk.injEq] using h
  have c1 := Finset.card_union_add_card_inter (opair n W (S.erase v))
      (({v} ×ˢ S.erase v).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W))
        ∪ (S.erase v ×ˢ {v}).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W)))
  have c2 := Finset.card_union_add_card_inter
      (({v} ×ˢ S.erase v).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W)))
      ((S.erase v ×ˢ {v}).filter (fun p => ¬ (Sym2.mk p.1 p.2 ∈ W)))
  rw [i1] at c1
  rw [i2] at c2
  simp only [Finset.card_empty] at c1 c2
  rw [hsplit]
  omega

open scoped Classical in
/-- The number of ordered pairs from `univ` whose edge lies in `W` is at most twice the
cardinal of `W`. -/
theorem used_pairs_le (n : ℕ) (W : Set (Sym2 (Fin n))) (hW : W.Finite) :
    (((Finset.univ : Finset (Fin n)).offDiag).filter
        (fun p : Fin n × Fin n => Sym2.mk p.1 p.2 ∈ W)).card
      ≤ 2 * W.ncard := by
  classical
  obtain ⟨lo, hlo_def⟩ : ∃ lo : Finset (Fin n × Fin n),
      lo = (((Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))).filter
        (fun p => p.1 < p.2 ∧ Sym2.mk p.1 p.2 ∈ W)) := ⟨_, rfl⟩
  obtain ⟨hi, hhi_def⟩ : ∃ hi : Finset (Fin n × Fin n),
      hi = (((Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))).filter
        (fun p => p.2 < p.1 ∧ Sym2.mk p.1 p.2 ∈ W)) := ⟨_, rfl⟩
  have hmemlo : ∀ p ∈ lo, p.1 < p.2 ∧ Sym2.mk p.1 p.2 ∈ W := by
    intro p hp
    rw [hlo_def] at hp
    exact (Finset.mem_filter.mp hp).2
  have hmemhi : ∀ p ∈ hi, p.2 < p.1 ∧ Sym2.mk p.1 p.2 ∈ W := by
    intro p hp
    rw [hhi_def] at hp
    exact (Finset.mem_filter.mp hp).2
  have hsplit : (((Finset.univ : Finset (Fin n)).offDiag).filter (fun p => Sym2.mk p.1 p.2 ∈ W))
      = lo ∪ hi := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product,
      Finset.mem_univ, and_true, true_and, hlo_def, hhi_def]
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · constructor
      · rintro ⟨hne, hm⟩
        exact Or.inl ⟨h, hm⟩
      · rintro (⟨h1, hm⟩ | ⟨h1, hm⟩)
        · exact ⟨by omega, hm⟩
        · exact ⟨by omega, hm⟩
    · simp [h]
    · constructor
      · rintro ⟨hne, hm⟩
        exact Or.inr ⟨h, hm⟩
      · rintro (⟨h1, hm⟩ | ⟨h1, hm⟩)
        · exact ⟨by omega, hm⟩
        · exact ⟨by omega, hm⟩
  have hlo : lo.card ≤ W.ncard := by
    have hinj : Set.InjOn (fun p : Fin n × Fin n => Sym2.mk p.1 p.2) (lo : Set (Fin n × Fin n)) := by
      rintro a ha b hb h
      have ha' := hmemlo a (Finset.mem_coe.mp ha)
      have hb' := hmemlo b (Finset.mem_coe.mp hb)
      rcases Sym2.eq_iff.mp h with ⟨r1, r2⟩ | ⟨r1, r2⟩
      · exact Prod.ext r1 r2
      · omega
    have himg : ((Finset.image (fun p : Fin n × Fin n => Sym2.mk p.1 p.2) lo
        : Set (Sym2 (Fin n)))) ⊆ W := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp he)
      exact (hmemlo p hp).2
    have h1 : (Finset.image (fun p : Fin n × Fin n => Sym2.mk p.1 p.2) lo).card = lo.card :=
      Finset.card_image_of_injOn hinj
    have h2 : ((Finset.image (fun p : Fin n × Fin n => Sym2.mk p.1 p.2) lo
        : Set (Sym2 (Fin n)))).ncard
      = (Finset.image (fun p : Fin n × Fin n => Sym2.mk p.1 p.2) lo).card :=
      Set.ncard_coe_finset _
    have h3 : ((Finset.image (fun p : Fin n × Fin n => Sym2.mk p.1 p.2) lo
        : Set (Sym2 (Fin n)))).ncard ≤ W.ncard := Set.ncard_le_ncard himg hW
    omega
  have hswap : hi = lo.image Prod.swap := by
    ext p
    constructor
    · intro hp
      rw [hhi_def] at hp
      have h := Finset.mem_filter.mp hp
      refine Finset.mem_image.mpr ⟨(p.2, p.1), ?_, rfl⟩
      rw [hlo_def]
      refine Finset.mem_filter.mpr ⟨
        Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        ⟨h.2.1, by rw [Sym2.eq_swap]; exact h.2.2⟩⟩
    · intro hp
      obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp hp
      rw [hlo_def] at hq
      have hq1 := (Finset.mem_filter.mp hq).2
      rw [hhi_def]
      refine Finset.mem_filter.mpr ⟨
        Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ⟨?_, ?_⟩⟩
      · rw [← hq']
        exact hq1.1
      · rw [← hq', Sym2.eq_swap]
        exact hq1.2
  have hhi : hi.card = lo.card := by
    rw [hswap, Finset.card_image_of_injOn]
    rintro a _ b _ h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have i12 : lo ∩ hi = ∅ := by
    ext p
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨h1', h2'⟩
      have hh1 := (hmemlo p h1').1
      have hh2 := (hmemhi p h2').1
      exact absurd (by omega) (Finset.notMem_empty p)
    · intro h
      exact absurd h (Finset.notMem_empty p)
  have c := Finset.card_union_add_card_inter lo hi
  rw [i12] at c
  simp only [Finset.card_empty] at c
  rw [hsplit]
  omega

/-- There are at least `n * n - n - 2 * #W` non-used ordered pairs. -/
theorem unused_pairs_ge (n : ℕ) (W : Set (Sym2 (Fin n))) (hW : W.Finite) :
    n * n - n ≤ (opair n W (Finset.univ : Finset (Fin n))).card + 2 * W.ncard := by
  classical
  have hop : opair n W (Finset.univ : Finset (Fin n))
      = (((Finset.univ : Finset (Fin n)).offDiag).filter
          (fun p : Fin n × Fin n => ¬ (Sym2.mk p.1 p.2 ∈ W))) := rfl
  have hpart : ((((Finset.univ : Finset (Fin n)).offDiag).filter
      (fun p : Fin n × Fin n => Sym2.mk p.1 p.2 ∈ W)).card
      + (opair n W (Finset.univ : Finset (Fin n))).card
      = ((Finset.univ : Finset (Fin n)).offDiag).card) :=
    Finset.card_filter_add_card_filter_not (fun p : Fin n × Fin n => Sym2.mk p.1 p.2 ∈ W)
  have hcard : ((Finset.univ : Finset (Fin n)).offDiag).card = n * n - n := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  have hused := used_pairs_le n W hW
  omega

/- Twice `a.choose 2` is `a * (a - 1)`. -/
theorem two_mul_choose_two (a : ℕ) : 2 * a.choose 2 = a * (a - 1) := by
  rw [Nat.choose_two_right]
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · have h2 : 2 ∣ a := by omega
    have h3 : 2 ∣ a * (a - 1) := h2.mul_right _
    omega
  · have h2 : 2 ∣ a - 1 := by omega
    have h3 : 2 ∣ a * (a - 1) := h2.mul_left _
    omega

/- Bollobás's min-degree lemma -/

/-- If there are more than `2 * ((#S - (k - 1)) * (k - 2) + (k - 1).choose 2)` non-used ordered
pairs inside `S`, then there is a nonempty `S'` in which every vertex has at least `k - 1`
non-used neighbours. -/
theorem exists_dense (n : ℕ) (W : Set (Sym2 (Fin n))) {k : ℕ} (hk : 2 ≤ k) :
    ∀ (c : ℕ) (S : Finset (Fin n)), S.card ≤ c →
      (opair n W S).card > 2 * ((S.card - (k - 1)) * (k - 2) + (k - 1).choose 2) →
      ∃ S' : Finset (Fin n), S'.Nonempty ∧ ∀ v ∈ S', (wnbr n W S' v).card ≥ k - 1 := by
  classical
  intro c
  induction c with
  | zero =>
    intro S hSc hcard
    have hS : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hSc)
    subst hS
    have h0 : (opair n W (∅ : Finset (Fin n))).card = 0 := by simp [opair]
    rw [Finset.card_empty] at hcard
    exact absurd hcard (by omega)
  | succ c ih =>
    intro S hSc hcard
    rcases Nat.lt_or_ge (S.card) k with hsk | hsk
    · -- the hypothesis is vacuous when #S < k
      have h1 : opair n W S ⊆ S.offDiag := fun p hp => (Finset.mem_filter.mp hp).1
      have h2 := Finset.card_le_card h1
      rw [Finset.offDiag_card] at h2
      have h3 : S.card * S.card - S.card = S.card * (S.card - 1) := by
        rw [Nat.mul_sub, Nat.mul_one]
      have h4 : S.card * (S.card - 1) ≤ (k - 1) * ((k - 1) - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h5 := two_mul_choose_two (k - 1)
      exact absurd hcard (by omega)
    · by_cases hA : ∀ v ∈ S, (wnbr n W S v).card ≥ k - 1
      · refine ⟨S, ?_, hA⟩
        have hpos : 0 < (opair n W S).card := by omega
        obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
        have hmem := Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1
        exact ⟨p.1, hmem.1⟩
      · push_neg at hA
        obtain ⟨v, hvS, hdeg⟩ := hA
        have hEq : wnbr n W (S.erase v) v = wnbr n W S v := by
          ext w
          simp only [wnbr, Finset.mem_filter]
          constructor
          · rintro ⟨hw, hvw, hp⟩
            exact ⟨(Finset.mem_erase.mp hw).2, hvw, hp⟩
          · rintro ⟨hw, hvw, hp⟩
            exact ⟨Finset.mem_erase.mpr ⟨Ne.symm hvw, hw⟩, hvw, hp⟩
        have hdegE : (wnbr n W (S.erase v) v).card = (wnbr n W S v).card := by rw [hEq]
        have hc := opair_erase n W hvS
        have hcardE : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hvS
        have hpass : (opair n W (S.erase v)).card
            > 2 * (((S.erase v).card - (k - 1)) * (k - 2) + (k - 1).choose 2) := by
          have hXY : (S.card - (k - 1)) * (k - 2)
            = ((S.erase v).card - (k - 1)) * (k - 2) + (k - 2) := by
            rw [hcardE]
            have h1 : S.card - (k - 1) = ((S.card - 1) - (k - 1)) + 1 := by omega
            rw [h1]
            ring
          omega
        exact ih (S.erase v) (by omega) hpass

/- Trees: leaves and edge counts -/

/-- A tree with at least two vertices has a leaf: a vertex with a unique neighbour. -/
theorem exists_leaf {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    {T : SimpleGraph α} (hT : T.IsTree) :
    ∃ ℓ p : α, T.Adj ℓ p ∧ ∀ q, T.Adj ℓ q → q = p := by
  classical
  obtain ⟨ℓ, hdeg⟩ := hT.exists_vert_degree_one_of_nontrivial
  obtain ⟨p, hadj, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  exact ⟨ℓ, p, hadj, huniq⟩

/-- Deleting a leaf from a tree leaves a tree. -/
theorem induce_compl_isTree {α : Type*} [Fintype α] [DecidableEq α] {T : SimpleGraph α}
    {ℓ : α} [Fintype ↥(T.neighborSet ℓ)]
    (hT : T.IsTree) (hdeg : T.degree ℓ = 1) : (T.induce {ℓ}ᶜ).IsTree :=
  ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hdeg, hT.isAcyclic.induce _⟩

/-- A tree on `α` has `#α - 1` edges. -/
theorem tree_edge_ncard {α : Type*} [Fintype α] [DecidableEq α] {T : SimpleGraph α}
    (hT : T.IsTree) : (T.edgeSet).ncard = Fintype.card α - 1 := by
  classical
  have h1 := hT.card_edgeFinset
  have h2 : T.edgeFinset.card = Fintype.card (T.edgeSet) := SimpleGraph.edgeFinset_card
  have h3 : Fintype.card (T.edgeSet) = (T.edgeSet).ncard := Set.fintypeCard_eq_ncard _
  rw [h2, h3] at h1
  omega

/-- Membership in the edge set of a mapped graph. -/
theorem mem_map_edgeSet {α : Type*} {β : Type*} {G : SimpleGraph α}
    {f : α → β} (hf : Function.Injective f) {e : Sym2 β} :
    e ∈ (G.map f).edgeSet ↔ ∃ a b, G.Adj a b ∧ e = Sym2.mk (f a) (f b) := by
  classical
  constructor
  · intro he
    have he' : e ∈ (⟨f, hf⟩ : α ↪ β).sym2Map '' G.edgeSet := by
      rw [← SimpleGraph.edgeSet_map]
      exact he
    obtain ⟨e', he'₁, he'₂⟩ := (Set.mem_image _ _ _).mp he'
    obtain ⟨q, rfl⟩ := Sym2.mk_surjective e'
    have hadj : G.Adj q.1 q.2 := (SimpleGraph.mem_edgeSet _).mp he'₁
    refine ⟨q.1, q.2, hadj, ?_⟩
    rw [← he'₂, Function.Embedding.sym2Map_apply]
    rfl
  · rintro ⟨a, b, hadj, rfl⟩
    refine (SimpleGraph.mem_edgeSet _).mpr ?_
    exact SimpleGraph.map_adj_apply' hadj (fun h => hadj.ne (hf h))

/- The greedy embedding of a tree -/

/-- A tree whose vertices all have at least `#α - 1` non-used neighbours available in `S`
embeds into `Fin n` so that all its edges avoid the used set `W`. -/
theorem embed_aux (n : ℕ) (W : Set (Sym2 (Fin n))) (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∀ (c : ℕ) (α : Type) [Fintype α] [DecidableEq α], Fintype.card α ≤ c →
      (∀ v ∈ S, (wnbr n W S v).card ≥ Fintype.card α - 1) →
      ∀ (T : SimpleGraph α), T.IsTree →
      ∃ f : α → Fin n, Function.Injective f ∧ (∀ a, f a ∈ S) ∧
        ∀ a b, T.Adj a b → f a ≠ f b ∧ ¬ (Sym2.mk (f a) (f b) ∈ W) := by
  intro c
  induction c with
  | zero =>
    intro α _ _ hc hdeg T hT
    exact absurd (Fintype.card_pos_iff.mpr hT.connected.nonempty) (by omega)
  | succ c ih =>
    intro α _ _ hc hdeg T hT
    rcases Nat.lt_or_ge (Fintype.card α) 2 with h2 | h2
    · have hsub : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      obtain ⟨v, hv⟩ := hS
      refine ⟨fun _ => v, fun a b _ => Subsingleton.elim a b, fun _ => hv, fun a b hab =>
        absurd (Subsingleton.elim a b) (SimpleGraph.Adj.ne hab)⟩
    · classical
      have hnax : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp h2
      obtain ⟨ℓ, p, hadj, huniq⟩ := exists_leaf (T := T) hT
      haveI : Fintype ↥(T.neighborSet ℓ) :=
        ((Set.finite_univ : (Set.univ : Set α).Finite).subset
          (fun x _ => Set.mem_univ x)).fintype
      have hpℓ : p ≠ ℓ := hadj.ne'
      have hpℓc : p ∈ ({ℓ}ᶜ : Set α) :=
        (Set.mem_compl_iff _ _).mpr (fun hh => hpℓ (Set.mem_singleton_iff.mp hh))
      have hdegℓ : T.degree ℓ = 1 :=
        SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ⟨p, hadj, huniq⟩
      have hT' : (T.induce {ℓ}ᶜ).IsTree := induce_compl_isTree hT hdegℓ
      have hcard' : Fintype.card ↥({ℓ}ᶜ : Set α) = Fintype.card α - 1 := by
        have h1 : Fintype.card ↥({ℓ}ᶜ : Set α)
            = Fintype.card α - Fintype.card ↥({ℓ} : Set α) :=
          Fintype.card_subtype_compl (fun x => x ∈ ({ℓ} : Set α))
        have h2 : Fintype.card ↥({ℓ} : Set α) = 1 := by
          rw [Set.fintypeCard_eq_ncard ({ℓ} : Set α)]
          simp
        rw [h1, h2]
      obtain ⟨f', hf'inj, hf'S, hf'edges⟩ :=
        ih ↥({ℓ}ᶜ : Set α) (by omega)
          (fun v hv => by have h1 := hdeg v hv; omega) (T.induce {ℓ}ᶜ) hT'
      have huS : f' ⟨p, hpℓc⟩ ∈ S := hf'S ⟨p, hpℓc⟩
      obtain ⟨w, hwmem, hwF⟩ : ∃ w ∈ wnbr n W S (f' ⟨p, hpℓc⟩),
          w ∉ Finset.univ.image f' := by
        by_contra hcon
        push Not at hcon
        have hnu : f' ⟨p, hpℓc⟩ ∉ wnbr n W S (f' ⟨p, hpℓc⟩) := by
          intro hnu'
          simp only [wnbr, Finset.mem_filter] at hnu'
          exact hnu'.2.1 rfl
        have hsub2 : wnbr n W S (f' ⟨p, hpℓc⟩)
            ⊆ (Finset.univ.image f').erase (f' ⟨p, hpℓc⟩) := by
          intro x hx
          refine Finset.mem_erase.mpr ⟨?_, hcon x hx⟩
          exact Ne.symm (Finset.mem_filter.mp hx).2.1
        have h1 : (wnbr n W S (f' ⟨p, hpℓc⟩)).card
            ≤ ((Finset.univ.image f').erase (f' ⟨p, hpℓc⟩)).card :=
          Finset.card_le_card hsub2
        have h2 : ((Finset.univ.image f').erase (f' ⟨p, hpℓc⟩)).card
            ≤ Fintype.card ↥({ℓ}ᶜ : Set α) - 1 := by
          have hmem : f' ⟨p, hpℓc⟩ ∈ (Finset.univ.image f') :=
            Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
          rw [Finset.card_erase_of_mem hmem]
          have h3 : (Finset.univ.image f').card ≤ Fintype.card ↥({ℓ}ᶜ : Set α) :=
            Finset.card_image_le.trans (by rw [Finset.card_univ])
          omega
        have h4 := hdeg (f' ⟨p, hpℓc⟩) huS
        omega
      have hwN : f' ⟨p, hpℓc⟩ ≠ w ∧ ¬ (Sym2.mk (f' ⟨p, hpℓc⟩) w ∈ W) :=
        (Finset.mem_filter.mp hwmem).2
      have hmemP : ∀ a : α, ¬ (a = ℓ) → a ∈ ({ℓ}ᶜ : Set α) := fun a h =>
        (Set.mem_compl_iff _ _).mpr (fun hh => h (Set.mem_singleton_iff.mp hh))
      refine ⟨fun a => if h : a = ℓ then w else f' ⟨a, hmemP a h⟩, ?_, ?_, ?_⟩
      · intro a b hab
        by_cases ha : a = ℓ
        · by_cases hb : b = ℓ
          · exact ha.trans hb.symm
          · simp only [dif_pos ha, dif_neg hb] at hab
            have hmem : f' ⟨b, hmemP b hb⟩ ∈ Finset.univ.image f' :=
              Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
            rw [← hab] at hmem
            exact absurd hmem hwF
        · by_cases hb : b = ℓ
          · simp only [dif_neg ha, dif_pos hb] at hab
            have hmem : f' ⟨a, hmemP a ha⟩ ∈ Finset.univ.image f' :=
              Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
            rw [hab] at hmem
            exact absurd hmem hwF
          · simp only [dif_neg ha, dif_neg hb] at hab
            exact Subtype.ext_iff.mp (hf'inj hab)
      · intro a
        by_cases ha : a = ℓ
        · simp only [dif_pos ha]
          exact (Finset.mem_filter.mp hwmem).1
        · simp only [dif_neg ha]
          exact hf'S _
      · intro a b hab
        by_cases ha : a = ℓ
        · have hb : b ≠ ℓ := fun h => hab.ne (ha.trans h.symm)
          have hbp : b = p := huniq b (by rw [← ha]; exact hab)
          simp only [dif_pos ha, dif_neg hb]
          have hfb : f' ⟨b, hmemP b hb⟩ = f' ⟨p, hpℓc⟩ :=
            congrArg f' (Subtype.ext hbp)
          rw [hfb]
          exact ⟨Ne.symm hwN.1, by rw [Sym2.eq_swap]; exact hwN.2⟩
        · by_cases hb : b = ℓ
          · have hap : a = p := huniq a (by exact (hb ▸ hab).symm)
            simp only [dif_neg ha, dif_pos hb]
            have hfa : f' ⟨a, hmemP a ha⟩ = f' ⟨p, hpℓc⟩ :=
              congrArg f' (Subtype.ext hap)
            rw [hfa]
            exact hwN
          · simp only [dif_neg ha, dif_neg hb]
            have h' : (T.induce {ℓ}ᶜ).Adj ⟨a, hmemP a ha⟩ ⟨b, hmemP b hb⟩ := by
              rw [SimpleGraph.induce_adj]
              exact hab
            exact hf'edges _ _ h'

/-- Supply calculation: the key arithmetic giving enough unused pairs at step `k`. -/
theorem supply_calc {n m k op w : ℕ} (hk : 2 ≤ k)
    (hkey : m * (m - 1) + 2 * ((n - k + 1) * (k - 2)) + (k - 1) * (k - 2)
      < n * (n - 1) + k * (k - 1))
    (hnn : n * (n - 1) = n * n - n)
    (hbr : (n - k + 1) * (k - 2) = (n - (k - 1)) * (k - 2))
    (h2k : 2 * k.choose 2 = k * (k - 1))
    (h2km : 2 * m.choose 2 = m * (m - 1))
    (h2kk : 2 * (k - 1).choose 2 = (k - 1) * (k - 2))
    (hu : n * n - n ≤ op + 2 * w)
    (hinv : w + k.choose 2 ≤ m.choose 2) :
    op > 2 * ((n - (k - 1)) * (k - 2) + (k - 1).choose 2) := by omega

/-- Bridge between the two ways of writing the remaining-vertex count. -/
theorem sub_bridge {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    (n - k + 1) * (k - 2) = (n - (k - 1)) * (k - 2) := by
  have h : n - k + 1 = n - (k - 1) := by omega
  rw [h]

/-- The invariant is preserved when adding the `k - 1` edges of `T k`. -/
theorem inv_calc {m k w' b : ℕ} (hinv : w' + k.choose 2 ≤ m.choose 2)
    (hB : b ≤ k - 1) (h3 : k.choose 2 = (k - 1).choose 2 + (k - 1)) :
    w' + b + (k - 1).choose 2 ≤ m.choose 2 := by omega

/-- Greedy decreasing-order packing of the trees `T k` for `k ∈ [k₀, m]` into `K_n`. -/
theorem pack_aux (n m : ℕ) (hm2 : 2 * m ^ 2 ≤ n ^ 2) (hmn : m ≤ n)
    (T : (k : ℕ) → SimpleGraph (Fin k))
    (hT : ∀ k, k ∈ Set.Icc 2 m → (T k).IsTree) :
    ∀ d k : ℕ, 2 ≤ k → k + d = m + 1 →
    ∃ (W : Set (Sym2 (Fin n))) (g : (j : Set.Icc k m) → Fin ↑j → Fin n),
      W.Finite ∧
      (∀ j : Set.Icc k m, Function.Injective (g j)) ∧
      (∀ j : Set.Icc k m, ((T ↑j).map (g j)).edgeSet ⊆ W) ∧
      (∀ j l : Set.Icc k m, (↑j : ℕ) < (↑l : ℕ) →
        Disjoint ((T ↑j).map (g j)).edgeSet ((T ↑l).map (g l)).edgeSet) ∧
      W.ncard + (k - 1).choose 2 ≤ m.choose 2 := by
  intro d
  induction d with
  | zero =>
    intro k hk hkdm
    have hIcc : ∀ j : Set.Icc k m, False := fun j => by
      have h1 := (Set.mem_Icc.mp j.2).1
      have h2 := (Set.mem_Icc.mp j.2).2
      omega
    refine ⟨∅, fun j x => (hIcc j).elim, Set.finite_empty,
      fun j => (hIcc j).elim, fun j => (hIcc j).elim, fun j l h => (hIcc j).elim, ?_⟩
    have hk1 : k = m + 1 := by omega
    subst hk1
    simp
  | succ d ih =>
    intro k hk hkdm
    obtain ⟨W', g', hW'fin, hinj', hsub', hdisj', hinv'⟩ := ih (k + 1) (by omega) (by omega)
    have hkm : k ≤ m := by omega
    have hinv : W'.ncard + k.choose 2 ≤ m.choose 2 := by
      have h1 := hinv'
      rw [Nat.add_sub_cancel] at h1
      exact h1
    have hmem : ∀ j : Set.Icc k m, k ≤ ↑j ∧ ↑j ≤ m := fun j => Set.mem_Icc.mp j.2
    have hmem2 : ∀ jv : ℕ, jv ∈ Set.Icc k m → ¬ (jv = k) → jv ∈ Set.Icc (k + 1) m := by
      intro jv hjv hj
      have h1 := (Set.mem_Icc.mp hjv).1
      have h2 := (Set.mem_Icc.mp hjv).2
      exact Set.mem_Icc.mpr ⟨by omega, h2⟩
    -- the supply: enough unused ordered pairs to host a copy of `T k`
    have hkey := key_ineq hk hkm hm2
    rw [Nat.mul_assoc] at hkey
    have hnn : n * (n - 1) = n * n - n := by rw [Nat.mul_sub, Nat.mul_one]
    have hbr : (n - k + 1) * (k - 2) = (n - (k - 1)) * (k - 2) :=
      sub_bridge hk (hkm.trans hmn)
    have h2k := two_mul_choose_two k
    have h2km := two_mul_choose_two m
    have h2kk : 2 * (k - 1).choose 2 = (k - 1) * (k - 2) :=
      (two_mul_choose_two (k - 1)).trans (congrArg (fun x => (k - 1) * x) (by omega))
    have hu := unused_pairs_ge n W' hW'fin
    have hsupply : (opair n W' (Finset.univ : Finset (Fin n))).card
        > 2 * ((n - (k - 1)) * (k - 2) + (k - 1).choose 2) :=
      supply_calc hk hkey hnn hbr h2k h2km h2kk hu hinv
    have hsupply' : (opair n W' (Finset.univ : Finset (Fin n))).card
        > 2 * (((Finset.univ : Finset (Fin n)).card - (k - 1)) * (k - 2)
          + (k - 1).choose 2) := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact hsupply
    obtain ⟨S', hS'ne, hS'deg⟩ :=
      exists_dense n W' hk n (Finset.univ : Finset (Fin n)) (by simp) hsupply'
    -- embed `T k` into `S'` avoiding the used edges `W'`
    have hdegk : ∀ v ∈ S', (wnbr n W' S' v).card ≥ Fintype.card (Fin k) - 1 := by
      intro v hv
      rw [Fintype.card_fin]
      exact hS'deg v hv
    obtain ⟨f_k, hfkinj, hfkS, hfkedges⟩ :=
      embed_aux n W' S' hS'ne k (Fin k) (by simp) hdegk (T k)
        (hT k (Set.mem_Icc.mpr ⟨hk, hkm⟩))
    -- count: the new `W` still satisfies the invariant
    have hdisjW : Disjoint W' ((T k).map f_k).edgeSet :=
      (Set.disjoint_left).mpr (fun _ heW hB => by
        obtain ⟨a, b, hadj, rfl⟩ := (mem_map_edgeSet hfkinj).mp hB
        exact (hfkedges a b hadj).2 heW)
    have hun := Set.ncard_union_eq hdisjW
    have hB : ((T k).map f_k).edgeSet.ncard ≤ k - 1 := by
      have h1 : ((T k).map f_k).edgeSet
          = (⟨f_k, hfkinj⟩ : Fin k ↪ Fin n).sym2Map '' (T k).edgeSet :=
        SimpleGraph.edgeSet_map (⟨f_k, hfkinj⟩ : Fin k ↪ Fin n) (T k)
      have h2 : ((⟨f_k, hfkinj⟩ : Fin k ↪ Fin n).sym2Map '' (T k).edgeSet).ncard
          ≤ (T k).edgeSet.ncard := Set.ncard_image_le
      have h34 : (T k).edgeSet.ncard = k - 1 := by
        have h3 := tree_edge_ncard (hT k (Set.mem_Icc.mpr ⟨hk, hkm⟩))
        rw [h3, Fintype.card_fin]
      rw [h1]
      exact h2.trans (le_of_eq h34)
    have h3 : k.choose 2 = (k - 1).choose 2 + (k - 1) := by
      have h : (k - 1 + 1).choose 2 = (k - 1).choose 1 + (k - 1).choose 2 :=
        Nat.choose_succ_succ (k - 1) 1
      have hk1 : k - 1 + 1 = k := by omega
      rw [hk1, Nat.choose_one_right] at h
      omega
    have hfinal : (W' ∪ ((T k).map f_k).edgeSet).ncard + (k - 1).choose 2 ≤ m.choose 2 := by
      rw [hun]
      exact inv_calc hinv hB h3
    refine ⟨W' ∪ ((T k).map f_k).edgeSet,
      fun j x => dite (↑j = k) (fun hj => f_k (Fin.cast hj x))
        (fun hj => g' ⟨↑j, hmem2 ↑j j.2 hj⟩ x),
      hW'fin.union
        ((Set.finite_univ : (Set.univ : Set (Sym2 (Fin n))).Finite).subset
          (fun x _ => Set.mem_univ x)),
      ?_, ?_, ?_, hfinal⟩
    · intro ⟨jv, hjv⟩
      by_cases hj : jv = k
      · intro a b hab
        simp only [dif_pos hj] at hab
        exact (Fin.cast_inj hj).mp (hfkinj hab)
      · have hjv2 : jv ∈ Set.Icc (k + 1) m := hmem2 jv hjv hj
        intro a b hab
        simp only [dif_neg hj] at hab
        exact hinj' ⟨jv, hjv2⟩ hab
    · intro ⟨jv, hjv⟩ e he
      by_cases hj : jv = k
      · simp only [dif_pos hj] at he
        subst hj
        exact Or.inr he
      · have hjv2 : jv ∈ Set.Icc (k + 1) m := hmem2 jv hjv hj
        simp only [dif_neg hj] at he
        exact Or.inl (hsub' ⟨jv, hjv2⟩ he)
    · intro ⟨jv, hjv⟩ ⟨lv, hlv⟩ hjl
      have hjl2 : jv < lv := hjl
      by_cases hj : jv = k
      · have hlne : ¬ (lv = k) := by
          have h1 := (Set.mem_Icc.mp hjv).1
          have h2 := (Set.mem_Icc.mp hlv).1
          omega
        have hlv2 : lv ∈ Set.Icc (k + 1) m := hmem2 lv hlv hlne
        simp only [dif_pos hj, dif_neg hlne]
        subst hj
        refine (Set.disjoint_left).mpr (fun _ heB hL => ?_)
        obtain ⟨a, b, hadj, rfl⟩ := (mem_map_edgeSet hfkinj).mp heB
        exact (hfkedges a b hadj).2 (hsub' ⟨lv, hlv2⟩ hL)
      · have hlne : ¬ (lv = k) := by
          have h1 := (Set.mem_Icc.mp hjv).1
          have h2 := (Set.mem_Icc.mp hlv).1
          omega
        have hjv2 : jv ∈ Set.Icc (k + 1) m := hmem2 jv hjv hj
        have hlv2 : lv ∈ Set.Icc (k + 1) m := hmem2 lv hlv hlne
        simp only [dif_neg hj, dif_neg hlne]
        exact hdisj' ⟨jv, hjv2⟩ ⟨lv, hlv2⟩ hjl

end OMA

theorem OMA.solution : type_of% @Erdos743.erdos_743.variants.bollobas := by
  intro n T hT
  obtain ⟨hmle, hm2⟩ := floor_bounds n
  by_cases hm : 2 ≤ ⌊(n : ℝ) / Real.sqrt 2⌋₊
  · obtain ⟨W, g, hfin, hinj, hsub, hdisj, hinv⟩ :=
      pack_aux n ⌊(n : ℝ) / Real.sqrt 2⌋₊ hm2 hmle T hT
        (⌊(n : ℝ) / Real.sqrt 2⌋₊ - 1) 2 (by omega) (by omega)
    exact ⟨g, hinj, hdisj⟩
  · have hIcc : ∀ j : Set.Icc 2 ⌊(n : ℝ) / Real.sqrt 2⌋₊, False := fun j => by
      have h1 := (Set.mem_Icc.mp j.2).1
      have h2 := (Set.mem_Icc.mp j.2).2
      have h3 : ¬ (2 ≤ ⌊(n : ℝ) / Real.sqrt 2⌋₊) := hm
      omega
    exact ⟨fun j x => (hIcc j).elim, fun j => (hIcc j).elim,
      fun j l h => (hIcc j).elim⟩
