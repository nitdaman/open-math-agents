import FormalConjectures.Wikipedia.HardyLittlewood

-- Problem: First Hardy–Littlewood conjecture — not first and secondHardyLittlewoodConjecture
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/HardyLittlewood.lean:121 (declaration HardyLittlewood.not_first_and_secondHardyLittlewoodConjecture)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# An admissible 447-tuple of width 3158

`tuple` is the narrowest known admissible 447-tuple, `admissible_447_3158.txt` from the
Polymath8 database of narrow admissible tuples (math.mit.edu/~primegaps); a 447-tuple of this
width was first found by Engelsma. It has `0 = tuple[0] < tuple[1] = 2 < ⋯ < tuple[446] = 3158`,
all entries even. `witness` lists, for each modulus `q = 2, 3, …, 447` in turn, a residue
`r < q` that no entry of `tuple` takes mod `q`; this is what makes the tuple admissible (for
`q > 447` a 447-tuple cannot cover all `q` classes).

The facts used later are Boolean checks closed by the kernel (`decide +kernel`, no
`native_decide`): the length, strict monotonicity, the bound `≤ 3158` together with evenness,
the witnesses, and `π(3159) ≤ 446` through a trial-division test proved complete for primes.
-/

namespace HardyLittlewood.Richards

def tuple : List ℕ :=
  [0, 2, 6, 8, 12, 20, 30, 32, 42, 48, 50, 56, 68, 72, 78, 90, 92, 96, 98, 102, 110, 116, 128,
    132, 138, 146, 152, 156, 158, 162, 176, 186, 200, 210, 212, 216, 228, 230, 240, 242, 246,
    252, 260, 266, 272, 278, 282, 288, 300, 306, 308, 312, 320, 326, 336, 338, 342, 350, 366,
    372, 378, 380, 386, 396, 398, 420, 422, 428, 432, 438, 440, 450, 462, 470, 476, 482, 488,
    492, 498, 506, 510, 512, 516, 518, 536, 546, 548, 558, 572, 576, 590, 600, 602, 606, 618,
    620, 638, 648, 650, 656, 662, 672, 690, 692, 702, 708, 716, 722, 726, 740, 746, 756, 762,
    768, 776, 782, 792, 798, 806, 810, 812, 818, 828, 840, 846, 858, 860, 866, 870, 872, 876,
    882, 888, 890, 900, 912, 926, 930, 938, 942, 950, 956, 960, 966, 968, 980, 986, 992, 1008,
    1020, 1022, 1026, 1040, 1052, 1056, 1058, 1062, 1068, 1080, 1082, 1086, 1098, 1110, 1112,
    1118, 1122, 1142, 1146, 1148, 1166, 1170, 1176, 1178, 1188, 1190, 1196, 1202, 1212, 1220,
    1236, 1238, 1250, 1260, 1262, 1266, 1272, 1278, 1290, 1296, 1302, 1308, 1328, 1332, 1346,
    1350, 1352, 1356, 1370, 1376, 1392, 1400, 1406, 1416, 1418, 1428, 1430, 1436, 1442, 1448,
    1458, 1470, 1476, 1478, 1488, 1496, 1500, 1502, 1520, 1530, 1532, 1538, 1542, 1560, 1566,
    1568, 1580, 1590, 1602, 1608, 1610, 1626, 1632, 1638, 1640, 1646, 1652, 1656, 1670, 1680,
    1682, 1692, 1706, 1712, 1716, 1722, 1728, 1730, 1748, 1758, 1766, 1770, 1772, 1790, 1796,
    1800, 1806, 1812, 1818, 1826, 1832, 1836, 1838, 1848, 1850, 1862, 1866, 1868, 1878, 1880,
    1892, 1896, 1898, 1902, 1910, 1916, 1926, 1932, 1938, 1940, 1946, 1962, 1980, 1982, 1988,
    1992, 2000, 2006, 2016, 2022, 2028, 2036, 2046, 2048, 2052, 2060, 2066, 2070, 2072, 2076,
    2078, 2088, 2102, 2108, 2112, 2120, 2130, 2132, 2148, 2162, 2178, 2186, 2190, 2192, 2198,
    2202, 2210, 2226, 2240, 2252, 2256, 2258, 2268, 2280, 2286, 2310, 2312, 2316, 2318, 2322,
    2336, 2342, 2352, 2358, 2360, 2366, 2372, 2388, 2396, 2400, 2406, 2408, 2412, 2430, 2438,
    2442, 2450, 2456, 2462, 2468, 2478, 2486, 2490, 2492, 2496, 2508, 2510, 2522, 2528, 2538,
    2540, 2552, 2562, 2570, 2576, 2580, 2582, 2592, 2598, 2606, 2616, 2618, 2622, 2630, 2640,
    2648, 2652, 2658, 2660, 2666, 2676, 2682, 2690, 2696, 2706, 2708, 2718, 2732, 2736, 2742,
    2750, 2756, 2760, 2762, 2778, 2786, 2790, 2798, 2808, 2820, 2822, 2826, 2828, 2850, 2856,
    2858, 2862, 2868, 2882, 2888, 2892, 2900, 2910, 2912, 2918, 2928, 2930, 2940, 2952, 2958,
    2966, 2970, 2972, 2982, 2990, 2996, 3002, 3018, 3036, 3042, 3050, 3056, 3060, 3066, 3072,
    3080, 3086, 3092, 3098, 3102, 3110, 3122, 3126, 3128, 3138, 3150, 3152, 3158]

def witness : List ℕ :=
  [1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 10, 1, 1, 1, 1, 1, 9, 1, 1, 1, 11, 1, 4, 1, 1, 1, 4, 1, 15,
    1, 1, 1, 3, 1, 34, 1, 1, 1, 4, 1, 21, 1, 1, 1, 23, 1, 3, 1, 1, 1, 44, 1, 4, 1, 1, 1, 29, 1,
    26, 1, 1, 1, 4, 1, 33, 1, 1, 1, 35, 1, 39, 1, 1, 1, 3, 1, 39, 1, 1, 1, 41, 1, 1, 1, 1, 1,
    51, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 1, 25, 1, 51, 1, 1, 1, 53, 1, 89, 1, 1, 1, 13, 1, 4, 1, 1,
    1, 1, 1, 5, 1, 1, 1, 4, 1, 63, 1, 1, 1, 65, 1, 3, 1, 1, 1, 40, 1, 69, 1, 1, 1, 5, 1, 4, 1,
    1, 1, 64, 1, 75, 1, 1, 1, 4, 1, 9, 1, 1, 1, 3, 1, 81, 1, 1, 1, 26, 1, 10, 1, 1, 1, 15, 1, 3,
    1, 1, 1, 1, 1, 39, 1, 1, 1, 4, 1, 1, 1, 1, 1, 41, 1, 28, 1, 1, 1, 5, 1, 28, 1, 1, 1, 3, 1,
    4, 1, 1, 1, 5, 1, 9, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 35, 1, 1, 1, 24, 1, 55, 1, 1, 1, 64,
    1, 4, 1, 1, 1, 46, 1, 13, 1, 1, 1, 3, 1, 7, 1, 1, 1, 19, 1, 5, 1, 1, 1, 77, 1, 3, 1, 1, 1,
    1, 1, 4, 1, 1, 1, 14, 1, 25, 1, 1, 1, 4, 1, 26, 1, 1, 1, 5, 1, 31, 1, 1, 1, 3, 1, 1, 1, 1,
    1, 17, 1, 4, 1, 1, 1, 10, 1, 3, 1, 1, 1, 4, 1, 11, 1, 1, 1, 3, 1, 16, 1, 1, 1, 1, 1, 4, 1,
    1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 9, 1, 1, 1, 4, 1, 19, 1, 1, 1, 5, 1, 3, 1, 1, 1, 7, 1, 41, 1,
    1, 1, 11, 1, 4, 1, 1, 1, 14, 1, 9, 1, 1, 1, 4, 1, 14, 1, 1, 1, 3, 1, 9, 1, 1, 1, 4, 1, 25,
    1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 9, 1, 1, 1, 3, 1, 9, 1, 1, 1, 3, 1, 17,
    1, 1, 1, 3, 1, 4, 1, 1, 1, 10, 1, 10, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 5,
    1, 1, 1, 5, 1, 3, 1, 1]

theorem tuple_length : tuple.length = 447 := by decide +kernel

theorem tuple_chain : tuple.IsChain (· < ·) := by decide +kernel

theorem tuple_even_le :
    tuple.all (fun x => x % 2 == 0 && decide (x ≤ 3158)) = true := by
  decide +kernel

theorem witness_ok :
    ((List.range' 2 446).zip witness).all
      (fun qr => decide (qr.2 < qr.1) && tuple.all fun x => x % qr.1 != qr.2) = true := by
  decide +kernel

theorem witness_length : witness.length = 446 := by decide +kernel

/-! ### `π(3159) ≤ 446` by trial division in the kernel -/

/-- Trial division of `n` by `k, k + 1, …`, stopping once `k * k > n`; `fuel` bounds the steps. -/
def trialOK (n : ℕ) : ℕ → ℕ → Bool
  | 0, k => decide (n < k * k)
  | fuel + 1, k => decide (n < k * k) || (n % k != 0 && trialOK n fuel (k + 1))

/-- A Boolean primality test, complete for primes (`isPrimeB_of_prime`). -/
def isPrimeB (n : ℕ) : Bool := decide (2 ≤ n) && trialOK n n 2

lemma trialOK_of_prime {n : ℕ} (hn : n.Prime) :
    ∀ fuel k, 2 ≤ k → n + 1 ≤ fuel + k → trialOK n fuel k = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro k hk hfk
    simp only [trialOK, decide_eq_true_eq]
    nlinarith
  | succ fuel ih =>
    intro k hk hfk
    simp only [trialOK, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq]
    by_cases hlt : n < k * k
    · exact Or.inl hlt
    · right
      refine ⟨fun h0 => ?_, ih (k + 1) (by omega) (by omega)⟩
      have hkn : k < n := by nlinarith
      rcases hn.eq_one_or_self_of_dvd k (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega

lemma isPrimeB_of_prime {n : ℕ} (hn : n.Prime) : isPrimeB n = true := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hn.two_le, trialOK_of_prime hn n 2 le_rfl (by omega)⟩

theorem count_isPrimeB : Nat.count (fun n => isPrimeB n = true) 3160 = 446 := by
  decide +kernel

/-- `π(3159) ≤ 446` (in fact `= 446`). -/
theorem primeCounting_3159_le : Nat.primeCounting 3159 ≤ 446 := by
  show Nat.count Nat.Prime 3160 ≤ 446
  rw [← count_isPrimeB]
  exact Nat.count_mono_left fun k _ hk => isPrimeB_of_prime hk

end HardyLittlewood.Richards

/-!
# Richards' theorem: the two Hardy–Littlewood conjectures are incompatible

Hensley and Richards (*Acta Arith.* 25 (1973/74), 375–391) and Richards (*Bull. Amer. Math.
Soc.* 80 (1974), 419–438) showed that the first Hardy–Littlewood conjecture (the prime
`k`-tuples conjecture with the Hardy–Littlewood constant) contradicts the second,
`π(x + y) ≤ π(x) + π(y)`. This file proves formal-conjectures'
`HardyLittlewood.not_first_and_secondHardyLittlewoodConjecture`, with its statement unchanged.

Proof.

1. `tuple` (`Implications.HardyLittlewood.Tuple`) is an admissible 447-tuple
   `0 = m₀ < ⋯ < m₄₄₆ = 3158` of even numbers, while `π(3159) = 446`.
2. Its Hardy–Littlewood constant is positive (`tprod_pos`): every factor is positive because
   the tuple misses a class mod every prime, and for `q > 3158` the factor
   `(1 - 447/q)/(1 - 1/q)^447` is within `2·447²/q²` of `1` (`factor_sub_one_le'`), so the logs of
   the factors are summable and the product is the exponential of their sum.
3. The integral `∫ t in 2..n, 1/log t ^ 447` is positive for `n ≥ 3`, so the first conjecture
   makes the counting function of the constellation eventually nonzero: some `p` has all 447
   numbers `p + mᵢ` prime (`exists_constellation`).
4. These are 447 primes in `[p, p + 3158]`, so `π(p - 1 + 3159) ≥ π(p - 1) + 447`, while the
   second conjecture at `x = p - 1 ≥ 2`, `y = 3159` gives at most `π(p - 1) + 446`.
-/

open Asymptotics Filter

open scoped Nat.Prime

namespace HardyLittlewood.Richards

/-- The 447-tuple as a function on `Fin 447`. -/
def m : Fin (Nat.succ 446) → ℕ := fun i => tuple.get (Fin.cast tuple_length.symm i)

lemma tuple_pairwise : tuple.Pairwise (· < ·) := List.isChain_iff_pairwise.mp tuple_chain

lemma tuple_nodup : tuple.Nodup := tuple_pairwise.imp fun h => ne_of_lt h

lemma m_mem (i : Fin (Nat.succ 446)) : m i ∈ tuple := List.get_mem _ _

lemma mem_tuple_iff (x : ℕ) : x ∈ tuple ↔ ∃ i, m i = x := by
  rw [List.mem_iff_get]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.cast tuple_length j, by simp [m]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.cast tuple_length.symm i, rfl⟩

lemma even_le_of_mem {x : ℕ} (hx : x ∈ tuple) : x % 2 = 0 ∧ x ≤ 3158 := by
  have := List.all_eq_true.mp tuple_even_le x hx
  simpa using this

lemma m_zero : m 0 = 0 := rfl

lemma m_one : m 1 = 2 := rfl

lemma m_injective : Function.Injective m := by
  intro i j h
  have := (List.nodup_iff_injective_get.mp tuple_nodup) h
  exact Fin.cast_injective _ this

lemma m_even (i : Fin (Nat.succ 446)) : Even (m i) :=
  Nat.even_iff.mpr (even_le_of_mem (m_mem i)).1

lemma m_le (i : Fin (Nat.succ 446)) : m i ≤ 3158 := (even_le_of_mem (m_mem i)).2

/-- For `2 ≤ q ≤ 447` some residue class mod `q` contains no `mᵢ`. -/
lemma exists_missing (q : ℕ) (hq2 : 2 ≤ q) (hq : q ≤ 447) :
    ∃ r < q, ∀ i, m i % q ≠ r := by
  have hj : q - 2 < ((List.range' 2 446).zip witness).length := by
    simp [witness_length]; omega
  have hmem := List.getElem_mem hj
  have h := List.all_eq_true.mp witness_ok _ hmem
  simp only [List.getElem_zip, List.getElem_range', Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, bne_iff_ne, ne_eq, one_mul] at h
  have hq' : 2 + (q - 2) = q := by omega
  rw [hq'] at h
  refine ⟨_, h.1, fun i => h.2 _ (m_mem i)⟩

/-- The number of classes mod `q` met by the tuple is below `q`, for every prime `q`. -/
lemma numResidues_lt (q : ℕ) (hq : q.Prime) : Nat.numResidues q m < q := by
  have : NeZero q := ⟨hq.ne_zero⟩
  unfold Nat.numResidues
  rcases le_or_gt q 447 with hle | hgt
  · obtain ⟨r, hr, hmiss⟩ := exists_missing q hq.two_le hle
    have hne : Set.range (fun i => (m i : ZMod q)) ≠ Set.univ := by
      intro h
      obtain ⟨i, hi⟩ := (Set.eq_univ_iff_forall.mp h) (r : ZMod q)
      have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hi
      rw [Nat.mod_eq_of_lt hr] at this
      exact hmiss i this
    calc _ < Nat.card (ZMod q) := Set.ncard_lt_card hne
      _ = q := Nat.card_zmod q
  · calc _ ≤ (Set.univ : Set (Fin (Nat.succ 446))).ncard := by
          rw [← Set.image_univ]; exact Set.ncard_image_le (Set.toFinite _)
      _ = 447 := by simp
      _ < q := hgt

/-- For `q > 3158` the 447 entries lie in distinct classes. -/
lemma numResidues_eq (q : ℕ) (hq : 3158 < q) : Nat.numResidues q m = 447 := by
  unfold Nat.numResidues
  have hinj : Function.Injective (fun i => (m i : ZMod q)) := by
    intro i j h
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
    rw [Nat.mod_eq_of_lt (by have := m_le i; omega),
      Nat.mod_eq_of_lt (by have := m_le j; omega)] at this
    exact m_injective this
  rw [Set.ncard_range_of_injective hinj]
  simp

/-! ### The analytic part, for a general tuple

Everything below is stated for an arbitrary `t : Fin k.succ → ℕ`, with the arithmetic input as
hypotheses; it is applied to `m` (with `k = 446`) only at the end. -/

/-- The elementary estimate behind the convergence of the singular series:
`|(1 - n x)/(1 - x)^n - 1| ≤ 2 n² x²` when `0 < x` and `n x ≤ 1/2`. -/
lemma factor_sub_one_le (n : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1' : x ≤ 1)
    (hx1 : (n : ℝ) * x ≤ 1 / 2) :
    |(1 - n * x) / (1 - x) ^ n - 1| ≤ 2 * (n : ℝ) ^ 2 * x ^ 2 := by
  have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg n) hx0.le
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (1 - x) ^ n := ⟨_, rfl⟩
  rw [← hP]
  have hlow : 1 - n * x ≤ P := by
    have h := one_add_mul_le_pow (a := -x) (by linarith) n
    rw [← sub_eq_add_neg, ← hP] at h
    linarith
  have hup : P ≤ 1 - n * x + (n * x) ^ 2 := by
    have h1 : P ≤ Real.exp (-x) ^ n := by
      rw [hP]
      exact pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg x) n
    have h2 : Real.exp (-x) ^ n = Real.exp (-(n * x)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h3 := Real.abs_exp_sub_one_sub_id_le (x := -(n * x))
      (by rw [abs_neg, abs_of_nonneg hnx]; linarith)
    have h4 := (abs_le.mp h3).2
    rw [neg_sq] at h4
    linarith
  have hP0 : 0 < P := by linarith
  rw [div_sub_one hP0.ne', abs_div, abs_of_pos hP0, div_le_iff₀ hP0,
    abs_of_nonpos (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg x))
    (by linarith : (0 : ℝ) ≤ 2 * P - 1)]

/-- The same estimate at `x = 1/q`. -/
lemma factor_sub_one_le' (n : ℕ) (q : ℝ) (hq : 2 * (n : ℝ) ≤ q) (hq1 : 1 ≤ q) :
    |(1 - (n : ℝ) / q) / (1 - 1 / q) ^ n - 1| ≤ 2 * (n : ℝ) ^ 2 * (1 / q ^ 2) := by
  have hq0 : 0 < q := by linarith
  have h := factor_sub_one_le n (1 / q) (by positivity) (by rw [div_le_one hq0]; exact hq1)
    (by rw [mul_one_div, div_le_iff₀ hq0]; linarith)
  rwa [mul_one_div, one_div_pow] at h

/-- A product of Hardy–Littlewood factors is positive when the tuple misses a class mod every
prime and occupies `k + 1` distinct classes mod every large prime. -/
lemma tprod_pos {k : ℕ} (t : Fin k.succ → ℕ) (B : ℕ)
    (hlt : ∀ q : ℕ, q.Prime → Nat.numResidues q t < q)
    (heq : ∀ q : ℕ, B < q → Nat.numResidues q t = k.succ) :
    0 < ∏' (q : { q : ℕ // q.Prime ∧ 3 ≤ q}),
        (1 - (Nat.numResidues q t : ℝ) / q) / (1 - 1 / q) ^ k.succ := by
  set f : { q : ℕ // q.Prime ∧ 3 ≤ q} → ℝ :=
    fun q => (1 - (Nat.numResidues q t : ℝ) / q) / (1 - 1 / q) ^ k.succ with hf
  have hpos : ∀ q, 0 < f q := by
    intro q
    have hq3 : (3 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.2.2
    have hl : (Nat.numResidues q t : ℝ) < (q : ℕ) := by exact_mod_cast hlt q q.2.1
    apply div_pos
    · rw [sub_pos, div_lt_one (by linarith)]; exact hl
    · apply pow_pos
      rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hg : Summable fun q => f q - 1 := by
    have hs : Summable fun q : { q : ℕ // q.Prime ∧ 3 ≤ q} =>
        2 * ((k.succ : ℕ) : ℝ) ^ 2 * (1 / ((q : ℕ) : ℝ) ^ 2) :=
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective
        Subtype.val_injective).mul_left _
    refine hs.of_norm_bounded_eventually ?_
    rw [Filter.eventually_cofinite]
    refine ((Set.finite_Iic (B + 2 * k.succ)).preimage Subtype.val_injective.injOn).subset ?_
    intro q hq
    simp only [Set.mem_preimage, Set.mem_Iic]
    by_contra hbig
    apply hq
    have hbig' : B + 2 * k.succ < (q : ℕ) := by omega
    have hq' : 2 * ((k.succ : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 * k.succ ≤ (q : ℕ))
    have hq1 : (1 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (q : ℕ))
    rw [Real.norm_eq_abs, hf]
    dsimp only
    rw [heq _ (by omega)]
    exact factor_sub_one_le' k.succ _ hq' hq1
  have hlog : Summable fun q => Real.log (f q) :=
    (Real.summable_log_one_add_of_summable hg).congr fun q => by rw [add_sub_cancel]
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  exact Real.exp_pos _

lemma integral_pos (k : ℕ) {n : ℝ} (hn : 3 ≤ n) :
    0 < ∫ t in (2 : ℝ)..n, 1 / t.log ^ k.succ := by
  have hI : Set.uIcc (2 : ℝ) n = Set.Icc 2 n := Set.uIcc_of_le (by linarith)
  have hpos : ∀ t ∈ Set.uIcc (2 : ℝ) n, 0 < Real.log t := by
    intro t ht
    rw [hI] at ht
    exact Real.log_pos (by linarith [ht.1])
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div continuousOn_const
      ((Real.continuousOn_log.mono fun t ht => ?_).pow k.succ) fun t ht => ?_
    · rw [hI] at ht
      exact Set.mem_compl_singleton_iff.mpr (by linarith [ht.1] : (0 : ℝ) < t).ne'
    · show Real.log t ^ k.succ ≠ 0
      exact pow_ne_zero _ (hpos t ht).ne'
  · intro t ht
    have : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    positivity
  · linarith

/-- If the first Hardy–Littlewood conjecture holds for `t` and its constant is positive, some
`p` makes every `p + tᵢ` prime. -/
lemma exists_constellation_of {k : ℕ} (t : Fin k.succ → ℕ) (B : ℕ)
    (h0 : t 0 = 0) (hev : ∀ i ≠ 0, Even (t i)) (hinj : Function.Injective t)
    (hlt : ∀ q : ℕ, q.Prime → Nat.numResidues q t < q)
    (heq : ∀ q : ℕ, B < q → Nat.numResidues q t = k.succ)
    (hHL : FirstHardyLittlewoodConjectureFor t) :
    ∃ p, ∀ i, (p + t i).Prime := by
  classical
  have h := hHL h0 hev hinj
  dsimp only at h
  have hC := tprod_pos t B hlt heq
  have hv : ∀ᶠ n : ℕ in atTop,
      (2 ^ k * ∏' (q : { q : ℕ // q.Prime ∧ 3 ≤ q}),
        (1 - (Nat.numResidues q t : ℝ) / q) / (1 - 1 / q) ^ k.succ) *
        (∫ x in (2 : ℝ)..n, 1 / x.log ^ k.succ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact (mul_pos (mul_pos (by positivity) hC)
      (integral_pos k (by exact_mod_cast hn))).ne'
  obtain ⟨n, hn1, hn2⟩ := (hv.and h.isBigO_symm.eq_zero_imp).exists
  have hcount : Nat.primeTupleCounting t n ≠ 0 := by
    intro h0; exact hn1 (hn2 (by simp [h0]))
  unfold Nat.primeTupleCounting at hcount
  rw [Nat.count_eq_card_filter_range, Finset.card_ne_zero] at hcount
  obtain ⟨p, hp⟩ := hcount
  exact ⟨p, (Finset.mem_filter.mp hp).2.1.2.2⟩

/-- Under the first Hardy–Littlewood conjecture, some `p` makes every `p + mᵢ` prime. -/
lemma exists_constellation
    (hHL : ∀ {k : ℕ} (m : Fin k.succ → ℕ), FirstHardyLittlewoodConjectureFor m) :
    ∃ p, ∀ i, (p + m i).Prime :=
  exists_constellation_of m 3158 m_zero (fun i _ => m_even i) m_injective numResidues_lt
    numResidues_eq (hHL (k := 446) m)

end HardyLittlewood.Richards

open HardyLittlewood HardyLittlewood.Richards in
theorem OMA.solution : type_of% @HardyLittlewood.not_first_and_secondHardyLittlewoodConjecture := by
  intro hHL hHL2
  obtain ⟨p, hp⟩ := exists_constellation hHL
  -- `p` is odd: `p` and `p + 2` are both prime.
  have hp3 : 3 ≤ p := by
    have h0 := hp 0
    have h1 := hp 1
    rw [m_zero] at h0
    rw [m_one] at h1
    have h2 := h0.two_le
    by_contra hlt
    have : p = 2 := by omega
    subst this
    exact absurd h1 (by norm_num)
  have h2 := hHL2 (x := p - 1) (y := 3159) (by omega) (by norm_num)
  unfold SecondHardyLittlewoodConjectureFor at h2
  have h3 := primeCounting_3159_le
  generalize π 3159 = c at h2 h3
  unfold Nat.primeCounting Nat.primeCounting' at h2
  have e1 : p - 1 + 3159 + 1 = p + 3159 := by omega
  have e2 : p - 1 + 1 = p := by omega
  rw [e1, e2, Nat.count_add] at h2
  -- the 447 entries of the tuple give 447 primes `p + x` with `x < 3159`
  have hcard : 447 ≤ Nat.count (fun k => (p + k).Prime) 3159 := by
    rw [Nat.count_eq_card_filter_range]
    calc 447 = tuple.toFinset.card := by
            rw [List.toFinset_card_of_nodup tuple_nodup, tuple_length]
      _ ≤ _ := by
        apply Finset.card_le_card
        intro x hx
        rw [List.mem_toFinset] at hx
        obtain ⟨i, rfl⟩ := (mem_tuple_iff x).mp hx
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by have := m_le i; omega, hp i⟩
  omega
