import FormalConjectures.ErdosProblems.«437»
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
The density of square partial products in Erdős problem 437.
We prove the finite upper counting bound from Halldon's proof of Tao's upper
estimate and use Mathlib's bound for smooth numbers at a fixed cutoff.
At a nonsmooth square-producing endpoint outside the large-square exceptions,
a large prime occurs exactly once. Its valuation must have changed since any
previous square-producing endpoint, so those two endpoints differ by at least
the smoothness cutoff. Counting their distinct integer quotients gives the gap
term. A sum over square divisors bounds the exceptional endpoints.
-/

namespace SquareEndpointBound

open Erdos437

private lemma val_lt {a : List ℕ} (ha : a.Pairwise (· < ·)) {i j : ℕ}
    (hij : i < j) (hj : j < a.length) : a[i]! < a[j]! := by
  simpa [getElem!_pos, hj, hij.trans hj] using
    (List.pairwise_iff_getElem.mp ha i j (hij.trans hj) hj hij)

private lemma prefix_ne_zero {a : List ℕ} (ha : ∀ n ∈ a, 0 < n) (i : ℕ) :
    (a.take i).prod ≠ 0 := by
  apply List.prod_ne_zero
  intro h
  exact (ha 0 (List.mem_of_mem_take h)).false

private lemma prefix_step {a : List ℕ} (ha : ∀ n ∈ a, 0 < n) {j : ℕ} (hj : j < a.length)
    (p : ℕ) : (a.take (j+1)).prod.factorization p =
    (a.take j).prod.factorization p + (a[j]!).factorization p := by
  rw [List.take_succ_eq_append_getElem hj, List.prod_append, List.prod_singleton,
    Nat.factorization_mul (prefix_ne_zero ha _) (ha _ (List.getElem_mem _)).ne',
    Finsupp.add_apply]
  simp [hj]

private lemma prefix_stable {a : List ℕ} (ha : ∀ n ∈ a, 0 < n) (p : ℕ) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ a.length)
    (h : ∀ k, i ≤ k → k < j → ¬p ∣ a[k]!) :
    (a.take j).prod.factorization p = (a.take i).prod.factorization p := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    simp [this]
  | succ j ih =>
    by_cases heq : i = j+1
    · simp [heq]
    · rw [prefix_step ha (by omega : j < a.length) p,
        Nat.factorization_eq_zero_of_not_dvd (h j (by omega) (by omega)), add_zero]
      exact ih (by omega) (by omega) (fun k hk hkj => h k hk (by omega))

private lemma even_square_val {n : ℕ} (hs : IsSquare n) (p : ℕ) : Even (n.factorization p) := by
  obtain ⟨s, rfl⟩ := hs
  rw [← sq, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  exact ⟨s.factorization p, by omega⟩

private lemma separated {a : List ℕ} (ha : a.Pairwise (· < ·)) (hpos : ∀ n ∈ a, 0 < n)
    {i j p : ℕ} (hij : i < j) (hj : j < a.length)
    (hsi : IsSquare (a.take (i+1)).prod) (hsj : IsSquare (a.take (j+1)).prod)
    (hp : p.Prime) (hdiv : p ∣ a[j]!) (hsq : ¬p^2 ∣ a[j]!) :
    a[i]! + p ≤ a[j]! := by
  by_contra! hshort
  have hmid : ∀ k, i+1 ≤ k → k < j → ¬p ∣ a[k]! := by
    intro k hik hkj hk
    have h₁ := val_lt ha (by omega : i < k) (hkj.trans hj)
    have h₂ := val_lt ha hkj hj
    have h₃ := Nat.le_of_dvd (Nat.sub_pos_of_lt h₂) (Nat.dvd_sub hdiv hk)
    omega
  have hjpos : 0 < a[j]! := by simpa [getElem!_pos, hj] using hpos _ (List.getElem_mem (l := a) hj)
  have hone : (a[j]!).factorization p = 1 := by
    have hg := (hp.dvd_iff_one_le_factorization hjpos.ne').mp hdiv
    have hnot := mt (hp.pow_dvd_iff_le_factorization hjpos.ne').mpr hsq
    omega
  obtain ⟨u, hu⟩ := even_square_val hsi p
  obtain ⟨v, hv⟩ := even_square_val hsj p
  rw [prefix_step hpos hj p, prefix_stable hpos p (i+1) j (by omega) (by omega) hmid,
    hone, hu] at hv
  omega

private def exceptions (x y : ℕ) := (Finset.Icc y x).biUnion fun p =>
  (Finset.range (x+1)).filter fun n => n ≠ 0 ∧ p^2 ∣ n

private lemma large_prime {x y n : ℕ} (hn : 0 < n) (hx : n ≤ x)
    (h : n ∉ x.smoothNumbersUpTo y ∪ exceptions x y) :
    ∃ p, p.Prime ∧ y ≤ p ∧ p ∣ n ∧ ¬ p^2 ∣ n := by
  have hs : n ∉ x.smoothNumbersUpTo y := fun hg => h (Finset.mem_union_left _ hg)
  have hns : n ∉ Nat.smoothNumbers y := fun hg => hs (Nat.mem_smoothNumbersUpTo.mpr ⟨hx,hg⟩)
  rw [Nat.mem_smoothNumbers'] at hns
  push Not at hns
  obtain ⟨p,hp,hd,hy⟩ := hns
  refine ⟨p,hp,hy,hd,?_⟩
  intro hsq
  apply h
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_Icc.mpr ⟨hy,(Nat.le_of_dvd hn hd).trans hx⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hn.ne',hsq⟩⟩

private lemma count_endpoints {x y : ℕ} (hy : 2 ≤ y) (a : List ℕ) (ha : a.Pairwise (· < ·))
    (hax : ∀ n ∈ a, n ∈ Finset.Icc 1 x) :
    squarePartialProducts a ≤ (x.smoothNumbersUpTo y ∪ exceptions x y).card + x / y := by
  classical
  let S := (Finset.range a.length).filter fun i => IsSquare (a.take (i+1)).prod
  let G := x.smoothNumbersUpTo y ∪ exceptions x y
  let small := S.filter fun i => a[i]! ∈ G
  let sparse := S.filter fun i => a[i]! ∉ G
  have hS {i : ℕ} (h : i ∈ S) : i < a.length ∧ IsSquare (a.take (i+1)).prod := by
    simpa [S] using h
  have hpos : ∀ n ∈ a, 0 < n := fun n hn => (Finset.mem_Icc.mp (hax n hn)).1
  have hv {i : ℕ} (hi : i < a.length) : 0 < a[i]! ∧ a[i]! ≤ x := by
    have hh := Finset.mem_Icc.mp (hax _ (List.getElem_mem (l := a) hi))
    simp only [getElem!_pos a i hi]
    exact ⟨by omega, hh.2⟩
  have hgood : small.card ≤ G.card := by
    refine Finset.card_le_card_of_injOn (fun i : ℕ => a[i]!) (fun i hi => (Finset.mem_filter.mp hi).2) ?_
    intro i hi j hj heq
    have hi' := (hS (Finset.mem_filter.mp hi).1).1
    have hj' := (hS (Finset.mem_filter.mp hj).1).1
    rcases lt_trichotomy i j with h | h | h
    · exact False.elim ((val_lt ha h hj').ne heq)
    · exact h
    · exact False.elim ((val_lt ha h hi').ne heq.symm)
  have hsep {i j : ℕ} (hi : i ∈ sparse) (hj : j ∈ sparse) (hij : i < j) :
      a[i]! / y < a[j]! / y := by
    obtain ⟨hiS, _⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjS, hn⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjlen,hsj⟩ := hS hjS
    obtain ⟨p,hp,hyp,hd,hns⟩ := large_prime (hv hjlen).1 (hv hjlen).2 hn
    have hgap := separated ha hpos hij hjlen (hS hiS).2 hsj hp hd hns
    have hdv := Nat.div_le_div_right (c := y) (show a[i]! + y ≤ a[j]! by omega)
    rw [Nat.add_div_right _ (by omega : 0 < y)] at hdv
    omega
  have hsparse : sparse.card ≤ x / y := by
    have hh : sparse.card ≤ (Finset.Icc 1 (x/y)).card := by
      refine Finset.card_le_card_of_injOn (fun i : ℕ => a[i]! / y) ?_ ?_
      · intro i hi
        obtain ⟨his, hn⟩ := Finset.mem_filter.mp hi
        obtain ⟨hnpos, hnx⟩ := hv (hS his).1
        obtain ⟨p,hp,hyp,hd,_⟩ := large_prime hnpos hnx hn
        apply Finset.mem_Icc.mpr
        refine ⟨?_,Nat.div_le_div_right hnx⟩
        exact Nat.div_pos (hyp.trans (Nat.le_of_dvd hnpos hd)) (by omega)
      · intro i hi j hj heq
        rcases lt_trichotomy i j with h | h | h
        · exact False.elim ((hsep hi hj h).ne heq)
        · exact h
        · exact False.elim ((hsep hj hi h).ne heq.symm)
    simpa [Nat.card_Icc] using hh
  have hn : small.card + sparse.card = S.card := Finset.card_filter_add_card_filter_not ..
  change S.card ≤ G.card + x / y
  omega

private lemma count_max (x y : ℕ) (hy : 2 ≤ y) :
    L x ≤ (x.smoothNumbersUpTo y ∪ exceptions x y).card + x / y := by
  unfold L
  apply csSup_le
  · exact ⟨0, [], by simp, by simp, by simp [squarePartialProducts]⟩
  · rintro m ⟨a, ha, hax, rfl⟩
    exact count_endpoints hy a ha hax

end SquareEndpointBound

open Finset

lemma largeSquareCount (x y : ℕ) (hy : 2 ≤ y) :
    (((Icc y x).biUnion fun p => (range (x + 1)).filter fun n => n ≠ 0 ∧ p^2 ∣ n).card : ℝ) ≤
      2 * x / y := by
  classical
  by_cases hxy : y ≤ x
  · let f : ℕ → ℝ := fun i => -(2 * (x : ℝ) / i)
    calc
      _ ≤ ∑ p ∈ Icc y x, (((range (x+1)).filter fun n => n ≠ 0 ∧ p^2 ∣ n).card : ℝ) := by
        exact_mod_cast (card_biUnion_le (s := Icc y x)
          (t := fun p => (range (x+1)).filter fun n => n ≠ 0 ∧ p^2 ∣ n))
      _ ≤ ∑ p ∈ Icc y x, (f (p+1) - f p) := by
        apply sum_le_sum
        intro p hp
        rw [Nat.card_multiples']
        have hyp := (mem_Icc.mp hp).1
        have h1 : 1 ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
        have hp0 : (0 : ℝ) < p := by linarith
        calc
          ((x / p^2 : ℕ) : ℝ) ≤ (x : ℝ) / (p : ℝ)^2 := by
            have e : ((p ^ 2 : ℕ) : ℝ) = (p : ℝ) ^ 2 := by push_cast; rfl
            rw [← e]
            exact Nat.cast_div_le
          _ ≤ f (p+1) - f p := by
            dsimp [f]
            push_cast
            field_simp
            nlinarith [mul_nonneg (show 0 ≤ (x : ℝ) by positivity) (sub_nonneg.mpr h1)]
      _ = f (x+1) - f y := sum_Icc_sub hxy f
      _ ≤ 2 * x / y := by
        dsimp [f]
        linarith [show 0 ≤ 2 * (x : ℝ) / (↑(x+1 : ℕ) : ℝ) by positivity]
  · simp [Icc_eq_empty_of_lt (by omega : x < y)]
    positivity

private lemma endpoint_count_bound (x y : ℕ) (hy : 2 ≤ y) :
    (Erdos437.L x : ℝ) ≤ ((x.smoothNumbersUpTo y).card : ℝ) + 3 * x / y := by
  have h₁ : (Erdos437.L x : ℝ) ≤
      ((x.smoothNumbersUpTo y ∪ SquareEndpointBound.exceptions x y).card : ℝ) + ((x / y : ℕ) : ℝ) := by
    exact_mod_cast SquareEndpointBound.count_max x y hy
  have h₂ : ((x.smoothNumbersUpTo y ∪ SquareEndpointBound.exceptions x y).card : ℝ) ≤
      ((x.smoothNumbersUpTo y).card : ℝ) + ((SquareEndpointBound.exceptions x y).card : ℝ) := by
    exact_mod_cast Finset.card_union_le (x.smoothNumbersUpTo y) (SquareEndpointBound.exceptions x y)
  have h₃ : ((SquareEndpointBound.exceptions x y).card : ℝ) ≤ 2 * (x : ℝ) / y :=
    largeSquareCount x y hy
  have h₄ := Nat.cast_div_le (α := ℝ) (m := x) (n := y)
  calc
    _ ≤ _ := h₁
    _ ≤ (((x.smoothNumbersUpTo y).card : ℝ) + 2 * (x : ℝ) / y) + (x : ℝ) / y :=
      add_le_add (h₂.trans (add_le_add (le_refl _) h₃)) h₄
    _ = _ := by ring


open Filter

private lemma sparse_squares_little_o (f : ℕ → ℕ)
    (hbound : ∀ x y : ℕ, 2 ≤ y →
      (f x : ℝ) ≤ ((x.smoothNumbersUpTo y).card : ℝ) + 3 * x / y) :
    (fun x : ℕ ↦ (f x : ℝ)) =o[atTop] fun x : ℕ ↦ (x : ℝ) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨k, hk⟩ := exists_nat_gt (6 / c)
  let y : ℕ := max k 2
  have hy : 2 ≤ y := le_max_right _ _
  have hky : (k : ℝ) ≤ y := by exact_mod_cast (le_max_left k 2)
  have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hcy : 6 ≤ (y : ℝ) * c := ((div_lt_iff₀ hc).mp (hk.trans_le hky)).le
  have hcoef : (3 : ℝ) / y ≤ c / 2 := by
    apply (div_le_iff₀ hypos).mpr
    nlinarith
  let C : ℕ := 2 ^ y.primesBelow.card
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (C : ℝ) / c)
  filter_upwards [eventually_ge_atTop (N * N)] with x hx
  have hroot : (N : ℝ) ≤ x.sqrt := by exact_mod_cast Nat.le_sqrt.mpr hx
  have hC : (C : ℝ) ≤ (c / 2) * (x.sqrt : ℝ) := by
    have h := (div_lt_iff₀ hc).mp (hN.trans_le hroot)
    nlinarith
  have hsmooth : ((x.smoothNumbersUpTo y).card : ℝ) ≤ (c / 2) * x := by
    calc
      _ ≤ (C : ℝ) * (x.sqrt : ℝ) := by
        exact_mod_cast Nat.smoothNumbersUpTo_card_le x y
      _ ≤ ((c / 2) * (x.sqrt : ℝ)) * (x.sqrt : ℝ) := by
        exact mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (by exact_mod_cast Nat.sqrt_le x : (x.sqrt : ℝ) * (x.sqrt : ℝ) ≤ (x : ℝ))
          (by positivity)
  have htail := mul_le_mul_of_nonneg_right hcoef (show (0 : ℝ) ≤ x by positivity)
  have h := hbound x y hy
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  calc
    (f x : ℝ) ≤ _ := h
    _ = ((x.smoothNumbersUpTo y).card : ℝ) + (3 / (y : ℝ)) * x := by ring
    _ ≤ (c / 2) * x + (c / 2) * x := add_le_add hsmooth htail
    _ = _ := by ring

theorem OMA.solution : type_of% @Erdos437.erdos_437.variants.little_o :=
  sparse_squares_little_o Erdos437.L endpoint_count_bound
