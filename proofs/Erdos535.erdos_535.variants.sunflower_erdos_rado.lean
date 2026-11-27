import FormalConjectures.ErdosProblems.«535»

/-!
The Erdős–Rado factorial bound for the multiplicity-sensitive gcd condition.
This proof gives the explicit constant c_r = 2 * r.
Reference: P. Erdős, Problems and Results on Combinatorial Number Theory (1973),
printed page 123, section 4, immediately before equation (4.3).
https://www.renyi.hu/~p_erdos/1973-21.pdf
-/

open ArithmeticFunction
open scoped ArithmeticFunction.Omega BigOperators

namespace OMA535

open Erdos535

/-- A bounded collection of primes meets every integer in a forbidden-pattern-free family. -/
theorem exists_prime_cover {r k : ℕ} {A : Finset ℕ}
    (hk : 0 < k) (hA : AllBigOmega k A)
    (hbad : NoConstantPairwiseGcdCoprimeSubsets r A) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ P.card ≤ k * (r - 1) ∧
      ∀ a ∈ A, ∃ p ∈ P, p ∣ a := by
  classical
  let family := A.powerset.filter fun C : Finset ℕ => (C : Set ℕ).Pairwise Nat.Coprime
  have hne : family.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [family]
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image family Finset.card hne
  have hCA : C ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1
  have hcop : (C : Set ℕ).Pairwise Nat.Coprime := (Finset.mem_filter.mp hC).2
  have hcard : C.card < r := by
    by_contra h
    obtain ⟨S, hSC, hSr⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
    apply hbad S (hSC.trans hCA) hSr
    refine ⟨1, by decide, ?_, ?_⟩
    · intro a ha b hb hab
      exact hcop (hSC ha) (hSC hb) hab
    · intro a ha
      exact ⟨a, by simp, by simp⟩
  have hshare : ∀ a ∈ A, ∃ b ∈ C, ¬ Nat.Coprime a b := by
    intro a ha
    by_contra h
    have hc : ∀ b ∈ C, Nat.Coprime a b := by
      intro b hb
      by_contra hnc
      exact h ⟨b, hb, hnc⟩
    have hins : insert a C ∈ family := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · exact Finset.insert_subset ha hCA
      · rw [Finset.coe_insert]
        exact hcop.insert fun b hb _ => ⟨hc b hb, (hc b hb).symm⟩
    have haC : a ∈ C := by
      by_contra hnC
      have hbound := hmax (insert a C) hins
      rw [Finset.card_insert_of_notMem hnC] at hbound
      omega
    have haone : a = 1 := by simpa using hc a haC
    have haOmega := (hA a ha).2
    simp [haone] at haOmega
    omega
  refine ⟨C.biUnion Nat.primeFactors, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, ha, hpa⟩ := Finset.mem_biUnion.mp hp
    exact Nat.prime_of_mem_primeFactors hpa
  · calc
      (C.biUnion Nat.primeFactors).card ≤ C.card * k := by
        apply Finset.card_biUnion_le_card_mul
        intro a ha
        calc
          a.primeFactors.card = a.primeFactorsList.dedup.length := by
            rw [← Nat.toFinset_factors, List.card_toFinset]
          _ ≤ a.primeFactorsList.length := a.primeFactorsList.dedup_sublist.length_le
          _ = k := (hA a (hCA ha)).2
      _ ≤ (r - 1) * k := Nat.mul_le_mul_right k (by omega)
      _ = k * (r - 1) := Nat.mul_comm _ _
  · intro a ha
    obtain ⟨b, hb, hnc⟩ := hshare a ha
    obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    refine ⟨p, Finset.mem_biUnion.mpr ⟨b, hb, ?_⟩, hpa⟩
    exact hp.mem_primeFactors hpb (by have := (hA b (hCA hb)).1; omega)

end OMA535

namespace OMA535

open Erdos535

lemma factorization_le_cardFactors (a p : ℕ) : a.factorization p ≤ Ω a := by
  simpa only [Nat.primeFactorsList_count_eq, cardFactors_apply] using
    (List.count_le_length (a := p) (l := a.primeFactorsList))

lemma prime_fiber_quotient {p e a k : ℕ} (hp : p.Prime)
    (ha : 1 ≤ a) (hΩ : Ω a = k) (he : a.factorization p = e) :
    e ≤ k ∧ 1 ≤ a / p ^ e ∧ p ^ e * (a / p ^ e) = a ∧
      Ω (a / p ^ e) = k - e ∧ Nat.Coprime (a / p ^ e) (p ^ e) := by
  have ha0 : a ≠ 0 := by omega
  have hp0 : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  have hdvd : p ^ e ∣ a := (hp.pow_dvd_iff_le_factorization ha0).2 (by omega)
  have hpos : 0 < a / p ^ e :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (Nat.pos_of_ne_zero hp0)
  have hmul : p ^ e * (a / p ^ e) = a := Nat.mul_div_cancel' hdvd
  have hcount : e + Ω (a / p ^ e) = k := by
    have := cardFactors_mul hp0 hpos.ne'
    rw [hmul, cardFactors_apply_prime_pow hp, hΩ] at this
    exact this.symm
  have hcop : Nat.Coprime p (a / p ^ e) := by
    simpa only [he] using Nat.coprime_ordCompl hp ha0
  exact ⟨by omega, by omega, hmul, by omega, hcop.symm.pow_right e⟩

lemma noConstant_of_scale {r q : ℕ} {A B : Finset ℕ}
    (hq : 0 < q) (hbad : NoConstantPairwiseGcdCoprimeSubsets r A)
    (hBA : ∀ b ∈ B, q * b ∈ A) (hcop : ∀ b ∈ B, Nat.Coprime b q) :
    NoConstantPairwiseGcdCoprimeSubsets r B := by
  classical
  intro S hSB hSc
  rintro ⟨d, hd, hpair, hquot⟩
  let T := S.image (fun b => q * b)
  have hinj : Function.Injective (fun b : ℕ => q * b) := by
    intro b c hbc
    exact Nat.eq_of_mul_eq_mul_left hq hbc
  have hTsub : T ⊆ A := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
    exact hBA b (hSB hb)
  have hTcard : T.card = r := by
    rw [Finset.card_image_of_injective S hinj, hSc]
  apply hbad T hTsub hTcard
  refine ⟨q * d, Nat.mul_pos hq hd, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hy
    have hbc : b ≠ c := fun h => hxy (congrArg (fun z => q * z) h)
    rw [Nat.gcd_mul_left, hpair hb hc hbc]
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨c, hbc, hcd⟩ := hquot b hb
    have hcb : c ∣ b := ⟨d, by simpa only [Nat.mul_comm] using hbc⟩
    have hcq : Nat.Coprime c q := (hcop b (hSB hb)).of_dvd_left hcb
    refine ⟨c, ?_, Nat.coprime_mul_iff_right.2 ⟨hcq, hcd⟩⟩
    rw [hbc, Nat.mul_assoc]

theorem fiber_reduction {r k p e : ℕ} {A : Finset ℕ} (hp : p.Prime)
    (hA : AllBigOmega k A) (hbad : NoConstantPairwiseGcdCoprimeSubsets r A) :
    let S := A.filter (fun a => a.factorization p = e)
    let B := S.image (fun a => a / p ^ e)
    B.card = S.card ∧ AllBigOmega (k - e) B ∧
      NoConstantPairwiseGcdCoprimeSubsets r B := by
  classical
  let S := A.filter (fun a => a.factorization p = e)
  let B := S.image (fun a => a / p ^ e)
  change B.card = S.card ∧ AllBigOmega (k - e) B ∧
    NoConstantPairwiseGcdCoprimeSubsets r B
  have hspec : ∀ a ∈ S,
      e ≤ k ∧ 1 ≤ a / p ^ e ∧ p ^ e * (a / p ^ e) = a ∧
        Ω (a / p ^ e) = k - e ∧ Nat.Coprime (a / p ^ e) (p ^ e) := by
    intro a ha
    obtain ⟨haA, he⟩ := Finset.mem_filter.1 ha
    exact prime_fiber_quotient hp (hA a haA).1 (hA a haA).2 he
  have hinj : Set.InjOn (fun a => a / p ^ e) (S : Set ℕ) := by
    intro a ha b hb hab
    calc
      a = p ^ e * (a / p ^ e) := (hspec a ha).2.2.1.symm
      _ = p ^ e * (b / p ^ e) := congrArg (fun z => p ^ e * z) hab
      _ = b := (hspec b hb).2.2.1
  refine ⟨Finset.card_image_of_injOn hinj, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨(hspec a ha).2.1, (hspec a ha).2.2.2.1⟩
  · apply noConstant_of_scale (q := p ^ e) (pow_pos hp.pos e) hbad
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
      rw [(hspec a ha).2.2.1]
      exact (Finset.mem_filter.1 ha).1
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
      exact (hspec a ha).2.2.2.2

end OMA535

namespace OMA535

open Erdos535

theorem card_le_prime_fibers {k : ℕ} {A P : Finset ℕ}
    (hA : AllBigOmega k A) (hP : ∀ p ∈ P, p.Prime)
    (hcover : ∀ a ∈ A, ∃ p ∈ P, p ∣ a) :
    A.card ≤ ∑ p ∈ P, ∑ j ∈ Finset.range k,
      (A.filter fun a => a.factorization p = j + 1).card := by
  classical
  have hsub : A ⊆ P.biUnion (fun p => (Finset.range k).biUnion
      fun j => A.filter fun a => a.factorization p = j + 1) := by
    intro a ha
    obtain ⟨p, hp, hpa⟩ := hcover a ha
    have hpos : 0 < a.factorization p :=
      (hP p hp).factorization_pos_of_dvd (by have := (hA a ha).1; omega) hpa
    have hle : a.factorization p ≤ k := by
      calc
        a.factorization p = a.primeFactorsList.count p := Nat.primeFactorsList_count_eq.symm
        _ ≤ a.primeFactorsList.length := List.count_le_length
        _ = Ω a := cardFactors_apply.symm
        _ = k := (hA a ha).2
    refine Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨a.factorization p - 1, ?_, ?_⟩
    · exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_filter.mpr ⟨ha, by omega⟩
  calc
    A.card ≤ (P.biUnion (fun p => (Finset.range k).biUnion
        fun j => A.filter fun a => a.factorization p = j + 1)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ p ∈ P, ((Finset.range k).biUnion
        fun j => A.filter fun a => a.factorization p = j + 1).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ p ∈ P, ∑ j ∈ Finset.range k,
        (A.filter fun a => a.factorization p = j + 1).card := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.card_biUnion_le

theorem card_le_one_of_omega_zero {A : Finset ℕ} (hA : AllBigOmega 0 A) :
    A.card ≤ 1 := by
  have hsub : A ⊆ ({1} : Finset ℕ) := by
    intro a ha
    have h := cardFactors_eq_zero_iff_eq_zero_or_one.mp (hA a ha).2
    have hpos := (hA a ha).1
    simp only [Finset.mem_singleton]
    omega
  simpa using Finset.card_le_card hsub

end OMA535

namespace OMA535

/-- The partial sum of factorial-weighted powers is at most twice its last term. -/
theorem sum_factorial_pow_bound (C n : ℕ) (hC : 2 ≤ C) :
    (∑ j ∈ Finset.range (n + 1), C ^ j * j.factorial) ≤
      2 * C ^ n * n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hterm : 2 * C ^ n * n.factorial ≤
          C ^ (n + 1) * (n + 1).factorial := by
        calc
          2 * C ^ n * n.factorial ≤ C * C ^ n * (n + 1).factorial :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ hC)
              (Nat.factorial_le (Nat.le_succ n))
          _ = C ^ (n + 1) * (n + 1).factorial := by
            rw [pow_succ]
            ac_rfl
      calc
        (∑ j ∈ Finset.range (n + 1 + 1), C ^ j * j.factorial) =
            (∑ j ∈ Finset.range (n + 1), C ^ j * j.factorial) +
              C ^ (n + 1) * (n + 1).factorial := Finset.sum_range_succ _ _
        _ ≤ C ^ (n + 1) * (n + 1).factorial +
            C ^ (n + 1) * (n + 1).factorial :=
          Nat.add_le_add_right (ih.trans hterm) _
        _ = 2 * C ^ (n + 1) * (n + 1).factorial := by ring

/-- The prime-cover recurrence is absorbed by the factorial bound with constant `2 * r`. -/
theorem prime_cover_recurrence_bound (r n : ℕ) (hr : 1 ≤ r) :
    (n + 1) * (r - 1) *
        (∑ j ∈ Finset.range (n + 1), (2 * r) ^ j * j.factorial) ≤
      (2 * r) ^ (n + 1) * (n + 1).factorial := by
  have hC : 2 ≤ 2 * r := by omega
  calc
    (n + 1) * (r - 1) *
        (∑ j ∈ Finset.range (n + 1), (2 * r) ^ j * j.factorial) ≤
        (n + 1) * (r - 1) * (2 * (2 * r) ^ n * n.factorial) :=
      Nat.mul_le_mul_left _ (sum_factorial_pow_bound (2 * r) n hC)
    _ ≤ (n + 1) * r * (2 * (2 * r) ^ n * n.factorial) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le r 1))
    _ = (2 * r) ^ (n + 1) * (n + 1).factorial := by
      rw [pow_succ, Nat.factorial_succ]
      ring

end OMA535

namespace OMA535

open Erdos535

theorem cardinal_bound {r : ℕ} (hr : 3 ≤ r) :
    ∀ k : ℕ, ∀ A : Finset ℕ, AllBigOmega k A →
      NoConstantPairwiseGcdCoprimeSubsets r A →
      A.card ≤ (2 * r) ^ k * k.factorial := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro A hA hbad
    cases k with
    | zero =>
      simpa using card_le_one_of_omega_zero hA
    | succ n =>
      classical
      obtain ⟨P, hP, hcard, hcover⟩ :=
        exists_prime_cover (by omega : 0 < n + 1) hA hbad
      have hfiber : ∀ p ∈ P, ∀ j ∈ Finset.range (n + 1),
          (A.filter fun a => a.factorization p = j + 1).card ≤
            (2 * r) ^ (n - j) * (n - j).factorial := by
        intro p hp j hj
        have hf := fiber_reduction (e := j + 1) (hP p hp) hA hbad
        dsimp only at hf
        obtain ⟨hBc, hBΩ, hBbad⟩ := hf
        rw [← hBc]
        have hsmall : n + 1 - (j + 1) < n + 1 := by omega
        simpa only [Nat.add_sub_add_right] using
          ih (n + 1 - (j + 1)) hsmall _ hBΩ hBbad
      have hreflect :
          (∑ j ∈ Finset.range (n + 1), (2 * r) ^ (n - j) * (n - j).factorial) =
          ∑ j ∈ Finset.range (n + 1), (2 * r) ^ j * j.factorial := by
        simpa only [Nat.add_sub_cancel] using
          Finset.sum_range_reflect (fun j => (2 * r) ^ j * j.factorial) (n + 1)
      calc
        A.card ≤ ∑ p ∈ P, ∑ j ∈ Finset.range (n + 1),
            (A.filter fun a => a.factorization p = j + 1).card :=
          card_le_prime_fibers hA hP hcover
        _ ≤ ∑ p ∈ P, ∑ j ∈ Finset.range (n + 1),
            (2 * r) ^ (n - j) * (n - j).factorial := by
          exact Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun j hj => hfiber p hp j hj
        _ = P.card * (∑ j ∈ Finset.range (n + 1), (2 * r) ^ j * j.factorial) := by
          simp only [hreflect, Finset.sum_const, smul_eq_mul]
        _ ≤ (n + 1) * (r - 1) *
            (∑ j ∈ Finset.range (n + 1), (2 * r) ^ j * j.factorial) :=
          Nat.mul_le_mul_right _ hcard
        _ ≤ (2 * r) ^ (n + 1) * (n + 1).factorial :=
          prime_cover_recurrence_bound r n (by omega)

end OMA535

theorem OMA.solution : type_of% @Erdos535.erdos_535.variants.sunflower_erdos_rado := by
  intro r hr
  refine ⟨((2 * r : ℕ) : ℝ), ?_, ?_⟩
  · exact_mod_cast (by omega : 0 < 2 * r)
  · intro k A hA hbad
    exact_mod_cast OMA535.cardinal_bound hr k A hA hbad
