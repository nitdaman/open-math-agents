import OMAReductions.R_OeisA224_conjecture_R1_H2_R1
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
For an odd integer with r distinct prime factors, r at least two, the
square-residue congruence forces a prime divisor strictly below 16 times 8^r.
This bound applies for all r and all positive exponents. The product estimate
controls the distance between n and 2^r a(n). A gap between consecutive
squares then excludes the only possible integer quotient.

Thomas Ordowski posed the original conjecture in OEIS A000224.
Credit: @HudZah, with Codex.
-/

open Finset OeisA224
namespace OMA.RoughSquares

theorem count_step (p e : ℕ) (hp : p.Prime) (hne : p ≠ 2) :
    a (p^(e+2)) = a (p^e) + (p^(e+1)*(p-1))/2 := by
  classical
  let residues (n : ℕ) : Finset ℕ :=
    (Finset.range n).image (fun k => k^2 % n)

  have mem_res {n r : ℕ} (hn : 0 < n) :
      r ∈ residues n ↔ ∃ k : ℕ, k^2 % n = r := by
    constructor
    · intro hr
      obtain ⟨k, _, h⟩ := Finset.mem_image.mp hr
      exact ⟨k, h⟩
    · rintro ⟨k, rfl⟩
      exact Finset.mem_image.mpr ⟨k % n, Finset.mem_range.mpr (Nat.mod_lt _ hn), (Nat.pow_mod ..).symm⟩

  let unitSq (n : ℕ) [NeZero n] : Finset ℕ := by
    classical
    exact Finset.univ.image (fun u : (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range =>
      (u.val.val).val)

  have mem_unitSq {n x : ℕ} [NeZero n] :
      x ∈ unitSq n ↔ ∃ u : (ZMod n)ˣ, ((u : ZMod n)^2).val = x := by
    classical
    constructor
    · intro hx
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv⟩ := u.property
      exact ⟨v, by simpa [← hv] using hu⟩
    · rintro ⟨u, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨u ^ 2, u, rfl⟩, Finset.mem_univ _, rfl⟩

  have unitSq_card (n : ℕ) [NeZero n] [IsCyclic (ZMod n)ˣ] (hn : 2 < n) :
      (unitSq n).card = n.totient / 2 := by
    classical
    unfold unitSq
    have hi : Function.Injective (fun u : (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range =>
        u.val.val.val) := fun _ _ h => Subtype.ext (Units.ext (ZMod.val_injective n h))
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ, ← Nat.card_eq_fintype_card,
      IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.gcd_eq_right (even_iff_two_dvd.mp (Nat.totient_even hn))]

  let N := p^(e+2)
  have hp0 := hp.pos
  have hn0 : 0 < N := pow_pos hp0 _
  have : NeZero N := ⟨hn0.ne'⟩
  have : IsCyclic (ZMod N)ˣ := ZMod.isCyclic_units_of_prime_pow p hp hne (e+2)
  have fact (u : ℕ) : (p*u)^2 % N = p^2 * (u^2 % p^e) := by
    rw [show N = p^2*p^e by dsimp [N]; ring, mul_pow, Nat.mul_mod_mul_left]
  let M := (residues (p^e)).image (fun t => p^2*t)
  have split : residues N = M ∪ unitSq N := by
    ext r
    constructor
    · intro hr
      obtain ⟨k, rfl⟩ := (mem_res hn0).mp hr
      by_cases hpk : p ∣ k
      · obtain ⟨u, rfl⟩ := hpk
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨u^2 % p^e, (mem_res (pow_pos hp0 _)).mpr ⟨u, rfl⟩, (fact u).symm⟩)
      · have hu : IsUnit (k : ZMod N) := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mpr hpk
        apply Finset.mem_union_right
        apply mem_unitSq.mpr
        exact ⟨hu.unit, by rw [IsUnit.unit_spec, ← Nat.cast_pow, ZMod.val_natCast]⟩
    · intro hr
      rcases Finset.mem_union.mp hr with hr | hr
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
        obtain ⟨u, rfl⟩ := (mem_res (pow_pos hp0 _)).mp ht
        exact (mem_res hn0).mpr ⟨p*u, fact u⟩
      · obtain ⟨u, rfl⟩ := mem_unitSq.mp hr
        exact (mem_res hn0).mpr ⟨u.val.val, by rw [← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]⟩
  have disj : Disjoint M (unitSq N) := by
    apply Finset.disjoint_left.mpr
    rintro r hr hunit
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨u, hu⟩ := mem_unitSq.mp hunit
    have hU : IsUnit (((p^2*t : ℕ) : ZMod N)) := by
      rw [← hu, ZMod.natCast_zmod_val]
      exact u.isUnit.pow 2
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (show 0 < e+2 by omega)).mp hU
      ((dvd_pow_self p (by decide : 2 ≠ 0)).trans (dvd_mul_right _ _))
  have high : 2 < N := lt_of_lt_of_le (lt_of_le_of_ne hp.two_le (Ne.symm hne))
    (Nat.le_pow (by omega : 0 < e+2))
  have hcnt : (unitSq N).card = _ := unitSq_card N high
  have hcard : (residues (p^e)).card = a (p^e) := by rw [a, if_neg (pow_ne_zero _ hp.ne_zero)]
  change a N = _
  rw [a, if_neg hn0.ne']
  change (residues N).card = _
  rw [split, Finset.card_union_of_disjoint disj, hcnt]
  dsimp only [M]
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left (pow_pos hp0 2) h), hcard]
  dsimp only [N]
  rw [Nat.totient_prime_pow_succ hp]

private theorem prime_count {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : a p = p / 2 + 1 := by
  rw [OMA.R_OeisA224_conjecture_R1.card_squares_prime p hp hodd]
  have := Nat.odd_iff.mp (hp.odd_of_ne_two hodd)
  omega

theorem count_formula (p : ℕ) (hp : p.Prime) (po : Odd p) (e : ℕ) :
    2*(p+1)*(a (p^e)-1) + (if Even e then p else 1) = p^(e+1) := by
  have hne : p ≠ 2 := by rintro rfl; norm_num at po
  induction e using Nat.twoStepInduction with
  | zero => simp [a_1]
  | one =>
    simp only [pow_one, prime_count hp hne, Nat.add_sub_cancel]
    obtain ⟨k, hk⟩ := po
    have hhalf : p/2 = k := by omega
    rw [hhalf, hk]
    simp
    ring
  | more e ih _ =>
    let x := p^(e+1)
    let q := x*(p-1)/2
    have hdouble : 2*q = x*(p-1) := by
      apply Nat.mul_div_cancel'
      apply dvd_mul_of_dvd_right
      have hh := Nat.odd_iff.mp po
      omega
    have ha : 1 ≤ a (p^e) := by
      rw [a, if_neg (pow_ne_zero _ hp.ne_zero), Finset.one_le_card]
      exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (pow_pos hp.pos e), by simp⟩⟩
    have hadd : a (p^(e+2)) - 1 = (a (p^e) - 1) + q := by
      rw [count_step p e hp hne]
      change a (p^e) + q - 1 = _
      omega
    have ev : Even (e+2) ↔ Even e := by simp only [Nat.even_iff]; omega
    rw [hadd, if_congr ev rfl rfl]
    calc
      _ = (2*(p+1)*(a (p^e)-1) + (if Even e then p else 1)) + (p+1)*(2*q) := by ring
      _ = x + (p+1)*(x*(p-1)) := by rw [ih, hdouble]
      _ = p^((e+2)+1) := by
        rw [show e+2+1 = (e+1)+2 by omega, pow_add]
        change x + (p+1)*(x*(p-1)) = x*p^2
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
        rw [hj]
        simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
        ring

theorem cleared (p e : ℕ) (hp : p.Prime) (hpo : Odd p) :
    2*(p+1)*a (p^e) = p*p^e + (if Even e then p+2 else 2*p+1) := by
  have h := count_formula p hp hpo e
  have ha : 1 ≤ a (p^e) := by
    rw [a, if_neg (pow_ne_zero _ hp.ne_zero), Finset.one_le_card]
    exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (pow_pos hp.pos e), by simp⟩⟩
  have restore := congrArg (fun x => 2*(p+1)*x) (Nat.sub_add_cancel ha)
  by_cases hEven : Even e <;> simp only [hEven, if_true, if_false, pow_succ] at * <;> nlinarith only [h, restore]

private theorem base_bounds {p e r : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : 0 < e) (hc : r ≤ p) :
    r*p^e ≤ 2*(r+1)*a (p^e) ∧ 2*r*a (p^e) ≤ (r+1)*p^e := by
  have eqn := cleared p e hp ho
  have ck : (if Even e then p+2 else 2*p+1) ≤ 2*p+1 := by
    split <;> have := hp.one_lt <;> omega
  have pn : p ≤ p^e := Nat.le_pow he
  constructor
  · apply Nat.le_of_mul_le_mul_left (c := p+1) _ (by omega)
    have hmul := Nat.mul_le_mul_right (p^e) hc
    nlinarith only [congrArg (fun x => (r+1)*x) eqn, hmul,
      Nat.zero_le ((r+1)*(if Even e then p+2 else 2*p+1))]
  · apply Nat.le_of_mul_le_mul_left (c := p+1) _ (by omega)
    have small := Nat.mul_le_mul_left r ck
    have h1 := Nat.mul_le_mul_left r pn
    have h2 := Nat.mul_le_mul_right (p+1) (hc.trans pn)
    nlinarith only [congrArg (fun x => r*x) eqn, small, h1, h2]

theorem impossible_square {n a t k : ℕ} (_hn : 0 < n) (ha : 0 < a)
    (hk : t^2=k) (kbig : 4<k) (ksmall : k<4*n+5)
    (eqn : n^2 = a*(a-1)*k+1) : False := by
  have ha' : a-1+1=a := Nat.sub_add_cancel ha
  have id : (t*(2*(a-1)+1))^2 + 4 = (2*n)^2+k := by
    rw [mul_pow, hk]
    nlinarith only [eqn,congrArg (fun x => x*(a-1)*k) ha']
  rcases le_or_gt (t*(2*(a-1)+1)) (2*n) with h|h
  · nlinarith only [id,kbig,Nat.pow_le_pow_left h 2]
  · have := Nat.pow_le_pow_left (show 2*n+1 ≤ t*(2*(a-1)+1) by omega) 2
    nlinarith only [id,ksmall,this]



private theorem factor_error {C p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hc : C ≤ p) (hC : 1 ≤ C) :
    (C : ℝ) * |2*(a (p^e) : ℝ) - (p^e : ℕ)| ≤ (p^e : ℕ) ∧ a (p^e) ≤ p^e := by
  have h := base_bounds hp ho he hc
  have lo : (C:ℝ)*(p^e:ℕ) ≤ 2*((C:ℝ)+1)*(a (p^e):ℝ) := by exact_mod_cast h.1
  have hi : 2*(C:ℝ)*(a (p^e):ℝ) ≤ ((C:ℝ)+1)*(p^e:ℕ) := by exact_mod_cast h.2
  constructor
  · by_cases hh : 2*(a (p^e):ℝ) ≤ (p^e:ℕ)
    · rw [abs_of_nonpos (by linarith)]
      nlinarith only [hh,lo]
    · rw [abs_of_nonneg (by linarith)]
      nlinarith only [hi]
  · by_contra! bad
    have hm := Nat.mul_le_mul_left (2*C) (show p^e+1 ≤ a (p^e) by omega)
    have hh := Nat.mul_le_mul_right (p^e) (show 1 ≤ C from hC)
    nlinarith only [h.2,hm,hh,hC]

private theorem product_error (s : Finset ℕ) (P A : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ p ∈ s, 0 ≤ A p ∧ 0 ≤ P p ∧ A p ≤ P p ∧ C*|2*A p-P p| ≤ P p) :
    C*|(2:ℝ)^s.card*(∏ p ∈ s,A p) - ∏ p ∈ s,P p| + ∏ p ∈ s,P p ≤
      (2:ℝ)^s.card * ∏ p ∈ s,P p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    obtain ⟨ap,pp,ab,fx⟩ := h x (by simp)
    have hs := ih (fun p hp => h p (Finset.mem_insert_of_mem hp))
    let t : ℝ := 2^s.card
    let u : ℝ := t * ∏ p ∈ s,A p
    let v : ℝ := ∏ p ∈ s,P p
    have vp : 0 ≤ v := Finset.prod_nonneg (fun p hp => (h p (Finset.mem_insert_of_mem hp)).2.1)
    change C*|u-v|+v ≤ t*v at hs
    have triangle : |2*A x*u-P x*v| ≤ 2*A x*|u-v|+v*|2*A x-P x| := by
      have eq : 2*A x*u-P x*v = (2*A x)*(u-v)+v*(2*A x-P x) := by ring
      rw [eq]
      simpa only [abs_mul,abs_of_nonneg (show 0 ≤ 2*A x by positivity),abs_of_nonneg vp]
        using abs_add_le ((2*A x)*(u-v)) (v*(2*A x-P x))
    have s1 := mul_le_mul_of_nonneg_left triangle hC
    have s2 := mul_le_mul_of_nonneg_left fx vp
    have s3 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*P x by positivity)
    have s4 := mul_le_mul_of_nonneg_right ab (mul_nonneg hC (abs_nonneg (u-v)))
    simp only [Finset.card_insert_of_notMem hx, Finset.prod_insert hx,pow_succ]
    change C*|(t*2)*(A x*(∏ p ∈ s,A p))-P x*v|+P x*v ≤ t*2*(P x*v)
    rw [show t*2*(A x*(∏ p ∈ s,A p))=2*A x*u by dsimp [u]; ring]
    nlinarith only [s1,s2,s3,s4]

private theorem quotient_gap {N A T K : ℝ} (hp : 2 ≤ T) (a0 : 0 < A)
    (err : 16*T^3*|N-T*A| ≤ T*N) (size : 16*T^3 ≤ N)
    (eqn : N^2 = K*A*(A-1)+1) :
    T^2-1 < K ∧ K < T^2+1 := by
  have t0 : 0 < T := by linarith
  have t2 : 4 ≤ T^2 := by nlinarith [sq_nonneg (T-2)]
  have err' : 16*T^2*|N-T*A| ≤ N := by
    apply le_of_mul_le_mul_left (a := T) _ t0
    nlinarith only [err]
  have one : |N-T*A| ≤ N/2 := by
    nlinarith only [err',mul_nonneg (show 0 ≤ 16*T^2-2 by linarith) (abs_nonneg (N-T*A))]
  have close : N ≤ 2*T*A := by linarith [le_abs_self (N-T*A)]
  have dsmall : 8*T*|N-T*A| ≤ A := by
    apply le_of_mul_le_mul_left (a := 2*T) _ (by positivity)
    nlinarith only [err',close]
  have abig : 8*T^2 ≤ A := by
    apply le_of_mul_le_mul_left (a := 2*T) _ (by positivity)
    nlinarith only [size,close]
  have a2 : 2 ≤ A := by linarith
  have pos : 0 ≤ N+T*A := by nlinarith only [size, mul_pos t0 (mul_self_pos.mpr t0.ne'),mul_pos t0 a0]
  have ident : |N^2-(T*A)^2| = |N-T*A| * (N+T*A) := by
    rw [show N^2-(T*A)^2=(N-T*A)*(N+T*A) by ring, abs_mul, abs_of_nonneg pos]
  have diff : 8*|N^2-(T*A)^2| ≤ 3*A^2 := by
    rw [ident]
    have h1 := mul_le_mul_of_nonneg_left close (abs_nonneg (N-T*A))
    have h2 := mul_le_mul_of_nonneg_right dsmall a0.le
    nlinarith only [h1,h2]
  have weight : 0 ≤ A*(A-1) := mul_nonneg a0.le (by linarith)
  constructor
  · by_contra! bad
    have b := mul_le_mul_of_nonneg_right bad weight
    have ab := neg_le_abs (N^2-(T*A)^2)
    nlinarith only [b,ab,diff,eqn,mul_self_nonneg (A-2),a2]
  · by_contra! bad
    have b := mul_le_mul_of_nonneg_right bad weight
    have ab := le_abs_self (N^2-(T*A)^2)
    have big := mul_le_mul_of_nonneg_right abig a0.le
    nlinarith only [b,ab,diff,eqn,big,mul_self_nonneg (A-2),a2]

private theorem prod_counts (n : ℕ) (hz : n ≠ 0) :
    a n = ∏ p ∈ n.primeFactors, a (p^(n.factorization p)) := by
  apply Nat.multiplicative_factorization a _ OeisA224.a_1 hz
  intro x y hc
  by_cases hx : x = 0
  · subst x
    have hy : y = 1 := by simpa using hc
    simp [hy,OeisA224.a_1]
  by_cases hy : y = 0
  · subst y
    have hx1 : x = 1 := by simpa using hc
    simp [hx1,OeisA224.a_1]
  exact OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy) hc

theorem rough_fails (n : ℕ) (ho : Odd n) (hr : 2 ≤ n.primeFactors.card)
    (hrough : ∀ p ∈ n.primeFactors, 16*(2^n.primeFactors.card)^3 ≤ p) :
    ¬ n^2 ≡ 1 [MOD a n*(a n-1)] := by
  intro test
  have nz : n ≠ 0 := by rintro rfl; simp at hr
  let t : ℕ := 2^n.primeFactors.card
  let C : ℕ := 16*t^3
  have ht : 4 ≤ t := by exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hr
  have hc : 1 ≤ C := by change 0 < 16*t^3; positivity
  have sm : C ≤ n := by
    have ne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p,hp⟩ := ne
    exact (hrough p hp).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero nz) (Nat.dvd_of_mem_primeFactors hp))
  have atom (p : ℕ) (hp : p ∈ n.primeFactors) :
      0 ≤ (a (p^(n.factorization p)) : ℝ) ∧ 0 ≤ ((p^(n.factorization p) : ℕ):ℝ) ∧
      (a (p^(n.factorization p)) : ℝ) ≤ ((p^(n.factorization p) : ℕ):ℝ) ∧
      (C:ℝ)*|2*(a (p^(n.factorization p)):ℝ)-((p^(n.factorization p):ℕ):ℝ)| ≤ ((p^(n.factorization p):ℕ):ℝ) := by
    have prime := Nat.prime_of_mem_primeFactors hp
    have pd := Nat.dvd_of_mem_primeFactors hp
    have po : Odd p := by
      by_contra bad
      exact ho.not_two_dvd_nat ((even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp bad)).trans pd)
    have z := factor_error prime po (prime.factorization_pos_of_dvd nz pd) (hrough p hp) hc
    exact ⟨by positivity,by positivity, by exact_mod_cast z.2, z.1⟩
  have bound := product_error n.primeFactors _ _ (C:ℝ) (by positivity) atom
  have hN : (∏ p ∈ n.primeFactors, ((p^(n.factorization p):ℕ):ℝ)) = n := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization nz).symm
  have hA : (∏ p ∈ n.primeFactors, (a (p^(n.factorization p)):ℝ)) = a n := by
    exact_mod_cast (prod_counts n nz).symm
  simp only [hN,hA] at bound
  have tp : (2:ℝ)^n.primeFactors.card = t := by simp [t]
  rw [tp, abs_sub_comm] at bound
  have ns : 1 < n^2 := by
    have : 1 < n := by dsimp [C] at sm; nlinarith only [ht,sm,Nat.one_le_pow 3 t (by omega)]
    exact Nat.one_lt_pow (by decide) this
  obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' ns.le).mp test.symm
  change n^2-1 = a n*(a n-1)*k at hk
  have eqn : n^2 = a n*(a n-1)*k+1 := by omega
  have a0 : 0 < a n := by
    by_contra! bad
    rw [show a n=0 by omega] at eqn
    simp at eqn
    omega
  have eqR : (n:ℝ)^2 = (k:ℝ)*(a n:ℝ)*((a n:ℝ)-1)+1 := by
    have lift := congrArg (fun x:ℕ => (x:ℝ)) eqn
    push_cast [Nat.cast_sub (by omega : 1 ≤ a n)] at lift
    nlinarith only [lift]
  have size : 16*(t:ℝ)^3 ≤ n := by exact_mod_cast sm
  have error : 16*(t:ℝ)^3*|(n:ℝ)-(t:ℝ)*(a n:ℝ)| ≤ (t:ℝ)*n := by
    have cdef : (C:ℝ)=16*(t:ℝ)^3 := by simp [C]
    rw [cdef] at bound
    linarith [show (0:ℝ) ≤ n by positivity]
  have near := quotient_gap (show 2 ≤ (t:ℝ) by exact_mod_cast (show 2 ≤ t by omega))
    (show 0 < (a n:ℝ) by exact_mod_cast a0) error size eqR
  have h1 : t^2 < k+1 := by exact_mod_cast (show (t:ℝ)^2 < (k:ℝ)+1 by linarith [near.1])
  have h2 : k < t^2+1 := by exact_mod_cast near.2
  have sq : t^2=k := by omega
  have big : 4 < k := by nlinarith only [sq,Nat.pow_le_pow_left ht 2]
  have small : k < 4*n+5 := by
    change 16*t^3 ≤ n at sm
    have mm := Nat.mul_le_mul_right (t^2) (show 1 ≤ t by omega)
    nlinarith only [sq,sm,mm]
  exact impossible_square (Nat.pos_of_ne_zero nz) a0 sq big small eqn

end OMA.RoughSquares

namespace OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1

-- The two finite prime-factor counts addressed by the accompanying arithmetic approach.
def H1 : Prop :=
  ∀ n : ℕ, Odd n → 3 ≤ n.primeFactors.card → n.primeFactors.card ≤ 4 →
    (∃ p ∈ n.primeFactors, p < 16*(2^n.primeFactors.card)^3) →
    ¬ n^2 ≡ 1 [MOD a n*(a n-1)]

-- Five or more distinct prime factors, including a divisor below the uniform bound.
def H2 : Prop :=
  ∀ n : ℕ, Odd n → 5 ≤ n.primeFactors.card →
    (∃ p ∈ n.primeFactors, p < 16*(2^n.primeFactors.card)^3) →
    ¬ n^2 ≡ 1 [MOD a n*(a n-1)]

theorem main : H1 → H2 → OMA.R_OeisA224_conjecture_R1_H2_R1.H2 := by
  intro small many n ho hr
  by_cases h : ∃ p ∈ n.primeFactors, p < 16*(2^n.primeFactors.card)^3
  · by_cases low : n.primeFactors.card ≤ 4
    · exact small n ho hr low h
    · exact many n ho (by omega) h
  · apply OMA.RoughSquares.rough_fails n ho (by omega)
    intro p hp
    by_contra! bad
    exact h ⟨p,hp,bad⟩

end OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1
