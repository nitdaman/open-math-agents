import FormalConjectures.ErdosProblems.«939»

/-! Start with Nitaj's example from the problem brief and iterate the tangent
construction on a sum of two signed cubes. Its absolute value grows at each
step by a cube factor, and the two coordinates stay coprime. -/

namespace OMA.Cubes

def U (x y : ℤ) := x * (x^3 + 2*y^3)
def V (x y : ℤ) := -y * (2*x^3 + y^3)

lemma tangent (x y : ℤ) :
    U x y ^ 3 + V x y ^ 3 = (x^3-y^3)^3 * (x^3+y^3) := by
  unfold U V
  ring

lemma shift {a b : ℤ} (h : IsCoprime a b) (t : ℤ) : IsCoprime (a+t*b) b := by
  obtain ⟨u,v,H⟩ := h
  exact ⟨u,v-u*t,by linear_combination H⟩

lemma coprime_next {x y : ℤ} (h : IsCoprime x y)
    (hx : x ≡ 5 [ZMOD 6]) (hy : y ≡ 1 [ZMOD 6]) : IsCoprime (U x y) (V x y) := by
  let A := x^3 + 2*y^3
  let B := 2*x^3 + y^3
  have hAy : IsCoprime A y := by
    convert shift (h.pow_left (m := 3)) (2*y^2) using 1 <;> dsimp [A] <;> ring
  have hxB : IsCoprime x B := by
    apply IsCoprime.symm
    convert shift (h.symm.pow_left (m := 3)) (2*x^2) using 1 <;> dsimp [B] <;> ring
  have hAmod : A ≡ 1 [ZMOD 6] :=
    ((hx.pow 3).add ((Int.ModEq.refl 2).mul (hy.pow 3))).trans (by decide)
  have hA3 : IsCoprime A 3 := by
    change A % 6 = 1 at hAmod
    exact ⟨1,-(2*(A/6)),by omega⟩
  have hABy : IsCoprime A (3*y^3) := hA3.mul_right (hAy.pow_right (n := 3))
  have hAB : IsCoprime A B := by
    apply IsCoprime.symm
    have hn := hABy.symm.neg_left
    convert shift hn 2 using 1 <;> dsimp [A,B] <;> ring
  change IsCoprime (x*A) (-y*B)
  rw [neg_mul]
  exact ((h.mul_right hxB).mul_left (hAy.mul_right hAB)).neg_right

lemma cube_full (z : ℕ) : (3 : ℕ).Full (z^3) := by
  intro p hp
  have h := Nat.mem_primeFactors.mp hp
  exact pow_dvd_pow_of_dvd (h.1.dvd_of_dvd_pow h.2.1) 3

lemma full_mul {a b : ℕ} (ha : (3 : ℕ).Full a) (hb : (3 : ℕ).Full b) : (3 : ℕ).Full (a*b) := by
  intro p hp
  have ⟨hprime,hd,hn⟩ := Nat.mem_primeFactors.mp hp
  rcases hprime.dvd_mul.mp hd with h | h
  · exact dvd_mul_of_dvd_left (ha _ (Nat.mem_primeFactors.mpr ⟨hprime,h,left_ne_zero_of_mul hn⟩)) _
  · exact dvd_mul_of_dvd_right (hb _ (Nat.mem_primeFactors.mpr ⟨hprime,h,right_ne_zero_of_mul hn⟩)) _

def Good (x y : ℤ) := IsCoprime x y ∧ x ≡ 5 [ZMOD 6] ∧ y ≡ 1 [ZMOD 6] ∧
  (3 : ℕ).Full (x^3+y^3).natAbs

lemma grow (N : ℕ) : ∃ x y : ℤ, Good x y ∧ N < (x^3+y^3).natAbs := by
  induction N with
  | zero =>
    refine ⟨-271,919,⟨Int.isCoprime_iff_nat_coprime.mpr (by decide),by decide,by decide,?_⟩,by decide⟩
    change (3 : ℕ).Full (2^3 * 3^5 * 73^3)
    apply full_mul (full_mul (cube_full 2) ?_) (cube_full 73)
    intro p hp
    have he := (Nat.mem_primeFactors.mp hp).1.dvd_of_dvd_pow (Nat.mem_primeFactors.mp hp).2.1
    have hp3 : p = 3 := ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp he).resolve_left (Nat.mem_primeFactors.mp hp).1.ne_one
    subst p
    decide
  | succ N ih =>
    obtain ⟨x,y,⟨hxy,hx,hy,hf⟩,hN⟩ := ih
    have hU : U x y ≡ 5 [ZMOD 6] :=
      (hx.mul ((hx.pow 3).add ((Int.ModEq.refl 2).mul (hy.pow 3)))).trans (by decide)
    have hV : V x y ≡ 1 [ZMOD 6] :=
      (hy.neg.mul (((Int.ModEq.refl 2).mul (hx.pow 3)).add (hy.pow 3))).trans (by decide)
    have hdel : x^3-y^3 ≡ 4 [ZMOD 6] := ((hx.pow 3).sub (hy.pow 3)).trans (by decide)
    have hsize : 2 ≤ (x^3-y^3).natAbs := by
      change (x^3-y^3) % 6 = 4 at hdel
      have := Int.natCast_natAbs (x^3-y^3)
      rcases abs_cases (x^3-y^3) with h | h <;> omega
    refine ⟨U x y,V x y,⟨coprime_next hxy hx hy,hU,hV,?_⟩,?_⟩
    · rw [tangent, Int.natAbs_mul, Int.natAbs_pow]
      exact full_mul (cube_full _) hf
    · rw [tangent, Int.natAbs_mul, Int.natAbs_pow]
      have hh := Nat.pow_le_pow_left hsize 3
      nlinarith


lemma abs_sums (u v : ℤ) :
    u.natAbs + v.natAbs = (u+v).natAbs ∨ u.natAbs + (u+v).natAbs = v.natAbs ∨
    v.natAbs + (u+v).natAbs = u.natAbs := by
  have := Int.natCast_natAbs u
  have := Int.natCast_natAbs v
  have := Int.natCast_natAbs (u+v)
  rcases abs_cases u with hu | hu <;> rcases abs_cases v with hv | hv <;>
    rcases abs_cases (u+v) with huv | huv <;> omega

lemma gcd_one {S : Finset ℕ} {a b : ℕ} (h : a.Coprime b) (ha : a ∈ S) (hb : b ∈ S) :
    S.Coprime := by
  apply Nat.dvd_one.mp
  rw [← h.gcd_eq_one]
  exact Nat.dvd_gcd (Finset.gcd_dvd ha) (Finset.gcd_dvd hb)

def triples : Set (ℕ × ℕ × ℕ) := {(a,b,c) | ({a,b,c} : Finset ℕ).Coprime ∧
  0 < a ∧ 0 < b ∧ (3 : ℕ).Full a ∧ (3 : ℕ).Full b ∧ (3 : ℕ).Full c ∧ a+b=c}

lemma large (N : ℕ) : ∃ t ∈ triples, N < t.2.2 := by
  obtain ⟨x,y,⟨hc,hx,hy,hf⟩,hN⟩ := grow N
  have hxn : x ≠ 0 := by intro h; subst x; contradiction
  have hyn : y ≠ 0 := by intro h; subst y; contradiction
  let A := x.natAbs^3
  let B := y.natAbs^3
  let C := (x^3+y^3).natAbs
  have ha : 0 < A := pow_pos (Int.natAbs_pos.mpr hxn) _
  have hb : 0 < B := pow_pos (Int.natAbs_pos.mpr hyn) _
  have hC : N < C := hN
  have hcAB : A.Coprime B := (Int.isCoprime_iff_nat_coprime.mp hc).pow _ _
  have hfa : (3 : ℕ).Full A := cube_full _
  have hfb : (3 : ℕ).Full B := cube_full _
  have h : A+B=C ∨ A+C=B ∨ B+C=A := by
    dsimp only [A,B,C]
    rw [← Int.natAbs_pow x 3, ← Int.natAbs_pow y 3]
    exact abs_sums (x^3) (y^3)
  rcases h with h | h | h
  · exact ⟨(A,B,C),⟨gcd_one hcAB (by simp) (by simp),ha,hb,hfa,hfb,hf,h⟩,hC⟩
  · exact ⟨(A,C,B),⟨gcd_one hcAB (by simp) (by simp),ha,by omega,hfa,hf,hfb,h⟩,by dsimp; omega⟩
  · exact ⟨(B,C,A),⟨gcd_one hcAB (by simp) (by simp),hb,by omega,hfb,hf,hfa,h⟩,by dsimp; omega⟩

end OMA.Cubes

theorem OMA.solution : type_of% @Erdos939.erdos_939.variants.triples := by
  change OMA.Cubes.triples.Infinite
  intro hfin
  obtain ⟨M,hM⟩ := (hfin.image (fun t : ℕ × ℕ × ℕ => t.2.2)).bddAbove
  obtain ⟨t,ht,hlarge⟩ := OMA.Cubes.large M
  exact (not_lt_of_ge (hM (Set.mem_image_of_mem _ ht))) hlarge
