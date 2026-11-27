import OMAReductions.R_Arxiv_0805_3777_isGenericRank_cube_R1

/-! Split a cubic tensor into a quasicubic coordinate block and its complement.
The inner configurations meet any prescribed nonempty principal open. The
complementary construction works on one such open. Once the quotient is covered,
zero-padded inner tangent vectors correct the residual without changing the exterior.

The formats and summand counts follow Strassen's quasicubic result and Lickteig's
complementary tangent estimates. [Lickteig (1985), Proposition 4.2, Lemmas 4.6–4.7
and Theorem 4.4](https://doi.org/10.1016/0024-3795(85)90070-9). -/

namespace OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1

section ExceptionalCases

/-- The small cubes and the isolated seven-dimensional case in the block argument. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≠ 3 → (n ≤ 4 ∨ n = 7) →
    let r := n ^ 3 ⌈/⌉ (3 * n - 2)
    ∃ a b c : Fin r → Fin n → ℂ, ∀ T : Fin n → Fin n → Fin n → ℂ,
      ∃ u v w : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i * (b t j * c t k) +
          a t i * (v t j * c t k) + a t i * (b t j * w t k))

end ExceptionalCases

section InnerBlock

/-- Spanning configurations for the quasicubic block are Zariski dense in the
space of its factor vectors. -/
def H2 : Prop :=
  ∀ n : ℕ, 5 ≤ n → n ≠ 7 →
    let d := if n % 3 = 1 then n - 1 else n - 2
    let e := if n % 3 = 1 then n - 2 else n
    let s := d * (if n % 3 = 1 then d else n) / 3
    ∀ P : MvPolynomial (Fin s × (Fin d ⊕ (Fin d ⊕ Fin e))) ℂ, P ≠ 0 →
      ∃ x : Fin s × (Fin d ⊕ (Fin d ⊕ Fin e)) → ℂ, MvPolynomial.eval x P ≠ 0 ∧
        ∀ T : Fin d → Fin d → Fin e → ℂ,
          ∃ u v : Fin s → Fin d → ℂ, ∃ w : Fin s → Fin e → ℂ, ∀ i j k,
            T i j k = ∑ t, (u t i * (x (t, Sum.inr (Sum.inl j)) * x (t, Sum.inr (Sum.inr k))) +
              x (t, Sum.inl i) * (v t j * x (t, Sum.inr (Sum.inr k))) +
              x (t, Sum.inl i) * (x (t, Sum.inr (Sum.inl j)) * w t k))

end InnerBlock

section Complement

/-- On a principal open set of inner configurations, add the remaining points
so the tangent sum covers all coordinates outside the block. -/
def H3 : Prop :=
  ∀ n : ℕ, 5 ≤ n → n ≠ 7 →
    let d := if n % 3 = 1 then n - 1 else n - 2
    let e := if n % 3 = 1 then n - 2 else n
    let s := d * (if n % 3 = 1 then d else n) / 3
    let r := n ^ 3 ⌈/⌉ (3 * n - 2)
    ∃ P : MvPolynomial (Fin s × (Fin d ⊕ (Fin d ⊕ Fin e))) ℂ, P ≠ 0 ∧
      ∀ x : Fin s × (Fin d ⊕ (Fin d ⊕ Fin e)) → ℂ, MvPolynomial.eval x P ≠ 0 →
        ∃ a b c : Fin r → Fin n → ℂ,
          (∀ (t : Fin r) (ht : t.val < s) (i : Fin n),
            a t i = (if h : i.val < d then x (⟨t.val,ht⟩, Sum.inl ⟨i.val,h⟩) else 0) ∧
            b t i = (if h : i.val < d then x (⟨t.val,ht⟩, Sum.inr (Sum.inl ⟨i.val,h⟩)) else 0) ∧
            c t i = (if h : i.val < e then x (⟨t.val,ht⟩, Sum.inr (Sum.inr ⟨i.val,h⟩)) else 0)) ∧
          ∀ T : Fin n → Fin n → Fin n → ℂ, ∃ u v w : Fin r → Fin n → ℂ, ∀ i j k,
            (d ≤ i.val ∨ d ≤ j.val ∨ e ≤ k.val) →
              T i j k = ∑ t, (u t i * (b t j * c t k) +
                a t i * (v t j * c t k) + a t i * (b t j * w t k))

end Complement

lemma sum_padded {s r : ℕ} (hs : s ≤ r) (f : Fin s → ℂ) :
    (∑ t : Fin r, if h : t.val < s then f ⟨t.val, h⟩ else 0) = ∑ t, f t := by
  induction r, hs using Nat.le_induction with
  | base =>
    apply Finset.sum_congr rfl
    intro i _
    simp [i.isLt]
  | succ r hr ih =>
    rw [Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc, Fin.val_last, dif_neg (Nat.not_lt.mpr hr), add_zero] using ih

lemma glue_block {n r d e s : ℕ} (hd : d ≤ n) (he : e ≤ n) (hs : s ≤ r)
    (x : Fin s × (Fin d ⊕ (Fin d ⊕ Fin e)) → ℂ)
    (a b c : Fin r → Fin n → ℂ)
    (fixed : ∀ (t : Fin r) (ht : t.val < s) (i : Fin n),
      a t i = (if h : i.val < d then x (⟨t.val,ht⟩, Sum.inl ⟨i.val,h⟩) else 0) ∧
      b t i = (if h : i.val < d then x (⟨t.val,ht⟩, Sum.inr (Sum.inl ⟨i.val,h⟩)) else 0) ∧
      c t i = (if h : i.val < e then x (⟨t.val,ht⟩, Sum.inr (Sum.inr ⟨i.val,h⟩)) else 0))
    (inner : ∀ T : Fin d → Fin d → Fin e → ℂ,
      ∃ u v : Fin s → Fin d → ℂ, ∃ w : Fin s → Fin e → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i * (x (t, Sum.inr (Sum.inl j)) * x (t, Sum.inr (Sum.inr k))) +
          x (t, Sum.inl i) * (v t j * x (t, Sum.inr (Sum.inr k))) +
          x (t, Sum.inl i) * (x (t, Sum.inr (Sum.inl j)) * w t k)))
    (outside : ∀ T : Fin n → Fin n → Fin n → ℂ, ∃ u v w : Fin r → Fin n → ℂ,
      ∀ i j k, (d ≤ i.val ∨ d ≤ j.val ∨ e ≤ k.val) →
        T i j k = ∑ t, (u t i * (b t j * c t k) +
          a t i * (v t j * c t k) + a t i * (b t j * w t k))) :
    ∀ T : Fin n → Fin n → Fin n → ℂ, ∃ u v w : Fin r → Fin n → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i * (b t j * c t k) +
        a t i * (v t j * c t k) + a t i * (b t j * w t k)) := by
  classical
  intro T
  obtain ⟨u₀,v₀,w₀,hout⟩ := outside T
  let base (i j k : Fin n) := ∑ t, (u₀ t i * (b t j * c t k) +
    a t i * (v₀ t j * c t k) + a t i * (b t j * w₀ t k))
  let residual (i j k : Fin n) := T i j k - base i j k
  have hzero (i j k : Fin n) (h : d ≤ i.val ∨ d ≤ j.val ∨ e ≤ k.val) :
      residual i j k = 0 := sub_eq_zero.mpr (hout i j k h)
  obtain ⟨u,v,w,hcore⟩ := inner (fun i j k => residual (i.castLE hd) (j.castLE hd) (k.castLE he))
  let extByZero (m : ℕ) (g : Fin m → ℂ) (i : Fin n) :=
    if h : i.val < m then g ⟨i.val, h⟩ else 0
  let liftRows (m : ℕ) (g : Fin s → Fin m → ℂ) (t : Fin r) (i : Fin n) :=
    if h : t.val < s then extByZero m (g ⟨t.val, h⟩) i else 0
  let A (t : Fin s) := extByZero d (fun i => x (t, Sum.inl i))
  let B (t : Fin s) := extByZero d (fun j => x (t, Sum.inr (Sum.inl j)))
  let C (t : Fin s) := extByZero e (fun k => x (t, Sum.inr (Sum.inr k)))
  let term (t : Fin s) (i j k : Fin n) :=
    extByZero d (u t) i * (B t j * C t k) + A t i * (extByZero d (v t) j * C t k) +
      A t i * (B t j * extByZero e (w t) k)
  have hsum (i j k : Fin n) :
      (∑ t : Fin r, (liftRows d u t i * (b t j * c t k) +
        a t i * (liftRows d v t j * c t k) + a t i * (b t j * liftRows e w t k))) =
        ∑ t : Fin s, term t i j k := by
    rw [← sum_padded hs (fun t => term t i j k)]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : t.val < s
    · rw [(fixed t ht i).1, (fixed t ht j).2.1, (fixed t ht k).2.2]
      simp only [liftRows, dif_pos ht, term, A, B, C, extByZero]
    · simp [liftRows, ht]
  have hres (i j k : Fin n) : residual i j k = ∑ t : Fin s, term t i j k := by
    by_cases hi : i.val < d
    · by_cases hj : j.val < d
      · by_cases hk : k.val < e
        · have hi' : (⟨i.val,hi⟩ : Fin d).castLE hd = i := Fin.ext rfl
          have hj' : (⟨j.val,hj⟩ : Fin d).castLE hd = j := Fin.ext rfl
          have hk' : (⟨k.val,hk⟩ : Fin e).castLE he = k := Fin.ext rfl
          simpa only [hi', hj', hk', term, A, B, C, extByZero, dif_pos hi, dif_pos hj, dif_pos hk] using
            hcore ⟨i.val,hi⟩ ⟨j.val,hj⟩ ⟨k.val,hk⟩
        · rw [hzero i j k (Or.inr (Or.inr (Nat.le_of_not_gt hk)))]
          simp [term, C, extByZero, hk]
      · rw [hzero i j k (Or.inr (Or.inl (Nat.le_of_not_gt hj)))]
        simp [term, B, extByZero, hj]
    · rw [hzero i j k (Or.inl (Nat.le_of_not_gt hi))]
      simp [term, A, extByZero, hi]
  refine ⟨fun t i => u₀ t i + liftRows d u t i, fun t j => v₀ t j + liftRows d v t j,
    fun t k => w₀ t k + liftRows e w t k, ?_⟩
  intro i j k
  calc
    T i j k = base i j k + residual i j k := by dsimp [residual]; ring
    _ = _ := by
      rw [hres, ← hsum]
      dsimp only [base]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      ring

lemma inner_count_le (n d m : ℕ) (hn : 1 ≤ n) (hd : d ≤ n) (hm : m ≤ n) :
    d * m / 3 ≤ n ^ 3 ⌈/⌉ (3 * n - 2) := by
  let s := d * m / 3
  have h3 : 3 * s ≤ n * n :=
    (by simpa only [Nat.mul_comm 3] using Nat.div_mul_le_self (d * m) 3 : 3 * s ≤ d * m).trans
      (Nat.mul_le_mul hd hm)
  have hden : 0 < 3 * n - 2 := by omega
  have hbound : (3 * n - 2) * s ≤ n ^ 3 := calc
    _ ≤ (3 * n) * s := Nat.mul_le_mul_right s (Nat.sub_le _ _)
    _ = n * (3 * s) := by ring
    _ ≤ n * (n * n) := Nat.mul_le_mul_left n h3
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left (hbound.trans ((ceilDiv_le_iff_le_mul hden).mp le_rfl)) hden

lemma coordinates_to_holors {n r : ℕ}
    (h : ∃ a b c : Fin r → Fin n → ℂ, ∀ T : Fin n → Fin n → Fin n → ℂ,
      ∃ u v w : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i * (b t j * c t k) +
          a t i * (v t j * c t k) + a t i * (b t j * w t k))) :
    ∃ a b c : Fin r → Holor ℂ [n], ∀ T : Holor ℂ [n,n,n],
      ∃ u v w : Fin r → Holor ℂ [n], T = ∑ t,
        (Holor.mul (u t) (Holor.mul (b t) (c t)) +
         Holor.mul (a t) (Holor.mul (v t) (c t)) +
         Holor.mul (a t) (Holor.mul (b t) (w t))) := by
  let idx : HolorIndex [n] → Fin n
    | ⟨i :: _, h⟩ => ⟨i, (List.forall₂_cons.mp h).1⟩
    | ⟨[], h⟩ => nomatch h
  let cube (i j k : Fin n) : HolorIndex [n,n,n] :=
    ⟨[i.val,j.val,k.val], .cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩
  have coordinates (q : HolorIndex [n,n,n]) : ∃ i j k, cube i j k = q := by
    rcases q with ⟨l, hl⟩
    cases hl with
    | cons hi rest =>
      cases rest with
      | cons hj rest =>
        cases rest with
        | cons hk rest =>
          cases rest
          exact ⟨⟨_, hi⟩, ⟨_, hj⟩, ⟨_, hk⟩, rfl⟩
  obtain ⟨a, b, c, hspan⟩ := h
  let pack (v : Fin r → Fin n → ℂ) (t : Fin r) (i : HolorIndex [n]) := v t (idx i)
  refine ⟨pack a, pack b, pack c, ?_⟩
  intro T
  obtain ⟨u, v, w, huv⟩ := hspan (fun i j k => T (cube i j k))
  refine ⟨pack u, pack v, pack w, ?_⟩
  funext q
  obtain ⟨i,j,k,rfl⟩ := coordinates q
  refine (huv i j k).trans ?_
  symm
  let summand (t : Fin r) := Holor.mul (pack u t) (Holor.mul (pack b t) (pack c t)) +
    Holor.mul (pack a t) (Holor.mul (pack v t) (pack c t)) +
    Holor.mul (pack a t) (Holor.mul (pack b t) (pack w t))
  exact Finset.sum_apply (M := fun _ : HolorIndex [n,n,n] => ℂ) (cube i j k) Finset.univ
    (fun t z => summand t z)

theorem main : H1 → H2 → H3 → OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1.H3 := by
  classical
  intro hsmall hinner hout n hn hn3
  apply coordinates_to_holors
  by_cases hx : n ≤ 4 ∨ n = 7
  · exact hsmall n hn hn3 hx
  obtain ⟨hn5, hn7⟩ : 5 ≤ n ∧ n ≠ 7 := by omega
  let d := if n % 3 = 1 then n - 1 else n - 2
  let e := if n % 3 = 1 then n - 2 else n
  let s := d * (if n % 3 = 1 then d else n) / 3
  let r := n ^ 3 ⌈/⌉ (3 * n - 2)
  have hd : d ≤ n := by dsimp [d]; split <;> omega
  have he : e ≤ n := by dsimp [e]; split <;> omega
  have hs : s ≤ r := inner_count_le n d _ hn hd (by split <;> omega)
  obtain ⟨P, hP, hfinish⟩ := hout n hn5 hn7
  obtain ⟨x, hxP, hcore⟩ := hinner n hn5 hn7 P hP
  obtain ⟨a,b,c,hfixed,hquot⟩ := hfinish x hxP
  exact ⟨a, b, c, glue_block hd he hs x a b c hfixed hcore hquot⟩

end OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1_H3_R1
