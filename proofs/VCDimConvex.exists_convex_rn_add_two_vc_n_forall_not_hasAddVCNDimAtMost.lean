import FormalConjectures.Other.VCDimConvex

/-!
# Convex sets of infinite `VCₙ` dimension in `ℝ^{n + 2}`

We prove `VCDimConvex.exists_convex_rn_add_two_vc_n_forall_not_hasAddVCNDimAtMost`: for every
`n : ℕ`, there exists a convex set `C ⊆ ℝ^{n + 2}` such that `¬ HasAddVCNDimAtMost C n d` for
every `d : ℕ`.

## Proof outline
1. Since `Fin n → ℕ` is countable, `|Set (Fin n → ℕ)| ≤ 2^ℵ₀ = |ℝ|`, giving an injection
   `e : Set (Fin n → ℕ) ↪ ℝ`.
2. For `p : Fin (n + 2) → ℝ`, let `q p = ∑ j : Fin (n + 1), (p j.castSucc)^2` and
   `z p = p (Fin.last (n + 1))`. Define the strict paraboloid epigraph
   `Kopen = { p | q p < z p }`, the boundary family
   `E = { bd S f | S : Set (Fin n → ℕ), f ∈ S }` where `bd S f` has coordinates
   `(f 0, ..., f (n - 1), e S, (e S)^2 + ∑ k, (f k)^2)`, and `C = Kopen ∪ E`.
3. By strict convexity of `q`, every open line segment between two distinct points of `C` lies
   strictly inside `Kopen ⊆ C`, so `C` is convex.
4. For any `d : ℕ`, define `x k m` with `(m : ℝ)` in coordinate `k` and `(m : ℝ)^2` in the last
   coordinate (and `0` elsewhere), and `y s` with `e (lift '' s)` in coordinate `n` and
   `(e (lift '' s))^2` in the last coordinate. Because the paraboloid height splits additively
   across the first `n` coordinates, `y s + ∑ k, x k (i k) = bd (lift '' s) (lift i)` lies on the
   paraboloid boundary, hence belongs to `C` if and only if it belongs to `E`, which by injectivity
   of `e` holds if and only if `i ∈ s`.
-/

-- Problem: VCₙ dimension of convex sets in ℝⁿ, ℝⁿ⁺¹, ℝⁿ⁺² — exists convex rn add two vc n forall not hasAddVCNDimAtMost
-- Upstream: formal-conjectures FormalConjectures/Other/VCDimConvex.lean:54 (declaration VCDimConvex.exists_convex_rn_add_two_vc_n_forall_not_hasAddVCNDimAtMost)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace VCDimConvexRN2Proof

private def qForm {n : ℕ} (p : Fin (n + 2) → ℝ) : ℝ :=
  ∑ j : Fin (n + 1), (p j.castSucc) ^ 2

private def zCoord {n : ℕ} (p : Fin (n + 2) → ℝ) : ℝ :=
  p (Fin.last (n + 1))

private def mkPt {n : ℕ} (u : Fin n → ℝ) (v w : ℝ) : Fin (n + 2) → ℝ :=
  fun i =>
    if h1 : i.val < n then u ⟨i.val, h1⟩
    else if i.val = n then v
    else w

private lemma mkPt_coord {n : ℕ} (u : Fin n → ℝ) (v w : ℝ) (k : Fin n) :
    mkPt u v w k.castSucc.castSucc = u k := by
  simp [mkPt, k.isLt]

private lemma mkPt_n {n : ℕ} (u : Fin n → ℝ) (v w : ℝ) :
    mkPt u v w (Fin.last n).castSucc = v := by
  simp [mkPt]

private lemma mkPt_last {n : ℕ} (u : Fin n → ℝ) (v w : ℝ) :
    mkPt u v w (Fin.last (n + 1)) = w := by
  simp [mkPt]

private lemma qForm_mkPt {n : ℕ} (u : Fin n → ℝ) (v w : ℝ) :
    qForm (mkPt u v w) = (∑ k : Fin n, (u k) ^ 2) + v ^ 2 := by
  rw [qForm, Fin.sum_univ_castSucc, mkPt_n]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mkPt_coord]

private lemma convex_paraboloid_union_boundary {n : ℕ}
    (E : Set (Fin (n + 2) → ℝ)) (hE : ∀ p ∈ E, qForm p = zCoord p) :
    Convex ℝ ({ p : Fin (n + 2) → ℝ | qForm p < zCoord p } ∪ E) := by
  intro p hp q hq a b ha hb hab
  by_cases ha0 : a = 0
  · subst ha0
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hq
  by_cases hb0 : b = 0
  · subst hb0
    have ha1 : a = 1 := by linarith
    subst ha1
    simpa using hp
  by_cases hpq : p = q
  · subst hpq
    rw [← add_smul, hab, one_smul]
    exact hp
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hp_le : qForm p ≤ zCoord p := by
    rcases hp with hp | hp
    · exact le_of_lt hp
    · exact le_of_eq (hE p hp)
  have hq_le : qForm q ≤ zCoord q := by
    rcases hq with hq | hq
    · exact le_of_lt hq
    · exact le_of_eq (hE q hq)
  left
  change qForm (a • p + b • q) < zCoord (a • p + b • q)
  have hterm : ∀ j : Fin (n + 1),
      ((a • p + b • q) j.castSucc) ^ 2 + a * b * (p j.castSucc - q j.castSucc) ^ 2 =
        a * (p j.castSucc) ^ 2 + b * (q j.castSucc) ^ 2 := by
    intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1a : a * (1 - a) = a * b := by nlinarith
    have h1b : b * (1 - b) = a * b := by nlinarith
    nlinarith
  have hid :
      qForm (a • p + b • q) +
        a * b * (∑ j : Fin (n + 1), (p j.castSucc - q j.castSucc) ^ 2) =
      a * qForm p + b * qForm q := by
    simp only [qForm, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm j
  have hz : zCoord (a • p + b • q) = a * zCoord p + b * zCoord q := by
    simp [zCoord]
  rw [hz]
  by_cases hbase : ∀ j : Fin (n + 1), p j.castSucc = q j.castSucc
  · have hdiff0 : ∑ j : Fin (n + 1), (p j.castSucc - q j.castSucc) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hbase j, sub_self, zero_pow (by norm_num)]
    have hzne : zCoord p ≠ zCoord q := by
      intro hzeq
      apply hpq
      ext i
      refine Fin.lastCases hzeq (fun j => hbase j) i
    have hstrict : qForm p < zCoord p ∨ qForm q < zCoord q := by
      rcases hp with hp | hp
      · exact Or.inl hp
      · rcases hq with hq | hq
        · exact Or.inr hq
        · exfalso
          have hqeq : qForm p = qForm q := by
            simp only [qForm]
            exact Finset.sum_congr rfl fun j _ => by rw [hbase j]
          exact hzne ((hE p hp).symm.trans (hqeq.trans (hE q hq)))
    rcases hstrict with hlt | hlt
    · have h1 : a * qForm p < a * zCoord p := mul_lt_mul_of_pos_left hlt ha_pos
      have h2 : b * qForm q ≤ b * zCoord q := mul_le_mul_of_nonneg_left hq_le hb
      rw [hdiff0, mul_zero, add_zero] at hid
      linarith
    · have h1 : a * qForm p ≤ a * zCoord p := mul_le_mul_of_nonneg_left hp_le ha
      have h2 : b * qForm q < b * zCoord q := mul_lt_mul_of_pos_left hlt hb_pos
      rw [hdiff0, mul_zero, add_zero] at hid
      linarith
  · push Not at hbase
    rcases hbase with ⟨j₀, hj₀⟩
    have hsum_pos : 0 < ∑ j : Fin (n + 1), (p j.castSucc - q j.castSucc) ^ 2 := by
      have hsq : 0 < (p j₀.castSucc - q j₀.castSucc) ^ 2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr hj₀)
      have hle : (p j₀.castSucc - q j₀.castSucc) ^ 2 ≤
          ∑ j : Fin (n + 1), (p j.castSucc - q j.castSucc) ^ 2 :=
        Finset.single_le_sum
          (f := fun j : Fin (n + 1) => (p j.castSucc - q j.castSucc) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ j₀)
      linarith
    have hab_pos : 0 < a * b * ∑ j : Fin (n + 1), (p j.castSucc - q j.castSucc) ^ 2 := by
      positivity
    have h1 : a * qForm p ≤ a * zCoord p := mul_le_mul_of_nonneg_left hp_le ha
    have h2 : b * qForm q ≤ b * zCoord q := mul_le_mul_of_nonneg_left hq_le hb
    linarith

end VCDimConvexRN2Proof

open VCDimConvex VCDimConvexRN2Proof

theorem OMA.solution :
    type_of% @VCDimConvex.exists_convex_rn_add_two_vc_n_forall_not_hasAddVCNDimAtMost := by
  intro n
  have hemb : Nonempty (Set (Fin n → ℕ) ↪ ℝ) := by
    rw [← Cardinal.le_def]
    calc
      Cardinal.mk (Set (Fin n → ℕ)) = 2 ^ Cardinal.mk (Fin n → ℕ) := Cardinal.mk_set
      _ ≤ 2 ^ Cardinal.aleph0 :=
            Cardinal.power_le_power_left (by norm_num) Cardinal.mk_le_aleph0
      _ = Cardinal.continuum := Cardinal.two_power_aleph0
      _ = Cardinal.mk ℝ := Cardinal.mk_real.symm
  rcases hemb with ⟨e⟩
  let bd : Set (Fin n → ℕ) → (Fin n → ℕ) → (Fin (n + 2) → ℝ) :=
    fun S f => mkPt (fun k => (f k : ℝ)) (e S) ((e S) ^ 2 + ∑ k : Fin n, (f k : ℝ) ^ 2)
  let E : Set (Fin (n + 2) → ℝ) :=
    { p | ∃ (S : Set (Fin n → ℕ)) (f : Fin n → ℕ), f ∈ S ∧ p = bd S f }
  let C : Set (Fin (n + 2) → ℝ) :=
    { p : Fin (n + 2) → ℝ | qForm p < zCoord p } ∪ E
  refine ⟨C, ?_, ?_⟩
  · refine convex_paraboloid_union_boundary E ?_
    rintro p ⟨S, f, _, rfl⟩
    simp only [bd, qForm_mkPt, zCoord, mkPt_last]
    ring
  · intro d hvc
    let x : Fin n → Fin (d + 1) → (Fin (n + 2) → ℝ) :=
      fun k m =>
        mkPt (fun k' => if k' = k then (m.val : ℝ) else 0) 0 ((m.val : ℝ) ^ 2)
    let lift : (Fin n → Fin (d + 1)) → (Fin n → ℕ) := fun i k => (i k).val
    have hlift_inj : Function.Injective lift := by
      intro i₁ i₂ h
      ext k
      exact congr_fun h k
    let Smap : Set (Fin n → Fin (d + 1)) → Set (Fin n → ℕ) := fun s => lift '' s
    let y : Set (Fin n → Fin (d + 1)) → (Fin (n + 2) → ℝ) :=
      fun s => mkPt (fun _ => 0) (e (Smap s)) ((e (Smap s)) ^ 2)
    refine hvc x y fun i s => ?_
    have hsum_eq : y s + ∑ k : Fin n, x k (i k) = bd (Smap s) (lift i) := by
      ext j
      simp only [Pi.add_apply, Finset.sum_apply, y, x, bd, lift, mkPt]
      by_cases h1 : j.val < n
      · simp only [h1, ↓reduceDIte, zero_add]
        have hsingle :
            ∑ k : Fin n, (if (⟨j.val, h1⟩ : Fin n) = k then ((i k).val : ℝ) else 0) =
              ((i ⟨j.val, h1⟩).val : ℝ) := by
          rw [Finset.sum_eq_single ⟨j.val, h1⟩]
          · simp
          · intro k _ hk
            simp [Ne.symm hk]
          · intro hmem
            exact absurd (Finset.mem_univ _) hmem
        exact hsingle
      · simp only [h1, ↓reduceDIte]
        by_cases h2 : j.val = n
        · simp [h2]
        · simp [h2]
    rw [hsum_eq]
    constructor
    · rintro (hlt | ⟨S', f', hf', heq⟩)
      · exfalso
        have hq : qForm (bd (Smap s) (lift i)) = zCoord (bd (Smap s) (lift i)) := by
          simp only [bd, qForm_mkPt, zCoord, mkPt_last]
          ring
        change qForm (bd (Smap s) (lift i)) < zCoord (bd (Smap s) (lift i)) at hlt
        linarith
      · have hn_eq : e (Smap s) = e S' := by
          simpa [bd, mkPt_n] using congr_fun heq (Fin.last n).castSucc
        have hS_eq : Smap s = S' := e.injective hn_eq
        have hf_eq : lift i = f' := by
          ext k
          have hk : ((lift i k : ℕ) : ℝ) = ((f' k : ℕ) : ℝ) := by
            simpa [bd, mkPt_coord] using congr_fun heq k.castSucc.castSucc
          exact Nat.cast_injective hk
        rw [← hS_eq, ← hf_eq] at hf'
        rcases hf' with ⟨i', hi's, hi'eq⟩
        rwa [← hlift_inj hi'eq]
    · intro his
      exact Or.inr ⟨Smap s, lift i, ⟨i, his, rfl⟩, rfl⟩
