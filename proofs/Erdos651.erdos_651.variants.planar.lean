import FormalConjectures.ErdosProblems.«651»
import Mathlib.Algebra.Module.Submodule.Union

/-!
The exponential witness uses translated copies from the Erdős–Szekeres cup and cap
construction (https://www.numdam.org/item/CM_1935__2__463_0/).
A separate planar finite Ramsey argument proves that the defining infimum is attained.
-/

open Filter
open scoped EuclideanGeometry Finset

open Finset
open scoped EuclideanGeometry

namespace PlanarSzekeres

private abbrev Point := ℝ × ℝ

private def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1)

private def Chain (up : Bool) (S : Finset Point) : Prop :=
  ∀ ⦃a b c : Point⦄, a ∈ S → b ∈ S → c ∈ S → a.1 < b.1 → b.1 < c.1 →
    if up then 0 < orient a b c else orient a b c < 0

private lemma chain_mono {up : Bool} {T S : Finset Point} (h : Chain up S) (hT : T ⊆ S) :
    Chain up T := by
  intro a b c ha hb hc hab hbc
  exact h (hT ha) (hT hb) (hT hc) hab hbc

private def Box (W : ℕ) (B : ℝ) (S : Finset Point) : Prop :=
  ∀ p ∈ S, ∃ i : ℕ, i < W ∧ p.1 = (i : ℝ) ∧ 0 ≤ p.2 ∧ p.2 ≤ B

private structure Config (m : ℕ) (B : ℝ) (S : Finset Point) : Prop where
  card : S.card = 2 ^ m
  box : Box (2 ^ m) B S
  inj : Set.InjOn Prod.fst (S : Set Point)
  nonzero : ∀ ⦃a b c : Point⦄, a ∈ S → b ∈ S → c ∈ S → a.1 < b.1 → b.1 < c.1 →
    orient a b c ≠ 0
  chain_card : ∀ (up : Bool) (T : Finset Point), T ⊆ S → Chain up T → T.card ≤ m + 1

private def rise (W : ℕ) (B : ℝ) : ℝ := (2 * (W : ℝ) + 2) * (B + 1)

private def shift (W : ℕ) (B : ℝ) (p : Point) : Point := (p.1 + W, p.2 + rise W B)

private lemma shift_injective (W : ℕ) (B : ℝ) : Function.Injective (shift W B) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (add_right_cancel h1) (add_right_cancel h2)

private lemma orient_shift (W : ℕ) (B : ℝ) (a b c : Point) :
    orient (shift W B a) (shift W B b) (shift W B c) = orient a b c := by
  unfold orient shift
  dsimp only
  ring

private lemma shift_lt_iff {W : ℕ} {B : ℝ} {a b : Point} :
    (shift W B a).1 < (shift W B b).1 ↔ a.1 < b.1 := by
  simp [shift]

private lemma box_bounds {W : ℕ} {B : ℝ} {S : Finset Point} (hbox : Box W B S)
    {p : Point} (hp : p ∈ S) :
    0 ≤ p.1 ∧ p.1 < (W : ℝ) ∧ 0 ≤ p.2 ∧ p.2 ≤ B := by
  obtain ⟨i, hi, he, hy₀, hy₁⟩ := hbox p hp
  exact ⟨he ▸ Nat.cast_nonneg i, he ▸ (by exact_mod_cast hi), hy₀, hy₁⟩

private lemma internal_gap {W : ℕ} {B : ℝ} {S : Finset Point} (hbox : Box W B S)
    {a b : Point} (ha : a ∈ S) (hb : b ∈ S) (hab : a.1 < b.1) :
    1 ≤ b.1 - a.1 ∧ b.2 - a.2 ≤ B := by
  obtain ⟨i, _, hi, ha₀, _⟩ := hbox a ha
  obtain ⟨j, _, hj, _, hb₁⟩ := hbox b hb
  have hij : i < j := by
    rw [hi, hj] at hab
    exact_mod_cast hab
  have h : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (by omega : i + 1 ≤ j)
  constructor <;> linarith

private lemma cross_gap {W : ℕ} {B : ℝ} {S : Finset Point} (hbox : Box W B S)
    {a b : Point} (ha : a ∈ S) (hb : b ∈ S) :
    a.1 < (shift W B b).1 ∧ (shift W B b).1 - a.1 ≤ 2 * (W : ℝ) ∧
      rise W B - B ≤ (shift W B b).2 - a.2 := by
  obtain ⟨ha₀, ha₁, -, ha₂⟩ := box_bounds hbox ha
  obtain ⟨hb₀, hb₁, hb₂, -⟩ := box_bounds hbox hb
  unfold shift
  dsimp only
  exact ⟨by linarith, by linarith, by linarith⟩

private lemma tilt_gap (W : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    B * (2 * (W : ℝ)) < rise W B - B := by
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  dsimp [rise]
  linarith

private lemma cross_orient_positive {W : ℕ} {B : ℝ} {S : Finset Point}
    (hbox : Box W B S) (hB : 0 ≤ B) {a b c : Point}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a.1 < b.1) :
    0 < orient a b (shift W B c) := by
  obtain ⟨hx, hy⟩ := internal_gap hbox ha hb hab
  obtain ⟨hsep, hdx, hdy⟩ := cross_gap hbox hb hc
  have hgap := tilt_gap W hB
  have hprod : 0 ≤ B * (2 * (W : ℝ)) := mul_nonneg hB (by positivity)
  have hl := mul_le_mul hx hdy (hprod.trans hgap.le) (by linarith)
  have hr := mul_le_mul hy hdx (by linarith) hB
  unfold orient
  linarith

private lemma cross_orient_negative {W : ℕ} {B : ℝ} {S : Finset Point}
    (hbox : Box W B S) (hB : 0 ≤ B) {a b c : Point}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hbc : b.1 < c.1) :
    orient a (shift W B b) (shift W B c) < 0 := by
  obtain ⟨hx, hy⟩ := internal_gap hbox hb hc hbc
  obtain ⟨hsep, hdx, hdy⟩ := cross_gap hbox ha hb
  have hgap := tilt_gap W hB
  have hprod : 0 ≤ B * (2 * (W : ℝ)) := mul_nonneg hB (by positivity)
  have hl := mul_le_mul hdy hx (by norm_num) (by linarith)
  have hr := mul_le_mul hy hdx (by linarith) hB
  change ((shift W B b).1 - a.1) * ((shift W B c).2 - (shift W B b).2) -
    ((shift W B b).2 - a.2) * ((shift W B c).1 - (shift W B b).1) < 0
  have hyShift : (shift W B c).2 - (shift W B b).2 = c.2 - b.2 := by unfold shift; simp
  have hxShift : (shift W B c).1 - (shift W B b).1 = c.1 - b.1 := by unfold shift; simp
  rw [hyShift, hxShift]
  linarith [mul_comm B (2 * (W : ℝ))]

private lemma shifted_chain_card {m : ℕ} {B : ℝ} {S : Finset Point} (h : Config m B S)
    (up : Bool) {T : Finset Point} (hT : T ⊆ S.image (shift (2 ^ m) B)) (ht : Chain up T) :
    T.card ≤ m + 1 := by
  classical
  let U := S.filter fun p => shift (2 ^ m) B p ∈ T
  have hU : U ⊆ S := Finset.filter_subset _ _
  have him : U.image (shift (2 ^ m) B) = T := by
    ext p
    constructor
    · intro hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
      exact (Finset.mem_filter.1 ha).2
    · intro hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (hT hp)
      exact Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, hp⟩, rfl⟩
  have hcu : Chain up U := by
    intro a b c ha hb hc hab hbc
    have hh := ht (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2 (Finset.mem_filter.1 hc).2
      (shift_lt_iff.2 hab) (shift_lt_iff.2 hbc)
    rwa [orient_shift] at hh
  rw [← him, Finset.card_image_of_injective _ (shift_injective _ _)]
  exact h.chain_card up U hU hcu

private lemma split_chain_card {m : ℕ} {B : ℝ} {S : Finset Point}
    (h : Config m B S) (hB : 0 ≤ B) (up : Bool)
    {T : Finset Point} (hT : T ⊆ S ∪ S.image (shift (2 ^ m) B)) (ht : Chain up T) :
    T.card ≤ m + 2 := by
  classical
  let W : ℕ := 2 ^ m
  let R := S.image (shift W B)
  let L' := T ∩ S
  let R' := T ∩ R
  have hL (p : Point) (hp : p ∈ L') : p ∈ T ∧ p ∈ S := Finset.mem_inter.1 hp
  have hR (p : Point) (hp : p ∈ R') : p ∈ T ∧ ∃ q ∈ S, shift W B q = p :=
    ⟨(Finset.mem_inter.1 hp).1, Finset.mem_image.1 (Finset.mem_inter.1 hp).2⟩
  have hboth : T.card ≤ L'.card + R'.card := by
    have hsub : T ⊆ L' ∪ R' := by
      intro p hp
      rcases Finset.mem_union.1 (hT hp) with hl | hr
      · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hp, hl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hp, hr⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hleft := h.chain_card up L' Finset.inter_subset_right
    (chain_mono ht Finset.inter_subset_left)
  have hright : R'.card ≤ m + 1 := shifted_chain_card h up Finset.inter_subset_right
    (chain_mono ht (show R' ⊆ T from Finset.inter_subset_left))
  have hcup (hu : up = true) (hne : L'.Nonempty) : R'.card ≤ 1 := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨haT, haS⟩ := hL a ha
    refine Finset.card_le_one_iff.2 fun {b c} hb hc => ?_
    obtain ⟨hbT, b', hbS, rfl⟩ := hR b hb
    obtain ⟨hcT, c', hcS, rfl⟩ := hR c hc
    by_contra hne'
    have hn : b'.1 ≠ c'.1 := fun he => hne' (congrArg (shift W B) (h.inj hbS hcS he))
    have hbad {p q : Point} (hp : p ∈ S) (hq : q ∈ S) (hpT : shift W B p ∈ T)
        (hqT : shift W B q ∈ T) (hpq : p.1 < q.1) : False := by
      have hlt := ht haT hpT hqT (cross_gap h.box haS hp).1 (shift_lt_iff.2 hpq)
      rw [hu, if_pos rfl] at hlt
      exact (cross_orient_negative h.box hB haS hp hq hpq).not_gt hlt
    exact (lt_or_gt_of_ne hn).elim (hbad hbS hcS hbT hcT) (hbad hcS hbS hcT hbT)
  have hcap (hu : up = false) (hne : R'.Nonempty) : L'.card ≤ 1 := by
    obtain ⟨c, hc⟩ := hne
    obtain ⟨hcT, c', hcS, rfl⟩ := hR c hc
    refine Finset.card_le_one_iff.2 fun {a b} ha hb => ?_
    obtain ⟨haT, haS⟩ := hL a ha
    obtain ⟨hbT, hbS⟩ := hL b hb
    by_contra hne'
    have hn : a.1 ≠ b.1 := fun he => hne' (h.inj haS hbS he)
    have hbad {p q : Point} (hp : p ∈ S) (hq : q ∈ S) (hpT : p ∈ T)
        (hqT : q ∈ T) (hpq : p.1 < q.1) : False := by
      have hlt := ht hpT hqT hcT hpq (cross_gap h.box hq hcS).1
      simp only [hu, Bool.false_eq_true, if_false] at hlt
      exact (cross_orient_positive h.box hB hp hq hcS hpq).not_gt hlt
    exact (lt_or_gt_of_ne hn).elim (hbad haS hbS haT hbT) (hbad hbS haS hbT haT)
  cases up
  · rcases R'.eq_empty_or_nonempty with he | hn
    · simp only [he, Finset.card_empty, add_zero] at hboth
      omega
    · have := hcap rfl hn
      omega
  · rcases L'.eq_empty_or_nonempty with he | hn
    · simp only [he, Finset.card_empty, zero_add] at hboth
      omega
    · have := hcup rfl hn
      omega

private lemma configurations (m : ℕ) : ∃ B ≥ (0 : ℝ), ∃ S, Config m B S := by
  classical
  induction m with
  | zero =>
    refine ⟨0, le_rfl, {0}, by simp, ?_, ?_, ?_, ?_⟩
    · intro a ha
      obtain rfl := Finset.mem_singleton.1 ha
      exact ⟨0, by decide, by norm_num, le_rfl, le_rfl⟩
    · intro a ha b hb _
      exact (Finset.mem_singleton.1 ha).trans (Finset.mem_singleton.1 hb).symm
    · intro a b c ha hb hc hab hbc
      obtain rfl := Finset.mem_singleton.1 ha
      obtain rfl := Finset.mem_singleton.1 hb
      exact False.elim ((lt_irrefl _) hab)
    · intro up T hT ht
      simpa using Finset.card_le_card hT
  | succ m ih =>
    obtain ⟨B, hB, S, hS⟩ := ih
    let W : ℕ := 2 ^ m
    let R := S.image (shift W B)
    let U := S ∪ R
    have hRise : 0 ≤ rise W B := by unfold rise; positivity
    have hMem (a : Point) (ha : a ∈ U) : a ∈ S ∨ ∃ a' ∈ S, shift W B a' = a :=
      (Finset.mem_union.1 ha).imp_right Finset.mem_image.1
    have disj : Disjoint S R := by
      refine Finset.disjoint_left.2 fun a ha hb => ?_
      obtain ⟨b, hbS, rfl⟩ := Finset.mem_image.1 hb
      exact (lt_irrefl _) (cross_gap hS.box ha hbS).1
    refine ⟨B + rise W B, add_nonneg hB hRise, U, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show U = S ∪ R from rfl, Finset.card_union_of_disjoint disj]
      rw [show R = S.image (shift W B) from rfl, Finset.card_image_of_injective _ (shift_injective _ _),
        hS.card, pow_succ]
      omega
    · intro a ha
      rw [pow_succ]
      rcases hMem a ha with h | ⟨b, hb, rfl⟩
      · obtain ⟨i, hi, hx, h₀, h₁⟩ := hS.box a h
        exact ⟨i, by omega, hx, h₀, by linarith⟩
      · obtain ⟨i, hi, hx, h₀, h₁⟩ := hS.box b hb
        exact ⟨i + W, by dsimp [W]; omega, by simp [shift, hx],
          add_nonneg h₀ hRise, by change b.2 + rise W B ≤ B + rise W B; linarith⟩
    · intro a ha b hb hab
      rcases hMem a ha with haL | ⟨a', haR, rfl⟩ <;> rcases hMem b hb with hbL | ⟨b', hbR, rfl⟩
      · exact hS.inj haL hbL hab
      · exact ((cross_gap hS.box haL hbR).1.ne hab).elim
      · exact ((cross_gap hS.box hbL haR).1.ne hab.symm).elim
      · exact congrArg (shift W B) (hS.inj haR hbR (add_right_cancel hab))
    · intro a b c ha hb hc hab hbc
      rcases hMem a ha with haL | ⟨a', haR, rfl⟩ <;>
        rcases hMem b hb with hbL | ⟨b', hbR, rfl⟩ <;>
        rcases hMem c hc with hcL | ⟨c', hcR, rfl⟩
      · exact hS.nonzero haL hbL hcL hab hbc
      · exact (cross_orient_positive hS.box hB haL hbL hcR hab).ne'
      · exact ((cross_gap hS.box hcL hbR).1.not_gt hbc).elim
      · exact (cross_orient_negative hS.box hB haL hbR hcR (shift_lt_iff.1 hbc)).ne
      · exact ((cross_gap hS.box hbL haR).1.not_gt hab).elim
      · exact ((cross_gap hS.box hbL haR).1.not_gt hab).elim
      · exact ((cross_gap hS.box hcL hbR).1.not_gt hbc).elim
      · rw [orient_shift]
        exact hS.nonzero haR hbR hcR (shift_lt_iff.1 hab) (shift_lt_iff.1 hbc)
    · intro up T hT ht
      exact split_chain_card hS hB up hT ht


/-- The point on the chord with the same abscissa as b records the orientation of a,b,c. -/
private lemma chord {K : Set Point} (hK : Convex ℝ K) {a b c : Point} (ha : a ∈ K) (hc : c ∈ K)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) :
    ∃ p ∈ K, p.1 = b.1 ∧ orient a b c = (c.1 - a.1) * (p.2 - b.2) := by
  have hden : 0 < c.1 - a.1 := by linarith
  let t := (b.1 - a.1) / (c.1 - a.1)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 hab.le) hden.le
  have ht1 : t ≤ 1 := (div_le_iff₀ hden).2 (by linarith)
  have he : t * (c.1 - a.1) = b.1 - a.1 := div_mul_cancel₀ _ hden.ne'
  let p := (1 - t) • a + t • c
  refine ⟨p, hK ha hc (sub_nonneg.2 ht1) ht0 (by ring), ?_, ?_⟩
  · change (1 - t) * a.1 + t * c.1 = b.1
    linarith only [he]
  · change orient a b c = (c.1 - a.1) * ((1 - t) * a.2 + t * c.2 - b.2)
    unfold orient
    linear_combination -(c.2 - a.2) * he

private lemma between_vertical {K : Set Point} (hK : Convex ℝ K) {p b q : Point}
    (hp : p ∈ K) (hq : q ∈ K) (hpx : p.1 = b.1) (hqx : q.1 = b.1)
    (hpy : p.2 < b.2) (hqy : b.2 < q.2) : b ∈ K := by
  have hden : 0 < q.2 - p.2 := by linarith
  let t := (b.2 - p.2) / (q.2 - p.2)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 hpy.le) hden.le
  have ht1 : t ≤ 1 := (div_le_iff₀ hden).2 (by linarith)
  have he : t * (q.2 - p.2) = b.2 - p.2 := div_mul_cancel₀ _ hden.ne'
  have hm : (1 - t) • p + t • q ∈ K := hK hp hq (sub_nonneg.2 ht1) ht0 (by ring)
  have heq : (1 - t) • p + t • q = b := by
    apply Prod.ext
    · change (1 - t) * p.1 + t * q.1 = b.1
      rw [hpx, hqx]
      ring
    · change (1 - t) * p.2 + t * q.2 = b.2
      linarith only [he]
  exact heq ▸ hm

private lemma no_opposite_chords {T : Finset Point}
    (hconv : ConvexIndependent ℝ ((↑) : ↥(T : Set Point) → Point))
    {a b c d e : Point} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T) (he : e ∈ T)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hdb : d.1 < b.1) (hbe : b.1 < e.1)
    (hneg : orient a b c < 0) (hpos : 0 < orient d b e) : False := by
  let K := convexHull ℝ ((T : Set Point) \ {b})
  have hK : Convex ℝ K := convex_convexHull _ _
  have hmem (u : Point) (hu : u ∈ T) (hne : u.1 ≠ b.1) : u ∈ K :=
    subset_convexHull _ _ ⟨hu, fun heq => hne (congrArg Prod.fst heq)⟩
  obtain ⟨p, hp, hpx, hpo⟩ := chord hK (hmem a ha hab.ne) (hmem c hc hbc.ne') hab hbc
  obtain ⟨q, hq, hqx, hqo⟩ := chord hK (hmem d hd hdb.ne) (hmem e he hbe.ne') hdb hbe
  have hpy : p.2 < b.2 := by
    have hneg' : (c.1 - a.1) * (p.2 - b.2) < 0 := hpo ▸ hneg
    have hden : 0 < c.1 - a.1 := by linarith
    exact sub_neg.1 (neg_of_mul_neg_right hneg' hden.le)
  have hqy : b.2 < q.2 := by
    have hpos' : 0 < (e.1 - d.1) * (q.2 - b.2) := hqo ▸ hpos
    have hden : 0 < e.1 - d.1 := by linarith
    exact sub_pos.1 (pos_of_mul_pos_right hpos' hden.le)
  exact (convexIndependent_set_iff_notMem_convexHull_sdiff.1 hconv) b hb
    (between_vertical hK hp hq hpx hqx hpy hqy)

private def LowerAt (T : Finset Point) (b : Point) : Prop :=
  ∀ ⦃a c : Point⦄, a ∈ T → c ∈ T → a.1 < b.1 → b.1 < c.1 → 0 < orient a b c

private lemma convex_subset_card {m : ℕ} {B : ℝ} {S T : Finset Point}
    (hS : Config m B S) (hT : T ⊆ S)
    (hc : ConvexIndependent ℝ ((↑) : ↥(T : Set Point) → Point)) :
    T.card ≤ 2 * m + 2 := by
  classical
  let A := T.filter (LowerAt T)
  let D := T.filter fun p => ¬ LowerAt T p
  have hA : A ⊆ T := Finset.filter_subset _ _
  have hD : D ⊆ T := Finset.filter_subset _ _
  have ha : Chain true A := by
    intro a b c ha hb hc hab hbc
    exact (Finset.mem_filter.1 hb).2 (hA ha) (hA hc) hab hbc
  have hd : Chain false D := by
    intro a b c ha hb hcc hab hbc
    have hn : ¬ LowerAt T b := (Finset.mem_filter.1 hb).2
    unfold LowerAt at hn
    push Not at hn
    obtain ⟨x, y, hx, hy, hxb, hby, hxy⟩ := hn
    have hneg : orient x b y < 0 :=
      lt_of_le_of_ne hxy (hS.nonzero (hT hx) (hT (hD hb)) (hT hy) hxb hby)
    change orient a b c < 0
    by_contra! hp
    have hp' := lt_of_le_of_ne hp (hS.nonzero (hT (hD ha)) (hT (hD hb)) (hT (hD hcc)) hab hbc).symm
    exact no_opposite_chords hc hx (hD hb) hy (hD ha) (hD hcc) hxb hby hab hbc hneg hp'
  have hcA := hS.chain_card true A (hA.trans hT) ha
  have hcD := hS.chain_card false D (hD.trans hT) hd
  have hsum : A.card + D.card = T.card := Finset.card_filter_add_card_filter_not (LowerAt T)
  omega

private lemma collinear_orient {K : Set Point} (h : Collinear ℝ K) {a b c : Point}
    (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) : orient a b c = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem ha).1 h
  obtain ⟨s, hs⟩ := hv b hb
  obtain ⟨t, ht⟩ := hv c hc
  change b = s • v + a at hs
  change c = t • v + a at ht
  rw [hs, ht]
  unfold orient
  change (s * v.1 + a.1 - a.1) * (t * v.2 + a.2 - (s * v.2 + a.2)) -
    (s * v.2 + a.2 - a.2) * (t * v.1 + a.1 - (s * v.1 + a.1)) = 0
  ring

private lemma general_position_prod {m : ℕ} {B : ℝ} {S T : Finset Point} (hS : Config m B S)
    (hT : T ⊆ S) (hc : T.card ≤ 3) :
    AffineIndependent ℝ ((↑) : ↥(T : Set Point) → Point) := by
  classical
  by_cases hlo : T.card ≤ 1
  · let hs : Subsingleton ↥(T : Set Point) :=
      Fintype.card_le_one_iff_subsingleton.1 (by simpa using hlo)
    exact affineIndependent_of_subsingleton _ _
  by_cases htwo : T.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 htwo
    have h := (affineIndependent_of_ne ℝ hab).range
    have hr : Set.range ![a, b] = (({a, b} : Finset Point) : Set Point) := by
      rw [Matrix.range_cons_cons_empty]
      simp
    rw [hr] at h
    exact h
  have hthree : T.card = 3 := by omega
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hthree
  have habx : a.1 ≠ b.1 := fun h => hab (hS.inj (hT (by simp)) (hT (by simp)) h)
  have hacx : a.1 ≠ c.1 := fun h => hac (hS.inj (hT (by simp)) (hT (by simp)) h)
  have hbcx : b.1 ≠ c.1 := fun h => hbc (hS.inj (hT (by simp)) (hT (by simp)) h)
  have hn : ¬ Collinear ℝ ({a, b, c} : Set Point) := by
    intro h
    have hbad {x y z : Point} (hx : x ∈ ({a, b, c} : Finset Point))
        (hy : y ∈ ({a, b, c} : Finset Point)) (hz : z ∈ ({a, b, c} : Finset Point))
        (hxy : x.1 < y.1) (hyz : y.1 < z.1) : False :=
      (hS.nonzero (hT hx) (hT hy) (hT hz) hxy hyz)
        (collinear_orient h (by simpa using hx) (by simpa using hy) (by simpa using hz))
    rcases lt_or_gt_of_ne habx with h1 | h1
    · rcases lt_or_gt_of_ne hbcx with h2 | h2
      · exact hbad (by simp) (by simp) (by simp) h1 h2
      rcases lt_or_gt_of_ne hacx with h3 | h3
      · exact hbad (by simp) (by simp) (by simp) h3 h2
      · exact hbad (by simp) (by simp) (by simp) h3 h1
    · rcases lt_or_gt_of_ne hacx with h3 | h3
      · exact hbad (by simp) (by simp) (by simp) h1 h3
      rcases lt_or_gt_of_ne hbcx with h2 | h2
      · exact hbad (by simp) (by simp) (by simp) h2 h3
      · exact hbad (by simp) (by simp) (by simp) h2 h1
  have hi := (affineIndependent_iff_not_collinear_set.2 hn).range
  have hr : Set.range ![a, b, c] = (({a, b, c} : Finset Point) : Set Point) := by
    rw [Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union]
    simp
  rw [hr] at hi
  exact hi

private noncomputable def coords : (ℝ^2) ≃ₗ[ℝ] Point :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv.trans
    (LinearEquiv.piFinTwo ℝ (fun _ => ℝ))

theorem witness (m : ℕ) :
    ∃ X : Finset (ℝ^2), X.card = 2 ^ m ∧ Erdos651.IsInGeneralPosition X ∧
      ∀ n, Erdos651.HasConvexSubset n X → n ≤ 2 * m + 2 := by
  classical
  obtain ⟨B, _, S, hS⟩ := configurations m
  let e := coords
  let X := S.image e.symm
  have hXcard : X.card = 2 ^ m := by
    rw [Finset.card_image_of_injective _ e.symm.injective, hS.card]
  have hImage (Y : Finset (ℝ^2)) (hY : Y ⊆ X) : Y.image e ⊆ S := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (hY hq)
    simpa using ha
  have hYcard (Y : Finset (ℝ^2)) : (Y.image e).card = Y.card :=
    Finset.card_image_of_injective _ e.injective
  refine ⟨X, hXcard, ?_, ?_⟩
  · intro Y hY hcard
    let T := Y.image e
    have hi := general_position_prod hS (hImage Y hY) (by simpa [hYcard] using hcard)
    let j : ↥(Y : Set (ℝ^2)) ↪ ↥(T : Set Point) :=
      ⟨fun a => ⟨e a, Finset.mem_image.2 ⟨a.val, a.property, rfl⟩⟩,
        fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h))⟩
    apply AffineIndependent.of_comp e.toAffineMap
    exact hi.comp_embedding j
  · intro n hn
    obtain ⟨Y, hY, hYn, hc⟩ := hn
    let T := Y.image e
    have hT : T ⊆ S := hImage Y hY
    have hTc : ConvexIndependent ℝ ((↑) : ↥(T : Set Point) → Point) := by
      rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hc ⊢
      intro p hp hpHull
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
      apply hc q hq
      have himage : e.symm '' ((T : Set Point) \ {e q}) ⊆ (Y : Set (ℝ^2)) \ {q} := by
        rintro _ ⟨u, hu, rfl⟩
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hu.1
        refine ⟨by simpa using hv, ?_⟩
        simpa using show e v ≠ e q from hu.2
      apply convexHull_mono himage
      change q ∈ convexHull ℝ (e.symm.toLinearMap '' ((T : Set Point) \ {e q}))
      rw [← e.symm.toLinearMap.image_convexHull]
      exact ⟨e q, hpHull, e.symm_apply_apply q⟩
    have hh := convex_subset_card hS hT hTc
    change (Y.image e).card ≤ 2 * m + 2 at hh
    simpa [hYcard, hYn] using hh

end PlanarSzekeres

theorem OMA.finite_ramsey_sets (α : Type*) [DecidableEq α] (r n : ℕ) :
    ∃ N : ℕ, ∀ (X : Finset α), N ≤ X.card → ∀ c : Finset α → Bool,
      ∃ Y ⊆ X, Y.card = n ∧ ∃ b : Bool, ∀ A ⊆ Y, A.card = r → c A = b := by
  induction r generalizing n with
  | zero =>
    refine ⟨n, fun X hX c => ?_⟩
    obtain ⟨Y, hYX, hcard⟩ := Finset.exists_subset_card_eq hX
    refine ⟨Y, hYX, hcard, c ∅, fun A _ hA => ?_⟩
    rw [Finset.card_eq_zero.mp hA]
  | succ r ih =>
    have stage (t : ℕ) : ∃ N : ℕ, ∀ (X : Finset α), N ≤ X.card → ∀ c : Finset α → Bool,
        ∃ Y ⊆ X, Y.card = t ∧ ∃ labels : α → Bool,
          ∀ A ⊆ Y, A.card = r + 1 → ∃ a ∈ A, c A = labels a := by
      induction t with
      | zero =>
        refine ⟨0, fun X _ _ => ⟨∅, Finset.empty_subset X, rfl, fun _ => false, ?_⟩⟩
        intro A hA hcard
        have hempty := Finset.subset_empty.mp hA
        simp [hempty] at hcard
      | succ t it =>
        obtain ⟨M, hM⟩ := it
        obtain ⟨N, hN⟩ := ih M
        refine ⟨N + 1, fun X hX c => ?_⟩
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
        have herase : N ≤ (X.erase x).card := by
          rw [Finset.card_erase_of_mem hx]
          omega
        obtain ⟨R, hR, hcardR, b, hb⟩ := hN (X.erase x) herase (fun A => c (insert x A))
        obtain ⟨Y, hY, hcard, labels, hlabels⟩ := hM R hcardR.ge c
        have hxY : x ∉ Y := fun h => (Finset.mem_erase.mp (hR (hY h))).1 rfl
        have hYX := hY.trans (hR.trans (Finset.erase_subset x X))
        refine ⟨insert x Y, Finset.insert_subset hx hYX, by simp [hxY, hcard],
          Function.update labels x b, ?_⟩
        intro A hA hcardA
        by_cases hxA : x ∈ A
        · have hAY : A.erase x ⊆ Y := by
            intro a ha
            obtain ⟨hne, haA⟩ := Finset.mem_erase.mp ha
            exact (Finset.mem_insert.mp (hA haA)).resolve_left hne
          have hac : (A.erase x).card = r := by rw [Finset.card_erase_of_mem hxA, hcardA]; simp
          refine ⟨x, hxA, ?_⟩
          simpa [Finset.insert_erase hxA] using hb _ (hAY.trans hY) hac
        · have hAY : A ⊆ Y := by
            intro a ha
            exact (Finset.mem_insert.mp (hA ha)).resolve_left (fun he => hxA (he ▸ ha))
          obtain ⟨a, ha, hc⟩ := hlabels A hAY hcardA
          have hax : a ≠ x := by
            rintro rfl
            exact hxA ha
          exact ⟨a, ha, by rwa [Function.update_of_ne hax]⟩
    obtain ⟨N, hN⟩ := stage (2 * n)
    refine ⟨N, fun X hX c => ?_⟩
    obtain ⟨Y, hYX, hcard, labels, hlabels⟩ := hN X hX c
    let U := Y.filter fun a => labels a = true
    let V := Y.filter fun a => labels a ≠ true
    have hsum : U.card + V.card = 2 * n :=
      (Finset.card_filter_add_card_filter_not (s := Y) _).trans hcard
    by_cases hU : n ≤ U.card
    · obtain ⟨Z, hZ, hcardZ⟩ := Finset.exists_subset_card_eq hU
      have hZY := hZ.trans (Finset.filter_subset _ _)
      refine ⟨Z, hZY.trans hYX, hcardZ, true, ?_⟩
      intro A hA hcardA
      obtain ⟨a, ha, he⟩ := hlabels A (hA.trans hZY) hcardA
      exact he.trans (Finset.mem_filter.mp (hZ (hA ha))).2
    · have hV : n ≤ V.card := by omega
      obtain ⟨Z, hZ, hcardZ⟩ := Finset.exists_subset_card_eq hV
      have hZY := hZ.trans (Finset.filter_subset _ _)
      refine ⟨Z, hZY.trans hYX, hcardZ, false, ?_⟩
      intro A hA hcardA
      obtain ⟨a, ha, he⟩ := hlabels A (hA.trans hZY) hcardA
      have ht := (Finset.mem_filter.mp (hZ (hA ha))).2
      exact he.trans (by cases h : labels a <;> simp_all)

theorem OMA.planar_coordinates (X : Finset (ℝ^2)) :
    ∃ x y : (ℝ^2) →ₗ[ℝ] ℝ, Set.InjOn x (X : Set (ℝ^2)) ∧
      ∀ p q, x p = x q → y p = y q → p = q := by
  classical
  let bad := (X ×ˢ X).image fun uv : (ℝ^2) × (ℝ^2) =>
    (uv.2 0 - uv.1 0) / (uv.1 1 - uv.2 1)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  let x : (ℝ^2) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 0 + t • EuclideanSpace.projₗ 1
  let y : (ℝ^2) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1
  have hjoint (p q : ℝ^2) (hx : x p = x q) (hy : y p = y q) : p = q := by
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 = q 1 at hy
    apply PiLp.ext
    intro i
    fin_cases i
    · change p 0 = q 0
      rw [hy] at hx
      exact add_right_cancel hx
    · exact hy
  refine ⟨x, y, ?_, hjoint⟩
  intro p hp q hq hx
  by_cases hy : y p = y q
  · exact hjoint p q hx hy
  · exfalso
    apply ht
    refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 ≠ q 1 at hy
    apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
    nlinarith only [hx]

noncomputable def OMA.planar_slope (x y : (ℝ^2) → ℝ) (p q : ℝ^2) : ℝ :=
  (y q - y p) / (x q - x p)

theorem OMA.planar_slope_ne (X : Finset (ℝ^2)) (hX : Erdos651.IsInGeneralPosition X)
    (x y : (ℝ^2) →ₗ[ℝ] ℝ) (hjoin : ∀ p q, x p = x q → y p = y q → p = q)
    {a b c : ℝ^2} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X)
    (hab : x a < x b) (hbc : x b < x c) :
    OMA.planar_slope x y a b ≠ OMA.planar_slope x y b c := by
  classical
  intro he
  let r := (x b - x a) / (x c - x b)
  have hxb : x b - x a = r * (x c - x b) := by
    dsimp [r]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hbc.ne')]
  have hyb : y b - y a = r * (y c - y b) := by
    have hex := (div_eq_div_iff (sub_ne_zero.mpr hab.ne') (sub_ne_zero.mpr hbc.ne')).mp he
    dsimp [r]
    rw [div_mul_eq_mul_div, eq_div_iff (sub_ne_zero.mpr hbc.ne')]
    exact hex.trans (mul_comm _ _)
  have hdiff : b - a = r • (c - b) := by
    apply hjoin
    · simpa only [map_sub, map_smul, smul_eq_mul] using hxb
    · simpa only [map_sub, map_smul, smul_eq_mul] using hyb
  have hcol : Collinear ℝ ({a, b, c} : Set (ℝ^2)) := by
    apply (collinear_iff_of_mem (show b ∈ ({a, b, c} : Set (ℝ^2)) by simp)).mpr
    refine ⟨c - b, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · refine ⟨-r, ?_⟩
      change _ = (-r) • (c - b) + b
      rw [neg_smul, ← hdiff]
      abel
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  let S : Finset (ℝ^2) := {a, b, c}
  have hSX : S ⊆ X := by
    intro p hp
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hnab : a ≠ b := fun h => hab.ne (congrArg x h)
  have hnac : a ≠ c := fun h => (hab.trans hbc).ne (congrArg x h)
  have hnbc : b ≠ c := fun h => hbc.ne (congrArg x h)
  let w : Fin 3 → (S : Set (ℝ^2)) :=
    ![⟨a, by simp [S]⟩, ⟨b, by simp [S]⟩, ⟨c, by simp [S]⟩]
  have hw : Function.Injective w := by
    intro i j hij
    have h := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [w, hnab, hnac, hnbc, hnab.symm, hnac.symm, hnbc.symm] at h ⊢
  have hind : AffineIndependent ℝ ![a, b, c] := by
    have h := (hX S hSX Finset.card_le_three).comp_embedding (⟨w, hw⟩ : Fin 3 ↪ S)
    convert h using 1
    ext i
    fin_cases i <;> rfl
  exact (affineIndependent_iff_not_collinear_set.mp hind) hcol

theorem OMA.planar_convex_of_increasing_slopes (Y : Finset (ℝ^2))
    (x y : (ℝ^2) →ₗ[ℝ] ℝ) (hinj : Set.InjOn x (Y : Set (ℝ^2)))
    (hslope : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, x a < x b → x b < x c →
      OMA.planar_slope x y a b < OMA.planar_slope x y b c) :
    ConvexIndependent ℝ (Subtype.val : ↥(Y : Set (ℝ^2)) → ℝ^2) := by
  classical
  have hsupport (p : ℝ^2) (hp : p ∈ Y) : ∃ L : (ℝ^2) →ₗ[ℝ] ℝ,
      ∀ q ∈ Y, q ≠ p → L p < L q := by
    let A := Y.filter fun q => x q < x p
    let B := Y.filter fun q => x p < x q
    by_cases hA : A.Nonempty
    · by_cases hB : B.Nonempty
      · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image A (fun a => OMA.planar_slope x y a p) hA
        obtain ⟨b, hb, hmin⟩ := Finset.exists_min_image B (OMA.planar_slope x y p) hB
        obtain ⟨haY, hap⟩ := Finset.mem_filter.mp ha
        obtain ⟨hbY, hpb⟩ := Finset.mem_filter.mp hb
        obtain ⟨s, h₁, h₂⟩ := exists_between (hslope a haY p hp b hbY hap hpb)
        refine ⟨y - s • x, fun q hq hqp => ?_⟩
        change y p - s * x p < y q - s * x q
        have hne : x q ≠ x p := fun h => hqp (hinj hq hp h)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hs := (hmax q (Finset.mem_filter.mpr ⟨hq, hlt⟩)).trans_lt h₁
          have hs' := (div_lt_iff₀ (sub_pos.mpr hlt)).mp hs
          linarith
        · have hs := h₂.trans_le (hmin q (Finset.mem_filter.mpr ⟨hq, hgt⟩))
          have hs' := (lt_div_iff₀ (sub_pos.mpr hgt)).mp hs
          linarith
      · refine ⟨-x, fun q hq hqp => ?_⟩
        change -x p < -x q
        have hne : x q ≠ x p := fun h => hqp (hinj hq hp h)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact neg_lt_neg hlt
        · exact (hB ⟨q, Finset.mem_filter.mpr ⟨hq, hgt⟩⟩).elim
    · refine ⟨x, fun q hq hqp => ?_⟩
      have hne : x q ≠ x p := fun h => hqp (hinj hq hp h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (hA ⟨q, Finset.mem_filter.mpr ⟨hq, hlt⟩⟩).elim
      · exact hgt
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
  intro p hp h
  obtain ⟨L, hL⟩ := hsupport p hp
  have hsub : (Y : Set (ℝ^2)) \ {p} ⊆ {q | L p < L q} :=
    fun q hq => hL q hq.1 hq.2
  have he := (convexHull_min hsub (convex_halfSpace_gt L.isLinear (L p))) h
  exact (lt_irrefl (L p)) he

theorem OMA.planar_cardSet_nonempty (n : ℕ) : (Erdos651.cardSet 2 n).Nonempty := by
  classical
  obtain ⟨N, hN⟩ := OMA.finite_ramsey_sets (ℝ^2) 3 n
  refine ⟨N, fun X hX hNX => ?_⟩
  obtain ⟨x, y, hx, hjoin⟩ := OMA.planar_coordinates X
  let color (A : Finset (ℝ^2)) : Bool := decide
    (∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, x a < x b ∧ x b < x c ∧
      OMA.planar_slope x y a b < OMA.planar_slope x y b c)
  obtain ⟨Y, hYX, hcard, col, hcol⟩ := hN X hNX color
  refine ⟨Y, hYX, hcard, ?_⟩
  have hY (a : ℝ^2) (ha : a ∈ Y) (b : ℝ^2) (hb : b ∈ Y) (c : ℝ^2) (hc : c ∈ Y)
      (hab : x a < x b) (hbc : x b < x c) :
      (OMA.planar_slope x y a b < OMA.planar_slope x y b c) ↔ col = true := by
    let A : Finset (ℝ^2) := {a, b, c}
    have hAY : A ⊆ Y := by
      intro p hp
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    have hAcard : A.card = 3 := Finset.card_triple_eq_three_iff.mpr
      ⟨fun h => hab.ne (congrArg x h), fun h => (hab.trans hbc).ne (congrArg x h),
        fun h => hbc.ne (congrArg x h)⟩
    rw [← hcol A hAY hAcard]
    change _ ↔ decide _ = true
    rw [decide_eq_true_eq]
    constructor
    · exact fun hs => ⟨a, by simp [A], b, by simp [A], c, by simp [A], hab, hbc, hs⟩
    · rintro ⟨a', ha', b', hb', c', hc', hab', hbc', hs'⟩
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at ha' hb' hc'
      have heq : a' = a ∧ b' = b ∧ c' = c := by
        rcases ha' with rfl | rfl | rfl <;>
          rcases hb' with rfl | rfl | rfl <;>
          rcases hc' with rfl | rfl | rfl <;> grind
      rcases heq with ⟨rfl, rfl, rfl⟩
      exact hs'
  cases h : col with
  | true =>
    exact OMA.planar_convex_of_increasing_slopes Y x y (hx.mono hYX)
      (fun a ha b hb c hc hab hbc => (hY a ha b hb c hc hab hbc).mpr h)
  | false =>
    apply OMA.planar_convex_of_increasing_slopes Y x (-y) (hx.mono hYX)
    intro a ha b hb c hc hab hbc
    have hnot : ¬OMA.planar_slope x y a b < OMA.planar_slope x y b c := by
      rw [hY a ha b hb c hc hab hbc, h]
      decide
    have hne := OMA.planar_slope_ne X hX x y hjoin (hYX ha) (hYX hb) (hYX hc) hab hbc
    have hgt := lt_of_le_of_ne (le_of_not_gt hnot) hne.symm
    have hflip (u v : ℝ^2) : OMA.planar_slope x (-y) u v = -OMA.planar_slope x y u v := by
      change (-y v - -y u) / (x v - x u) = -((y v - y u) / (x v - x u))
      rw [show -y v - -y u = -(y v - y u) by ring, neg_div]
    calc
      OMA.planar_slope x (-y) a b = -OMA.planar_slope x y a b := hflip a b
      _ < -OMA.planar_slope x y b c := neg_lt_neg hgt
      _ = OMA.planar_slope x (-y) b c := (hflip b c).symm



theorem OMA.planar_lower_of_construction
    (build : ∀ m : ℕ, ∃ X : Finset (ℝ^2), X.card = 2 ^ m ∧
      Erdos651.IsInGeneralPosition X ∧
      ∀ n : ℕ, Erdos651.HasConvexSubset n X → n ≤ 2 * m + 4)
    (nonempty : ∀ n : ℕ, (Erdos651.cardSet 2 n).Nonempty) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (1 + c) ^ n < (Erdos651.f 2 n : ℝ) := by
  refine ⟨1 / 10, by norm_num, eventually_atTop.2 ⟨21, ?_⟩⟩
  intro n hn
  let m := (n - 5) / 2
  have hlen : 2 * m + 4 < n := by dsimp [m]; omega
  have hpow : n ≤ 3 * m := by dsimp [m]; omega
  obtain ⟨X, hcard, hpos, hconv⟩ := build m
  have hfmem : Erdos651.f 2 n ∈ Erdos651.cardSet 2 n := Nat.sInf_mem (nonempty n)
  have hlt : 2 ^ m < Erdos651.f 2 n := by
    by_contra! h
    exact (not_le_of_gt hlen) (hconv n (hfmem X hpos (h.trans_eq hcard.symm)))
  calc
    (1 + (1 / 10 : ℝ)) ^ n ≤ (1 + 1 / 10) ^ (3 * m) :=
      pow_le_pow_right₀ (by norm_num) hpow
    _ = ((1 + 1 / 10 : ℝ) ^ 3) ^ m := pow_mul _ _ _
    _ ≤ (2 : ℝ) ^ m := pow_le_pow_left₀ (by positivity) (by norm_num) _
    _ < (Erdos651.f 2 n : ℝ) := by exact_mod_cast hlt

theorem OMA.solution : type_of% @Erdos651.erdos_651.variants.planar := by
  apply OMA.planar_lower_of_construction _ OMA.planar_cardSet_nonempty
  intro m
  obtain ⟨X, hX, hG, hC⟩ := PlanarSzekeres.witness m
  exact ⟨X, hX, hG, fun n hn => (hC n hn).trans (by omega)⟩