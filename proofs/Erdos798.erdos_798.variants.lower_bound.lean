import FormalConjectures.ErdosProblems.«798»
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat

/-!
The Erdős–Purdy lower bound for covering a square grid by lines determined
by a set of grid points. This bound is recorded in the introduction to Alon's
[Economical coverings of sets of lattice points](https://web.math.princeton.edu/~nalon/PDFS/lattice.pdf).
-/

open Finset
open scoped Classical

private abbrev Point := ℕ × ℕ

private def grid (n : ℕ) : Finset Point := (Icc 1 n).product (Icc 1 n)

private def embed (p : Point) : ℝ × ℝ := (p.1, p.2)

private theorem embed_inj : Function.Injective embed := by
  intro p q h
  have h₁ : (p.1 : ℝ) = q.1 := congrArg Prod.fst h
  have h₂ : (p.2 : ℝ) = q.2 := congrArg Prod.snd h
  exact Prod.ext (by exact_mod_cast h₁) (by exact_mod_cast h₂)

private theorem image_grid (n : ℕ) : embed '' (grid n : Set Point) = Erdos798.gridPoints n := by
  ext x
  change (∃ p : Point, p ∈ grid n ∧ embed p = x) ↔
    ∃ i j : ℕ, 1 ≤ i ∧ i ≤ n ∧ 1 ≤ j ∧ j ≤ n ∧ x = ((i : ℝ), (j : ℝ))
  constructor
  · rintro ⟨⟨i, j⟩, hp, rfl⟩
    obtain ⟨hi, hj⟩ := mem_product.mp (show (i, j) ∈ (Icc 1 n).product (Icc 1 n) from hp)
    exact ⟨i, j, (mem_Icc.mp hi).1, (mem_Icc.mp hi).2, (mem_Icc.mp hj).1,
      (mem_Icc.mp hj).2, rfl⟩
  · rintro ⟨i, j, hi, hi', hj, hj', rfl⟩
    exact ⟨(i, j), mem_product.mpr ⟨mem_Icc.mpr ⟨hi, hi'⟩, mem_Icc.mpr ⟨hj, hj'⟩⟩, rfl⟩

private theorem card_grid (n : ℕ) : (grid n).card = n ^ 2 := by
  simp [grid, Nat.card_Icc, pow_two]

private def delta (p q : Point) : ℤ × ℤ :=
  ((q.1 : ℤ) - (p.1 : ℤ), (q.2 : ℤ) - (p.2 : ℤ))

private def height (d : ℤ × ℤ) : ℕ := max d.1.natAbs d.2.natAbs

private def offset (d : ℤ × ℤ) (p : Point) : ℤ :=
  d.1 * (p.2 : ℤ) - d.2 * (p.1 : ℤ)

private def line (n : ℕ) (d : ℤ × ℤ) (b : ℤ) : Finset Point :=
  (grid n).filter fun p => offset d p = b

private theorem delta_ne_zero {p q : Point} (h : p ≠ q) : delta p q ≠ (0, 0) := by
  intro e
  have e₁ := congrArg Prod.fst e
  have e₂ := congrArg Prod.snd e
  dsimp [delta] at e₁ e₂
  exact h (Prod.ext (by omega) (by omega))

private theorem height_pos {d : ℤ × ℤ} (hd : d ≠ (0, 0)) : 0 < height d := by
  by_contra! h
  have h₁ : d.1.natAbs = 0 := by
    have h₁ := le_max_left d.1.natAbs d.2.natAbs
    unfold height at h
    omega
  have h₂ : d.2.natAbs = 0 := by
    have h₂ := le_max_right d.1.natAbs d.2.natAbs
    unfold height at h
    omega
  exact hd (Prod.ext (Int.natAbs_eq_zero.mp h₁) (Int.natAbs_eq_zero.mp h₂))

private theorem collinear_offset {p q x : Point}
    (h : Collinear ℝ ({embed p, embed q, embed x} : Set (ℝ × ℝ))) :
    offset (delta p q) x = offset (delta p q) p := by
  obtain ⟨a, v, hf⟩ := (collinear_iff_exists_forall_eq_smul_vadd (k := ℝ) _).mp h
  obtain ⟨r, hp⟩ := hf (embed p) (by simp)
  obtain ⟨s, hq⟩ := hf (embed q) (by simp)
  obtain ⟨t, hx⟩ := hf (embed x) (by simp)
  have hp₁ := congrArg Prod.fst hp
  have hp₂ := congrArg Prod.snd hp
  have hq₁ := congrArg Prod.fst hq
  have hq₂ := congrArg Prod.snd hq
  have hx₁ := congrArg Prod.fst hx
  have hx₂ := congrArg Prod.snd hx
  change (p.1 : ℝ) = r * v.1 + a.1 at hp₁
  change (p.2 : ℝ) = r * v.2 + a.2 at hp₂
  change (q.1 : ℝ) = s * v.1 + a.1 at hq₁
  change (q.2 : ℝ) = s * v.2 + a.2 at hq₂
  change (x.1 : ℝ) = t * v.1 + a.1 at hx₁
  change (x.2 : ℝ) = t * v.2 + a.2 at hx₂
  have hr :
      ((q.1 : ℝ) - p.1) * (x.2 : ℝ) - ((q.2 : ℝ) - p.2) * (x.1 : ℝ) =
        ((q.1 : ℝ) - p.1) * (p.2 : ℝ) - ((q.2 : ℝ) - p.2) * (p.1 : ℝ) := by
    rw [hp₁, hp₂, hq₁, hq₂, hx₁, hx₂]
    ring
  unfold offset delta
  exact_mod_cast hr

private theorem offset_iff {d : ℤ × ℤ} {p q : Point} :
    offset d p = offset d q ↔ d.1 * (delta p q).2 = d.2 * (delta p q).1 := by
  dsimp [offset, delta]
  constructor <;> intro h <;> nlinarith only [h]

private theorem kernel_transfer {d e z : ℤ × ℤ} (hd : d ≠ (0, 0))
    (he : d.1 * e.2 = d.2 * e.1) (hz : d.1 * z.2 = d.2 * z.1) :
    e.1 * z.2 = e.2 * z.1 := by
  by_cases h : d.1 = 0
  · have h₂ : d.2 ≠ 0 := fun h₂ => hd (Prod.ext h h₂)
    have hmul : d.2 * (e.1 * z.2 - e.2 * z.1) = 0 := by
      linear_combination e.2 * hz - z.2 * he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left h₂)
  · have hmul : d.1 * (e.1 * z.2 - e.2 * z.1) = 0 := by
      linear_combination e.1 * hz - z.1 * he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left h)

private theorem line_relabel {n : ℕ} {d : ℤ × ℤ} {b : ℤ} {p q : Point} (hd : d ≠ (0, 0))
    (hp : p ∈ line n d b) (hq : q ∈ line n d b) (hne : p ≠ q) :
    line n d b = line n (delta p q) (offset (delta p q) p) := by
  have hp' := (mem_filter.mp hp).2
  have hq' := (mem_filter.mp hq).2
  have h₁ := offset_iff.mp (hp'.trans hq'.symm)
  have h₂ : (delta p q).1 * d.2 = (delta p q).2 * d.1 := by nlinarith only [h₁]
  ext x
  simp only [line, mem_filter]
  constructor
  · rintro ⟨hx, hxb⟩
    have hpx := offset_iff.mp (hp'.trans hxb.symm)
    exact ⟨hx, (offset_iff.mpr (kernel_transfer hd h₁ hpx)).symm⟩
  · rintro ⟨hx, hxb⟩
    have hpx := offset_iff.mp hxb.symm
    exact ⟨hx, (offset_iff.mpr (kernel_transfer (delta_ne_zero hne) h₂ hpx)).symm.trans hp'⟩

private def dominant (d : ℤ × ℤ) (p : Point) : ℕ :=
  if d.2.natAbs ≤ d.1.natAbs then p.1 else p.2

private theorem height_dominant {d : ℤ × ℤ} {p q : Point} (hd : d ≠ (0, 0))
    (h : offset d p = offset d q) :
    height (delta p q) = ((dominant d q : ℤ) - (dominant d p : ℤ)).natAbs := by
  have he := congrArg Int.natAbs (offset_iff.mp h)
  simp only [Int.natAbs_mul] at he
  unfold dominant
  split
  · rename_i hle
    have hne : 0 < d.1.natAbs := by
      by_contra! h
      have h₁ := Int.natAbs_eq_zero.mp (show d.1.natAbs = 0 by omega)
      have h₂ := Int.natAbs_eq_zero.mp (show d.2.natAbs = 0 by omega)
      exact hd (Prod.ext h₁ h₂)
    have hh : (delta p q).2.natAbs ≤ (delta p q).1.natAbs := by
      apply Nat.le_of_mul_le_mul_left _ hne
      rw [he]
      exact Nat.mul_le_mul_right _ hle
    exact max_eq_left hh
  · rename_i hle
    have hle' : d.1.natAbs ≤ d.2.natAbs := by omega
    have hne : 0 < d.2.natAbs := by omega
    have hh : (delta p q).1.natAbs ≤ (delta p q).2.natAbs := by
      apply Nat.le_of_mul_le_mul_left _ hne
      rw [← he]
      exact Nat.mul_le_mul_right _ hle'
    exact max_eq_right hh

private theorem line_card_le {n H : ℕ} {d : ℤ × ℤ} {b : ℤ} (hd : d ≠ (0, 0))
    (hH : 0 < H)
    (hspace : ∀ p ∈ line n d b, ∀ q ∈ line n d b, p ≠ q → H ≤ height (delta p q)) :
    (line n d b).card ≤ n / H + 1 := by
  let f (p : Point) := dominant d p / H
  have hmaps : Set.MapsTo f (line n d b : Set Point) (range (n / H + 1) : Set ℕ) := by
    intro p hp
    have hp' : p ∈ grid n := (mem_filter.mp hp).1
    obtain ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ := mem_product.mp hp' |>.imp mem_Icc.mp mem_Icc.mp
    have hh : dominant d p ≤ n := by unfold dominant; split <;> assumption
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hh))
  have hinj : (line n d b : Set Point).InjOn f := by
    intro p hp q hq he
    by_contra hne
    have ha := Nat.div_add_mod (dominant d p) H
    have hb := Nat.div_add_mod (dominant d q) H
    have hpa := Nat.mod_lt (dominant d p) hH
    have hqa := Nat.mod_lt (dominant d q) hH
    change dominant d p / H = dominant d q / H at he
    rw [he] at ha
    have hdiff : ((dominant d q : ℤ) - (dominant d p : ℤ)).natAbs < H := by
      rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs, abs_lt]
      constructor <;> omega
    have hparallel := (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
    have hdom := height_dominant hd hparallel
    exact (not_lt_of_ge (hspace p hp q hq hne)) (hdom ▸ hdiff)
  simpa only [card_range] using card_le_card_of_injOn f hmaps hinj

private def directionInterval (h : ℕ) : Finset ℤ := Icc (-(h : ℤ)) (h : ℤ)

private def shell (h : ℕ) : Finset (ℤ × ℤ) :=
  ((directionInterval h).product (directionInterval h)).filter fun d => height d = h

private theorem mem_box_of_natAbs_le {h : ℕ} {z : ℤ} (hz : z.natAbs ≤ h) : z ∈ directionInterval h := by
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, abs_le] at hz
  exact mem_Icc.mpr hz

private theorem mem_shell_of_height {h : ℕ} {d : ℤ × ℤ} (hh : height d = h) : d ∈ shell h := by
  have h₁ : d.1.natAbs ≤ h := (le_max_left _ _).trans_eq hh
  have h₂ : d.2.natAbs ≤ h := (le_max_right _ _).trans_eq hh
  exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_box_of_natAbs_le h₁, mem_box_of_natAbs_le h₂⟩, hh⟩

private theorem shell_card (h : ℕ) (hh : 0 < h) : (shell h).card ≤ 12 * h := by
  let ends : Finset ℤ := {-(h : ℤ), (h : ℤ)}
  have hmem (z : ℤ) (hz : z.natAbs = h) : z ∈ ends := by
    have habs : |z| = (h : ℤ) := by rw [← Int.natCast_natAbs, hz]
    by_cases hz0 : 0 ≤ z
    · have he : z = h := by simpa only [abs_of_nonneg hz0] using habs
      simp [ends, he]
    · have he : z = -(h : ℤ) := by rw [abs_of_neg (lt_of_not_ge hz0)] at habs; omega
      simp [ends, he]
  have hsub : shell h ⊆ ends.product (directionInterval h) ∪ (directionInterval h).product ends := by
    intro d hd
    obtain ⟨hd, hdH⟩ := mem_filter.mp hd
    obtain ⟨ha, hb⟩ := mem_product.mp hd
    by_cases hle : d.2.natAbs ≤ d.1.natAbs
    · have he : d.1.natAbs = h := (max_eq_left hle).symm.trans hdH
      exact mem_union.mpr (.inl (mem_product.mpr ⟨hmem _ he, hb⟩))
    · have he : d.2.natAbs = h := (max_eq_right (by omega)).symm.trans hdH
      exact mem_union.mpr (.inr (mem_product.mpr ⟨ha, hmem _ he⟩))
  have hend : ends.card ≤ 2 := card_le_two
  have hbox : (directionInterval h).card = 2 * h + 1 := by
    rw [directionInterval, Int.card_Icc]
    omega
  calc
    _ ≤ (ends.product (directionInterval h) ∪ (directionInterval h).product ends).card := card_le_card hsub
    _ ≤ (ends.product (directionInterval h)).card + ((directionInterval h).product ends).card := card_union_le _ _
    _ ≤ 2 * (2 * h + 1) + (2 * h + 1) * 2 := by
      have ha : (ends.product (directionInterval h)).card = ends.card * (directionInterval h).card :=
        Finset.card_product _ _
      have hb : ((directionInterval h).product ends).card = (directionInterval h).card * ends.card :=
        Finset.card_product _ _
      rw [ha, hb, hbox]
      exact Nat.add_le_add (Nat.mul_le_mul_right _ hend) (Nat.mul_le_mul_left _ hend)
    _ ≤ _ := by omega

private def IsSpaced (n H : ℕ) (d : ℤ × ℤ) (b : ℤ) : Prop :=
  ∀ p ∈ line n d b, ∀ q ∈ line n d b, p ≠ q → H ≤ height (delta p q)

private noncomputable def packet (n H : ℕ) (d : ℤ × ℤ) (b : ℤ) : Finset Point :=
  if d ≠ (0, 0) ∧ IsSpaced n H d b then line n d b else ∅

private theorem packet_card (n H : ℕ) (hH : 0 < H) (d : ℤ × ℤ) (b : ℤ) :
    (packet n H d b).card ≤ n / H + 1 := by
  unfold packet
  split
  · rename_i h
    exact line_card_le h.1 hH h.2
  · simp

private noncomputable def shortUnion (n h : ℕ) (A : Finset Point) : Finset Point :=
  (shell h).biUnion fun d => (A.image (offset d)).biUnion (packet n h d)

private noncomputable def tallUnion (n R : ℕ) (A : Finset Point) : Finset Point :=
  (A.product A).biUnion fun p =>
    packet n (R + 1) (delta p.1 p.2) (offset (delta p.1 p.2) p.1)

private theorem card_shortUnion (n h : ℕ) (A : Finset Point) (hh : 0 < h) (hn : h ≤ n) :
    (shortUnion n h A).card ≤ 24 * n * A.card := by
  have hpack (d : ℤ × ℤ) :
      ((A.image (offset d)).biUnion (packet n h d)).card ≤ A.card * (n / h + 1) := by
    calc
      _ ≤ ∑ b ∈ A.image (offset d), (packet n h d b).card := card_biUnion_le
      _ ≤ ∑ _ ∈ A.image (offset d), (n / h + 1) :=
        sum_le_sum (fun b _ => packet_card n h hh d b)
      _ = (A.image (offset d)).card * (n / h + 1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ card_image_le
  have hhdiv : h * (n / h) ≤ n := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  calc
    _ ≤ ∑ d ∈ shell h, ((A.image (offset d)).biUnion (packet n h d)).card := card_biUnion_le
    _ ≤ ∑ _ ∈ shell h, A.card * (n / h + 1) := sum_le_sum (fun d _ => hpack d)
    _ = (shell h).card * (A.card * (n / h + 1)) := by simp
    _ ≤ (12 * h) * (A.card * (n / h + 1)) := Nat.mul_le_mul_right _ (shell_card h hh)
    _ = (12 * A.card) * (h * (n / h) + h) := by ring
    _ ≤ (12 * A.card) * (n + n) := Nat.mul_le_mul_left _ (Nat.add_le_add hhdiv hn)
    _ = 24 * n * A.card := by ring

private theorem card_all_short (n R : ℕ) (A : Finset Point) (hn : R ≤ n) :
    ((Icc 1 R).biUnion (fun h => shortUnion n h A)).card ≤ 24 * n * A.card * R := by
  calc
    _ ≤ ∑ h ∈ Icc 1 R, (shortUnion n h A).card := card_biUnion_le
    _ ≤ ∑ _ ∈ Icc 1 R, 24 * n * A.card := by
      apply sum_le_sum
      intro h hh
      obtain ⟨h₀, hR⟩ := mem_Icc.mp hh
      exact card_shortUnion n h A h₀ (hR.trans hn)
    _ = _ := by simp [Nat.card_Icc, Nat.mul_comm]

private theorem card_tall (n R : ℕ) (A : Finset Point) :
    (tallUnion n R A).card ≤ A.card ^ 2 * (n / (R + 1) + 1) := by
  calc
    _ ≤ ∑ p ∈ A.product A, (packet n (R + 1) (delta p.1 p.2) (offset (delta p.1 p.2) p.1)).card :=
      card_biUnion_le
    _ ≤ ∑ _ ∈ A.product A, (n / (R + 1) + 1) := by
      apply sum_le_sum
      intro p _
      exact packet_card n (R + 1) (by omega) _ _
    _ = _ := by simp [pow_two]

private theorem line_cover_bound (n R : ℕ) (A : Finset Point) (hR : R ≤ n)
    (hA : A ⊆ grid n)
    (hCover : ∀ x ∈ grid n, ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧
      offset (delta p q) x = offset (delta p q) p) :
    n ^ 2 ≤ 24 * n * A.card * R + A.card ^ 2 * (n / (R + 1) + 1) := by
  let small := (Icc 1 R).biUnion (fun h => shortUnion n h A)
  let tall := tallUnion n R A
  have hsubset : grid n ⊆ small ∪ tall := by
    intro x hx
    obtain ⟨p, hp, q, hq, hpq, hl⟩ := hCover x hx
    let d := delta p q
    let b := offset d p
    let L := line n d b
    have hd : d ≠ (0, 0) := delta_ne_zero hpq
    have hpL : p ∈ L := mem_filter.mpr ⟨hA hp, rfl⟩
    have hqL : q ∈ L := by
      refine mem_filter.mpr ⟨hA hq, ?_⟩
      exact (offset_iff.mpr (mul_comm d.1 d.2)).symm
    have hxL : x ∈ L := mem_filter.mpr ⟨hx, hl⟩
    let Good (h : ℕ) := ∃ a ∈ L, ∃ c ∈ L, a ≠ c ∧ height (delta a c) = h
    have hex : ∃ h, Good h := ⟨height d, p, hpL, q, hqL, hpq, rfl⟩
    let h := Nat.find hex
    obtain ⟨a, ha, c, hc, hac, hh⟩ := Nat.find_spec hex
    have hhMin : IsSpaced n h d b := by
      intro y hy z hz hyz
      exact Nat.find_min' hex (show Good (height (delta y z)) from ⟨y, hy, z, hz, hyz, rfl⟩)
    by_cases hsmall : h ≤ R
    · let e := delta a c
      let b' := offset e a
      have he : e ≠ (0, 0) := delta_ne_zero hac
      have hpos : 0 < h := (height_pos he).trans_eq hh
      have hrel : L = line n e b' := line_relabel hd ha hc hac
      have hpNew : p ∈ line n e b' := hrel ▸ hpL
      have hb' : b' ∈ A.image (offset e) := mem_image.mpr ⟨p, hp, (mem_filter.mp hpNew).2⟩
      have hs : IsSpaced n h e b' := by
        have heq : line n e b' = line n d b := hrel.symm
        simpa only [IsSpaced, heq] using hhMin
      have hxNew : x ∈ packet n h e b' := by
        rw [packet, if_pos ⟨he, hs⟩]
        exact hrel ▸ hxL
      refine mem_union.mpr (.inl (mem_biUnion.mpr ⟨h, mem_Icc.mpr ⟨hpos, hsmall⟩, ?_⟩))
      exact mem_biUnion.mpr ⟨e, mem_shell_of_height hh, mem_biUnion.mpr ⟨b', hb', hxNew⟩⟩
    · have hs : IsSpaced n (R + 1) d b := by
        intro y hy z hz hyz
        exact (show R + 1 ≤ h by omega).trans (hhMin y hy z hz hyz)
      have hxNew : x ∈ packet n (R + 1) d b := by
        rw [packet, if_pos ⟨hd, hs⟩]
        exact hxL
      exact mem_union.mpr (.inr (mem_biUnion.mpr ⟨(p, q), mem_product.mpr ⟨hp, hq⟩, hxNew⟩))
  calc
    n ^ 2 = (grid n).card := (card_grid n).symm
    _ ≤ (small ∪ tall).card := card_le_card hsubset
    _ ≤ small.card + tall.card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add (card_all_short n R A hR) (card_tall n R A)

private theorem OMA.gridCountLower {n t : ℕ} (hn : 1 ≤ n)
    (hcount : n ^ 2 ≤ 24 * n * t * t.sqrt + t ^ 2 * (n / (t.sqrt + 1) + 1)) :
    (n : ℝ) ^ (2 / 3 : ℝ) ≤ 26 * (t : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hnt : n ≤ t
  · have hpow : (n : ℝ) ^ (2 / 3 : ℝ) ≤ n := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (2 / 3 : ℝ) ≤ 1)
    exact hpow.trans ((Nat.cast_le.mpr hnt).trans (by linarith [show 0 ≤ (t : ℝ) by positivity]))
  have ht : 1 ≤ t := by
    by_contra! h
    have hz : t = 0 := by omega
    simp [hz, show n ≠ 0 by omega] at hcount
  let s := Real.sqrt (t : ℝ)
  have hs : 1 ≤ s := by
    change 1 ≤ Real.sqrt (t : ℝ)
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ t by exact_mod_cast ht)
  have hss : s ^ 2 = (t : ℝ) := Real.sq_sqrt (by positivity)
  have hsl : (t.sqrt : ℝ) ≤ s := Real.nat_sqrt_le_real_sqrt
  have hsr : s ≤ (t.sqrt : ℝ) + 1 := by
    have hsq : (t : ℝ) < ((t.sqrt : ℝ) + 1) ^ 2 := by
      exact_mod_cast Nat.lt_succ_sqrt' t
    calc
      _ ≤ Real.sqrt (((t.sqrt : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt hsq.le
      _ = _ := Real.sqrt_sq (by positivity)
  have hdiv : ((n / (t.sqrt + 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((t.sqrt : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (t.sqrt : ℝ) + 1)).2
    exact_mod_cast Nat.div_mul_le_self n (t.sqrt + 1)
  have hscale : (t : ℝ) ^ 2 * ((n : ℝ) / ((t.sqrt : ℝ) + 1)) ≤ (n : ℝ) * t * s := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (t.sqrt : ℝ) + 1)).2
    calc
      _ = ((n : ℝ) * t * s) * s := by
        calc
          _ = (n : ℝ) * t * (t : ℝ) := by ring
          _ = _ := by rw [← hss]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsr (by positivity)
  have htR : (t : ℝ) ≤ n := by exact_mod_cast le_of_not_ge hnt
  have htsq : (t : ℝ) ^ 2 ≤ (n : ℝ) * t * s := by
    calc
      _ ≤ (n : ℝ) * t := by rw [sq]; gcongr
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hs
  have hcountR : (n : ℝ) ^ 2 ≤ 24 * n * t * (t.sqrt : ℝ) +
      (t : ℝ) ^ 2 * (((n / (t.sqrt + 1) : ℕ) : ℝ) + 1) := by exact_mod_cast hcount
  have htot : (n : ℝ) ^ 2 ≤ 26 * (n : ℝ) * t * s := by
    have hfirst := mul_le_mul_of_nonneg_left hsl (by positivity : 0 ≤ 24 * (n : ℝ) * t)
    have hsecond := mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ (t : ℝ) ^ 2)
    nlinarith only [hcountR, hfirst, hsecond, hscale, htsq]
  have hle : (n : ℝ) ≤ 26 * t * s := by
    have hnPos : (0 : ℝ) < n := by linarith
    apply (mul_le_mul_iff_right₀ hnPos).mp
    calc
      _ = (n : ℝ) ^ 2 := by ring
      _ ≤ 26 * (n : ℝ) * t * s := htot
      _ = _ := by ring
  have htPos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hsPow : (26 * t * s : ℝ) ^ (2 / 3 : ℝ) = (26 : ℝ) ^ (2 / 3 : ℝ) * t := by
    have heq : (t : ℝ) * s = (t : ℝ) ^ (3 / 2 : ℝ) := by
      change (t : ℝ) * Real.sqrt (t : ℝ) = _
      rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add htPos, Real.rpow_one]
    rw [mul_assoc, heq, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 26) (by positivity),
      ← Real.rpow_mul htPos.le]
    norm_num
  calc
    _ ≤ (26 * t * s : ℝ) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hle (by norm_num)
    _ = (26 : ℝ) ^ (2 / 3 : ℝ) * t := hsPow
    _ ≤ 26 * t := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 26)
          (by norm_num : (2 / 3 : ℝ) ≤ 1)

private theorem grid_cover_exists (n : ℕ) (hn : 2 ≤ n) :
    Erdos798.IsLineCover n (Erdos798.gridPoints n) := by
  have ha : embed (1, 1) ∈ Erdos798.gridPoints n := ⟨1, 1, by omega, by omega, by omega, by omega, rfl⟩
  have hb : embed (1, 2) ∈ Erdos798.gridPoints n := ⟨1, 2, by omega, by omega, by omega, hn, rfl⟩
  refine ⟨Set.Subset.rfl, ?_⟩
  intro x hx
  have hh (q : ℝ × ℝ) : Collinear ℝ ({x, q, x} : Set (ℝ × ℝ)) := by
    have he : ({x, q, x} : Set (ℝ × ℝ)) = {x, q} := by
      ext a
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [he]
    exact collinear_pair ℝ x q
  by_cases h : x = embed (1, 1)
  · refine ⟨x, hx, embed (1, 2), hb, ?_, hh _⟩
    rw [h]
    intro he
    have hh := embed_inj he
    exact (by decide : ((1, 1) : Point) ≠ (1, 2)) hh
  · exact ⟨x, hx, embed (1, 1), ha, h, hh _⟩

private theorem finite_cover_lower (n : ℕ) (hn : 1 ≤ n) (S : Set (ℝ × ℝ))
    (hS : Erdos798.IsLineCover n S) : (n : ℝ) ^ (2 / 3 : ℝ) ≤ 26 * (S.ncard : ℝ) := by
  let A := (grid n).filter (fun p => embed p ∈ S)
  have hA : A ⊆ grid n := filter_subset _ _
  have hImage : embed '' (A : Set Point) = S := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (mem_filter.mp hp).2
    · intro hx
      have hx' : x ∈ embed '' (grid n : Set Point) := by rw [image_grid]; exact hS.1 hx
      obtain ⟨p, hp, rfl⟩ := hx'
      exact ⟨p, mem_filter.mpr ⟨hp, hx⟩, rfl⟩
  have hAcard : A.card = S.ncard := by
    rw [← hImage, Set.ncard_image_of_injective _ embed_inj, Set.ncard_coe_finset]
  have hCover : ∀ x ∈ grid n, ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧
      offset (delta p q) x = offset (delta p q) p := by
    intro x hx
    have hx' : embed x ∈ Erdos798.gridPoints n := by
      rw [← image_grid]
      exact ⟨x, hx, rfl⟩
    obtain ⟨p, hp, q, hq, hpq, hcol⟩ := hS.2 (embed x) hx'
    rw [← hImage] at hp hq
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨q', hq', rfl⟩ := hq
    exact ⟨p', hp', q', hq', fun he => hpq (congrArg embed he), collinear_offset hcol⟩
  have hR : A.card.sqrt ≤ n := by
    have hbound := (card_le_card hA).trans_eq (card_grid n)
    exact Nat.lt_succ_iff.mp (Nat.sqrt_lt'.mpr (by nlinarith [Nat.zero_le n]))
  have hcount := line_cover_bound n A.card.sqrt A hR hA hCover
  simpa only [hAcard] using (OMA.gridCountLower hn hcount)

theorem OMA.solution : type_of% @Erdos798.erdos_798.variants.lower_bound := by
  apply Asymptotics.IsBigO.of_bound 26
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
  have hne : {k | ∃ S : Set (ℝ × ℝ), Erdos798.IsLineCover n S ∧ S.ncard = k}.Nonempty :=
    ⟨_, Erdos798.gridPoints n, grid_cover_exists n hn, rfl⟩
  have ht := Nat.sInf_mem hne
  change ∃ S : Set (ℝ × ℝ), Erdos798.IsLineCover n S ∧ S.ncard = Erdos798.t n at ht
  obtain ⟨S, hS, hcard⟩ := ht
  have h := finite_cover_lower n (by omega) S hS
  rw [hcard] at h
  have hn₀ : 0 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have ht₀ : (0 : ℝ) ≤ (Erdos798.t n : ℝ) := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn₀, abs_of_nonneg ht₀] using h