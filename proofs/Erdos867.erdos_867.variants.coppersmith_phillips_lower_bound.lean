import FormalConjectures.ErdosProblems.«867»

/-! The 13/24 lower bound for consecutive-sum-free sets.

The residue classes are those in Table 1 of Coppersmith and Phillips,
*On a Question of Erdös on Subsequence Sums*.
-/

open Finset

namespace CoppersmithPhillips

private structure Band where
  lo : ℕ
  hi : ℕ
  period : ℕ
  residues : Finset ℕ

-- The scale 207360 makes every endpoint integral and every width a multiple of its period.
private def band : Fin 12 → Band := ![
  ⟨41472, 46080, 16, {0, 1, 2, 5, 6, 8, 10, 11, 14, 15}⟩,
  ⟨46080, 51840, 1, {0}⟩,
  ⟨51840, 61440, 1, ∅⟩,
  ⟨61440, 69120, 4, {1, 2, 3}⟩,
  ⟨69120, 77760, 3, {1, 2}⟩,
  ⟨77760, 92160, 32, {0, 2, 6, 8, 9, 12, 13, 16, 19, 20, 23, 24, 26, 30}⟩,
  ⟨92160, 103680, 2, {0}⟩,
  ⟨103680, 122880, 1, {0}⟩,
  ⟨122880, 138240, 8, {1, 2, 4, 6, 7}⟩,
  ⟨138240, 155520, 3, {1, 2}⟩,
  ⟨155520, 184320, 64, range 64 \ {2, 8, 14, 17, 21, 25, 29, 35, 39, 43, 47, 50, 56, 62}⟩,
  ⟨184320, 207360, 4, {0, 1, 3}⟩]

private def Band.accepts (B : Band) (x : ℕ) : Prop :=
  x % B.period ∈ B.residues

instance (B : Band) : DecidablePred B.accepts := fun x =>
  inferInstanceAs (Decidable (x % B.period ∈ B.residues))

private def Band.points (B : Band) (k : ℕ) : Finset ℕ :=
  (Ico (B.lo * k) (B.hi * k)).filter B.accepts

private def base (k : ℕ) : Finset ℕ :=
  (univ : Finset (Fin 12)).biUnion fun i => (band i).points k

private theorem mem_points {B : Band} {k x : ℕ} :
    x ∈ B.points k ↔ B.lo * k ≤ x ∧ x < B.hi * k ∧ B.accepts x := by
  simp only [Band.points, mem_filter, mem_Ico]
  tauto

private theorem mem_base {k x : ℕ} :
    x ∈ base k ↔ ∃ i : Fin 12, (band i).lo * k ≤ x ∧ x < (band i).hi * k ∧ (band i).accepts x := by
  simp [base, mem_points]

private theorem row_bounds (i : Fin 12) :
    41472 ≤ (band i).lo ∧ (band i).lo ≤ (band i).hi ∧
      (band i).hi ≤ 207360 ∧ 0 < (band i).period ∧
      (band i).period ∣ (band i).hi - (band i).lo := by
  fin_cases i <;> decide

private theorem rows_ordered : ∀ i j : Fin 12, i < j → (band i).hi ≤ (band j).lo := by
  decide +kernel

private theorem base_bounds {k x : ℕ} (hx : x ∈ base k) :
    41472 * k ≤ x ∧ x < 207360 * k := by
  obtain ⟨i, hlo, hhi, _⟩ := mem_base.mp hx
  exact ⟨(Nat.mul_le_mul_right k (row_bounds i).1).trans hlo,
    hhi.trans_le (Nat.mul_le_mul_right k (row_bounds i).2.2.1)⟩

private theorem periodic_card (a p r : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : Function.Periodic P p) :
    ((Ico a (a + p * r)).filter P).card = r * p.count P := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h₁ : a ≤ a + p * r := Nat.le_add_right _ _
    have h₂ : a + p * r ≤ a + p * r + p := Nat.le_add_right _ _
    rw [Nat.mul_succ, ← Nat.add_assoc, ← Ico_union_Ico_eq_Ico h₁ h₂, filter_union,
      card_union_of_disjoint ((Ico_disjoint_Ico_consecutive a (a + p * r) (a + p * r + p)).mono
        (filter_subset _ _) (filter_subset _ _)),
      ih, Nat.filter_Ico_card_eq_of_periodic _ _ _ hP, Nat.succ_mul]

private def weight (i : Fin 12) : ℕ :=
  let B := band i
  ((B.hi - B.lo) / B.period) * B.period.count B.accepts

private theorem base_card (k : ℕ) : (base k).card = 112320 * k := by
  have hdis : ((univ : Finset (Fin 12)) : Set (Fin 12)).PairwiseDisjoint
      (fun i => (band i).points k) := by
    intro i _ j _ hij
    have oneSide (a b : Fin 12) (hab : a < b) :
        Disjoint ((band a).points k) ((band b).points k) := by
      apply Finset.disjoint_left.mpr
      intro x hxa hxb
      exact (mem_points.mp hxa).2.1.not_ge
        ((Nat.mul_le_mul_right k (rows_ordered a b hab)).trans (mem_points.mp hxb).1)
    exact (lt_or_gt_of_ne hij).elim (oneSide i j) (fun h => (oneSide j i h).symm)
  unfold base
  rw [card_biUnion hdis]
  calc
    _ = ∑ i : Fin 12, weight i * k := by
      apply sum_congr rfl
      intro i _
      let B := band i
      have hgap : B.lo + B.period * ((B.hi - B.lo) / B.period) = B.hi := by
        rw [Nat.mul_div_cancel' (row_bounds i).2.2.2.2]
        exact Nat.add_sub_of_le (row_bounds i).2.1
      change ((Ico (B.lo * k) (B.hi * k)).filter B.accepts).card = _
      rw [show B.hi * k = B.lo * k + B.period * (((B.hi - B.lo) / B.period) * k) by
        rw [← mul_assoc, ← add_mul, hgap]]
      rw [periodic_card _ _ _ _ (fun x => by
        unfold Band.accepts
        rw [Nat.add_mod_right])]
      unfold weight
      ring
    _ = _ := by
      rw [← sum_mul]
      have hw : (∑ i : Fin 12, weight i) = 112320 := by decide +kernel
      rw [hw]

private def offsets (B : Band) (u w : ℕ) : Finset ℕ :=
  (range (w + 1)).filter fun a => B.accepts (u + a)

private theorem offsets_eq {B : Band} {u v w : ℕ} (h : u ≡ v [MOD B.period]) :
    offsets B u w = offsets B v w := by
  ext a
  simp only [offsets, mem_filter]
  unfold Band.accepts
  rw [show (u + a) % B.period = (v + a) % B.period from h.add_right a]

set_option maxRecDepth 4096 in
private theorem short_gaps (i : Fin 12) :
    ∀ u : Fin (band i).period, (band i).accepts u → 5 ≤ (offsets (band i) u 16).card := by
  fin_cases i <;> decide +kernel

private def destination : Fin 12 → Fin 5 → Option (Fin 12)
  | 0, 2 => some 5
  | 0, 3 => some 8
  | 0, 4 => some 10
  | 1, 2 => some 6
  | 1, 3 => some 9
  | 1, 4 => some 11
  | 3, 2 => some 8
  | 3, 3 => some 11
  | 4, 2 => some 9
  | 5, 2 => some 10
  | 6, 2 => some 11
  | _, _ => none

set_option maxRecDepth 4096 in
private theorem destination_bounds (i : Fin 12) (r : Fin 5) :
    2 ≤ r.val → (band i).residues.Nonempty →
    (destination i r = none → 207360 ≤ r.val * (band i).lo) ∧
      ∀ j : Fin 12, destination i r = some j →
        (band j).lo ≤ r.val * (band i).lo ∧ r.val * (band i).hi ≤ (band j).hi := by
  fin_cases i <;> fin_cases r <;> decide +kernel

private def residueCheck (B D : Band) (r : ℕ) : Prop :=
  ∀ (u : Fin (B.period.lcm D.period)) (w : Fin 16),
    B.accepts u → B.accepts (u + w) → (offsets B u w).card = r →
      ¬ D.accepts (∑ a ∈ offsets B u w, ((u : ℕ) + a))

instance (B D : Band) (r : ℕ) : Decidable (residueCheck B D r) := by
  unfold residueCheck
  infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem residue_checks (i : Fin 12) (r : Fin 5) :
    ∀ j : Fin 12, destination i r = some j → residueCheck (band i) (band j) r.val := by
  fin_cases i <;> fin_cases r <;> decide +kernel

private theorem distinct_bands {k x : ℕ} {i j : Fin 12}
    (hi : (band i).lo * k ≤ x ∧ x < (band i).hi * k)
    (hj : (band j).lo * k ≤ x ∧ x < (band j).hi * k) : i = j := by
  by_contra h
  rcases lt_or_gt_of_ne h with hij | hji
  · exact hi.2.not_ge ((Nat.mul_le_mul_right k (rows_ordered i j hij)).trans hj.1)
  · exact hj.2.not_ge ((Nat.mul_le_mul_right k (rows_ordered j i hji)).trans hi.1)

private theorem offset_subset {k m n u v w : ℕ} {i : Fin 12}
    (hu : u ∈ Icc m n ∩ base k) (hv : v ∈ Icc m n ∩ base k)
    (hulo : (band i).lo * k ≤ u) (hvhi : v < (band i).hi * k) (hw : u + w ≤ v) :
    (offsets (band i) u w).image (u + ·) ⊆ Icc m n ∩ base k := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
  obtain ⟨hal, hap⟩ := mem_filter.mp ha
  have hau : a < w + 1 := mem_range.mp hal
  have hum := (mem_Icc.mp (mem_inter.mp hu).1).1
  have hvn := (mem_Icc.mp (mem_inter.mp hv).1).2
  exact mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩,
    mem_base.mpr ⟨i, by omega, by omega, hap⟩⟩

private theorem homogeneous {k m n : ℕ} (i : Fin 12)
    (hcard : 2 ≤ (Icc m n ∩ base k).card) (hfour : (Icc m n ∩ base k).card ≤ 4)
    (hs : Icc m n ∩ base k ⊆ (band i).points k) :
    (∑ x ∈ Icc m n ∩ base k, x) ∉ base k := by
  let T := Icc m n ∩ base k
  let z := ∑ x ∈ T, x
  show z ∉ base k
  change 2 ≤ T.card at hcard
  change T.card ≤ 4 at hfour
  let B := band i
  have hT : T.Nonempty := card_pos.mp (by omega)
  let u := T.min' hT
  let v := T.max' hT
  have hu : u ∈ T := min'_mem _ _
  have hv : v ∈ T := max'_mem _ _
  have huB := mem_points.mp (hs hu)
  have hvB := mem_points.mp (hs hv)
  have huv : u ≤ v := min'_le _ _ hv
  have hB : 0 < B.period := (row_bounds i).2.2.2.1
  have hwidth : v - u < 16 := by
    by_contra! hwidth
    let q : Fin B.period := ⟨u % B.period, Nat.mod_lt _ hB⟩
    have hmod : u ≡ q.val [MOD B.period] := (Nat.mod_mod _ _).symm
    have hq : B.accepts q := by
      rw [Band.accepts, ← show u % B.period = q.val % B.period from hmod]
      exact huB.2.2
    have hfive : 5 ≤ (offsets B u 16).card := by
      rw [offsets_eq hmod]
      exact short_gaps i q hq
    have hle := card_le_card (offset_subset hu hv huB.1 hvB.2.1 (by omega : u + 16 ≤ v))
    rw [card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)] at hle
    change (offsets B u 16).card ≤ T.card at hle
    omega
  let w : Fin 16 := ⟨v - u, hwidth⟩
  have hshift : u + w.val = v := Nat.add_sub_of_le huv
  have hTeq : T = (offsets B u w).image (u + ·) := by
    refine Subset.antisymm ?_ (offset_subset hu hv huB.1 hvB.2.1 hshift.le)
    intro x hx
    have hul : u ≤ x := min'_le _ _ hx
    have hvu : x ≤ v := le_max' _ _ hx
    have heq : u + (x - u) = x := Nat.add_sub_of_le hul
    refine mem_image.mpr ⟨x - u, mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩, heq⟩
    · change x - u < v - u + 1
      omega
    · rw [heq]
      exact (mem_points.mp (hs hx)).2.2
  have hTcard : (offsets B u w).card = T.card := by
    conv_rhs => rw [hTeq, card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)]
  have hzsum : z = ∑ a ∈ offsets B u w, (u + a) := by
    dsimp [z]
    rw [hTeq, sum_image (fun _ _ _ _ h => Nat.add_left_cancel h)]
  have hzlo : T.card * (B.lo * k) ≤ z := by
    simpa [nsmul_eq_mul] using
      card_nsmul_le_sum T (fun x : ℕ => x) (B.lo * k) (fun x hx => (mem_points.mp (hs hx)).1)
  have hzhi : z < T.card * (B.hi * k) := by
    have h := sum_le_sum (fun x hx => Nat.succ_le_of_lt (mem_points.mp (hs hx)).2.1)
    have hh : (∑ x ∈ T, (x + 1)) ≤ ∑ _x ∈ T, (B.hi * k) := h
    simp [sum_add_distrib] at hh
    omega
  let r : Fin 5 := ⟨T.card, by omega⟩
  have hR : B.residues.Nonempty := ⟨u % B.period, huB.2.2⟩
  have hdest := destination_bounds i r hcard hR
  have hcert := residue_checks i r
  intro hz
  have hzbound := (base_bounds hz).2
  cases ht : destination i r with
  | none =>
    have h := Nat.mul_le_mul_right k (hdest.1 ht)
    rw [mul_assoc] at h
    exact hzbound.not_ge (h.trans hzlo)
  | some j =>
    have hbounds := hdest.2 j ht
    have hzB : (band j).lo * k ≤ z ∧ z < (band j).hi * k := by
      have h1 := Nat.mul_le_mul_right k hbounds.1
      have h2 := Nat.mul_le_mul_right k hbounds.2
      rw [mul_assoc] at h1 h2
      exact ⟨h1.trans hzlo, hzhi.trans_le h2⟩
    obtain ⟨j', hjlo, hjhi, hja⟩ := mem_base.mp hz
    have hJ : j' = j := distinct_bands ⟨hjlo, hjhi⟩ hzB
    subst j'
    let D := band j
    let l := B.period.lcm D.period
    let q : Fin l := ⟨u % l, Nat.mod_lt _ (Nat.lcm_pos hB (row_bounds j).2.2.2.1)⟩
    have hmodP : u ≡ q.val [MOD B.period] :=
      (Nat.mod_mod_of_dvd _ (Nat.dvd_lcm_left B.period D.period)).symm
    have hmodQ : u ≡ q.val [MOD D.period] :=
      (Nat.mod_mod_of_dvd _ (Nat.dvd_lcm_right B.period D.period)).symm
    have hq : B.accepts q := by
      rw [Band.accepts, ← show u % B.period = q.val % B.period from hmodP]
      exact huB.2.2
    have hqw : B.accepts (q.val + w.val) := by
      rw [Band.accepts, ← show (u + w.val) % B.period = (q.val + w.val) % B.period
        from hmodP.add_right _, hshift]
      exact hvB.2.2
    have hEq := offsets_eq (w := w.val) hmodP
    have hqcard : (offsets B q w).card = r.val := hEq ▸ hTcard
    have hsum := Nat.ModEq.sum (s := offsets B u w) fun a _ => hmodQ.add_right a
    rw [← hzsum] at hsum
    rw [hEq] at hsum
    apply hcert j ht q w hq hqw hqcard
    change (∑ a ∈ offsets B q w, (q.val + a)) % D.period ∈ D.residues
    rw [← show z % D.period = (∑ a ∈ offsets B q w, (q.val + a)) % D.period from hsum]
    exact hja

private def leftNear (A : Finset ℕ) (b : ℕ) : Finset ℕ :=
  A.filter fun x => x < b ∧ (A.filter fun y => x ≤ y ∧ y < b).card ≤ 4

private def rightNear (A : Finset ℕ) (b : ℕ) : Finset ℕ :=
  A.filter fun x => b ≤ x ∧ (A.filter fun y => b ≤ y ∧ y ≤ x).card ≤ 4

private theorem leftNear_card (A : Finset ℕ) (b : ℕ) : (leftNear A b).card ≤ 4 := by
  by_cases h : (leftNear A b).Nonempty
  · let x := (leftNear A b).min' h
    have hx : x ∈ leftNear A b := min'_mem _ _
    refine le_trans (card_le_card ?_) (mem_filter.mp hx).2.2
    intro y hy
    exact mem_filter.mpr ⟨(mem_filter.mp hy).1, min'_le _ _ hy, (mem_filter.mp hy).2.1⟩
  · simp [not_nonempty_iff_eq_empty.mp h]

private theorem rightNear_card (A : Finset ℕ) (b : ℕ) : (rightNear A b).card ≤ 4 := by
  by_cases h : (rightNear A b).Nonempty
  · let x := (rightNear A b).max' h
    have hx : x ∈ rightNear A b := max'_mem _ _
    refine le_trans (card_le_card ?_) (mem_filter.mp hx).2.2
    intro y hy
    exact mem_filter.mpr ⟨(mem_filter.mp hy).1, (mem_filter.mp hy).2.1, le_max' _ _ hy⟩
  · simp [not_nonempty_iff_eq_empty.mp h]

private theorem near_of_crossing {A : Finset ℕ} {b m n : ℕ}
    {u v : ℕ} (hu : u ∈ Icc m n ∩ A) (hv : v ∈ Icc m n ∩ A) (hb : u < b ∧ b ≤ v)
    (hc : (Icc m n ∩ A).card ≤ 4) :
    Icc m n ∩ A ⊆ leftNear A b ∪ rightNear A b := by
  have hu' := mem_Icc.mp (mem_inter.mp hu).1
  have hv' := mem_Icc.mp (mem_inter.mp hv).1
  intro x hx
  obtain ⟨hxi, hxA⟩ := mem_inter.mp hx
  have hxi' := mem_Icc.mp hxi
  by_cases hxb : x < b
  · apply mem_union_left
    refine mem_filter.mpr ⟨hxA, hxb, le_trans (card_le_card ?_) hc⟩
    intro y hy
    obtain ⟨hyA, hyx, hyb⟩ := mem_filter.mp hy
    exact mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hyA⟩
  · apply mem_union_right
    refine mem_filter.mpr ⟨hxA, by omega, le_trans (card_le_card ?_) hc⟩
    intro y hy
    obtain ⟨hyA, hyb, hyx⟩ := mem_filter.mp hy
    exact mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hyA⟩

-- A window which crosses b can have only four points, chosen within four positions of b.
private def candidates (A : Finset ℕ) (b : ℕ) : Finset ℕ :=
  (leftNear A b ∪ rightNear A b).powerset.image (fun s => ∑ x ∈ s, x)

private theorem candidates_card (A : Finset ℕ) (b : ℕ) : (candidates A b).card ≤ 256 := by
  unfold candidates
  refine card_image_le.trans ?_
  rw [card_powerset]
  change 2 ^ _ ≤ 2 ^ 8
  apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
  exact (card_union_le _ _).trans (Nat.add_le_add (leftNear_card A b) (rightNear_card A b))

private theorem sum_mem_candidates {A : Finset ℕ} {b m n : ℕ}
    {u v : ℕ} (hu : u ∈ Icc m n ∩ A) (hv : v ∈ Icc m n ∩ A) (hb : u < b ∧ b ≤ v)
    (hc : (Icc m n ∩ A).card ≤ 4) :
    (∑ x ∈ Icc m n ∩ A, x) ∈ candidates A b :=
  mem_image.mpr ⟨_, mem_powerset.mpr (near_of_crossing hu hv hb hc), rfl⟩

-- Both endpoints of a witness window are required to belong to the set.
private noncomputable def bad (A : Finset ℕ) : Finset ℕ := by
  classical
  exact A.filter (fun z =>
    ∃ a ∈ A, ∃ b ∈ A, 2 ≤ (Icc a b ∩ A).card ∧ ∑ x ∈ Icc a b ∩ A, x = z)

private theorem mem_bad {A : Finset ℕ} {z : ℕ} :
    z ∈ bad A ↔ z ∈ A ∧
      ∃ a ∈ A, ∃ b ∈ A, 2 ≤ (Icc a b ∩ A).card ∧ ∑ x ∈ Icc a b ∩ A, x = z := by
  classical
  exact mem_filter

private theorem bad_eq_empty {A : Finset ℕ} (h : bad A = ∅) :
    Erdos867.ConsecutiveSumFree A := by
  intro m n hcard hsum
  let T := Icc m n ∩ A
  change 2 ≤ T.card at hcard
  have hTne : T.Nonempty := card_pos.mp (by omega)
  let a := T.min' hTne
  let b := T.max' hTne
  have ha : a ∈ T := min'_mem _ _
  have hb : b ∈ T := max'_mem _ _
  have haI := mem_Icc.mp (mem_inter.mp ha).1
  have hbI := mem_Icc.mp (mem_inter.mp hb).1
  have hT : T = Icc a b ∩ A := by
    ext x
    constructor
    · intro hx
      exact mem_inter.mpr ⟨mem_Icc.mpr ⟨min'_le _ _ hx, le_max' _ _ hx⟩, (mem_inter.mp hx).2⟩
    · intro hx
      have hxI := mem_Icc.mp (mem_inter.mp hx).1
      exact mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, (mem_inter.mp hx).2⟩
  have hmem : (∑ x ∈ T, x) ∈ bad A := by
    apply mem_bad.mpr
    refine ⟨hsum, a, (mem_inter.mp ha).2, b, (mem_inter.mp hb).2, ?_, ?_⟩
    · rw [← hT]
      exact hcard
    · rw [← hT]
  simp only [h, notMem_empty] at hmem

private theorem window_lower {A : Finset ℕ} {k a b : ℕ} (hA : A ⊆ base k) :
    (Icc a b ∩ A).card * (41472 * k) ≤ ∑ x ∈ Icc a b ∩ A, x := by
  simpa [nsmul_eq_mul] using card_nsmul_le_sum (Icc a b ∩ A) (fun x : ℕ => x) (41472 * k)
    (fun _ hx => (base_bounds (hA (mem_inter.mp hx).2)).1)

private theorem window_four {A : Finset ℕ} {k a b : ℕ} (hA : A ⊆ base k)
    (hz : (∑ x ∈ Icc a b ∩ A, x) ∈ A) :
    (Icc a b ∩ A).card ≤ 4 := by
  by_contra! h
  have h₁ := window_lower (a := a) (b := b) hA
  have h₂ := Nat.mul_le_mul_right (41472 * k) (show 5 ≤ (Icc a b ∩ A).card by omega)
  have h₃ := (base_bounds (hA hz)).2
  omega

private theorem initial_card (k : ℕ) : (bad (base k)).card ≤ 12 * 256 := by
  refine (card_le_card (t := (univ : Finset (Fin 12)).biUnion
    (fun i => candidates (base k) ((band i).lo * k))) ?_).trans ?_
  · intro z hz
    obtain ⟨hzB, a, ha, b, hb, hc, hzsum⟩ := mem_bad.mp hz
    have hab : a ≤ b := by
      obtain ⟨x, hx⟩ := card_pos.mp (show 0 < (Icc a b ∩ base k).card by omega)
      exact (mem_Icc.mp (mem_inter.mp hx).1).1.trans (mem_Icc.mp (mem_inter.mp hx).1).2
    have haT : a ∈ Icc a b ∩ base k := mem_inter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hab⟩, ha⟩
    have hbT : b ∈ Icc a b ∩ base k := mem_inter.mpr ⟨mem_Icc.mpr ⟨hab, le_rfl⟩, hb⟩
    obtain ⟨i, hail, haih, _⟩ := mem_base.mp ha
    obtain ⟨j, hbjl, hbjh, _⟩ := mem_base.mp hb
    have hzB' : (∑ x ∈ Icc a b ∩ base k, x) ∈ base k := hzsum ▸ hzB
    have hf := window_four (Subset.rfl : base k ⊆ base k) hzB'
    rcases lt_trichotomy i j with hij | rij | hji
    · have haa := haih.trans_le (Nat.mul_le_mul_right k (rows_ordered i j hij))
      exact mem_biUnion.mpr ⟨j, mem_univ _, hzsum ▸ sum_mem_candidates haT hbT ⟨haa, hbjl⟩ hf⟩
    · subst j
      have hsub : Icc a b ∩ base k ⊆ (band i).points k := by
        intro x hx
        obtain ⟨hxab, hxA⟩ := mem_inter.mp hx
        have hlo := hail.trans (mem_Icc.mp hxab).1
        have hhi := (mem_Icc.mp hxab).2.trans_lt hbjh
        obtain ⟨j, hxl, hxh, hxp⟩ := mem_base.mp hxA
        have hEq : j = i := distinct_bands ⟨hxl, hxh⟩ ⟨hlo, hhi⟩
        subst j
        exact mem_points.mpr ⟨hlo, hhi, hxp⟩
      exact (homogeneous i hc hf hsub hzB').elim
    · exact (hbjh.not_ge ((Nat.mul_le_mul_right k (rows_ordered j i hji)).trans
        (hail.trans hab))).elim
  · simpa using card_biUnion_le_card_mul (univ : Finset (Fin 12))
      (fun i => candidates (base k) ((band i).lo * k)) 256 (fun i _ => candidates_card _ _)

private noncomputable def prune (A : Finset ℕ) : Finset ℕ := A \ bad A

private theorem prune_subset (A : Finset ℕ) : prune A ⊆ A := sdiff_subset

-- Any newly bad window contains a deleted point between its endpoints.
private theorem next_witness {A : Finset ℕ} {k z : ℕ} (hA : A ⊆ base k)
    (hz : z ∈ bad (prune A)) :
    ∃ d ∈ bad A, z ∈ candidates (prune A) d ∧ 41472 * k + d ≤ z := by
  obtain ⟨hz', a, ha, b, hb, hc, hzsum⟩ := mem_bad.mp hz
  let T := Icc a b ∩ prune A
  have hab : a < b := by
    by_contra! h
    have hsmall : T ⊆ {a} := by
      intro x hx
      have hh := mem_Icc.mp (mem_inter.mp hx).1
      exact mem_singleton.mpr (by omega)
    have hh := card_le_card hsmall
    rw [card_singleton] at hh
    change 2 ≤ T.card at hc
    omega
  have haT : a ∈ T := mem_inter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hab.le⟩, ha⟩
  have hbT : b ∈ T := mem_inter.mpr ⟨mem_Icc.mpr ⟨hab.le, le_rfl⟩, hb⟩
  have hdel : ∃ d ∈ Icc a b ∩ A, d ∈ bad A := by
    by_contra! h
    have heq : Icc a b ∩ A = T := by
      ext x
      simp only [T, prune, mem_inter, mem_sdiff]
      constructor
      · intro hx
        exact ⟨hx.1, hx.2, h x (mem_inter.mpr hx)⟩
      · exact fun hx => ⟨hx.1, hx.2.1⟩
    have hzbad : z ∈ bad A := mem_bad.mpr
      ⟨prune_subset _ hz', a, prune_subset _ ha, b, prune_subset _ hb,
        heq.symm ▸ hc, heq.symm ▸ hzsum⟩
    exact (mem_sdiff.mp hz').2 hzbad
  obtain ⟨d, hd, hda⟩ := hdel
  have hdI := mem_Icc.mp (mem_inter.mp hd).1
  have hstrict : a < d := lt_of_le_of_ne hdI.1 (fun h => (mem_sdiff.mp ha).2 (h ▸ hda))
  have hcard := window_four ((prune_subset A).trans hA) (hzsum ▸ hz')
  have hcand := sum_mem_candidates haT hbT ⟨hstrict, hdI.2⟩ hcard
  have hsum : a + b ≤ ∑ x ∈ T, x := by
    have hsub : ({a, b} : Finset ℕ) ⊆ T :=
      insert_subset_iff.mpr ⟨haT, singleton_subset_iff.mpr hbT⟩
    simpa [sum_insert, hab.ne] using (sum_le_sum_of_subset (f := fun x : ℕ => x) hsub)
  have hlo := (base_bounds (hA (prune_subset A ha))).1
  exact ⟨d, hda, hzsum ▸ hcand, by change ∑ x ∈ T, x = z at hzsum; omega⟩

private theorem next_card {A : Finset ℕ} {k : ℕ} (hA : A ⊆ base k) :
    (bad (prune A)).card ≤ (bad A).card * 256 := by
  refine (card_le_card (t := (bad A).biUnion (candidates (prune A))) ?_).trans ?_
  · intro z hz
    obtain ⟨d, hd, hzd, _⟩ := next_witness hA hz
    exact mem_biUnion.mpr ⟨d, hd, hzd⟩
  · exact card_biUnion_le_card_mul _ _ _ (fun d _ => candidates_card _ d)

private theorem next_lower {A : Finset ℕ} {k l : ℕ} (hA : A ⊆ base k)
    (hlo : ∀ x ∈ bad A, l ≤ x) : ∀ z ∈ bad (prune A), 41472 * k + l ≤ z := by
  intro z hz
  obtain ⟨d, hd, _, hzd⟩ := next_witness hA hz
  exact (Nat.add_le_add_left (hlo d hd) _).trans hzd

private theorem cleaned (k : ℕ) :
    ∃ A ⊆ base k, Erdos867.ConsecutiveSumFree A ∧ 112320 * k ≤ A.card + 203000000 := by
  let A₀ := base k
  let A₁ := prune A₀
  let A₂ := prune A₁
  let A₃ := prune A₂
  have h₁ : A₁ ⊆ A₀ := prune_subset _
  have h₂ : A₂ ⊆ A₀ := (prune_subset _).trans h₁
  have h₃ : A₃ ⊆ A₀ := (prune_subset _).trans h₂
  have hlo₀ : ∀ z ∈ bad A₀, 2 * (41472 * k) ≤ z := by
    intro z hz
    obtain ⟨_, a, _, b, _, hc, hsum⟩ := mem_bad.mp hz
    exact (Nat.mul_le_mul_right _ hc).trans
      (hsum ▸ window_lower (a := a) (b := b) (Subset.rfl : A₀ ⊆ base k))
  have hlo₁ : ∀ z ∈ bad A₁, 41472 * k + 2 * (41472 * k) ≤ z := next_lower Subset.rfl hlo₀
  have hlo₂ := next_lower h₁ hlo₁
  have hlo₃ := next_lower h₂ hlo₂
  have hempty : bad A₃ = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    have hlu := hlo₃ z hz
    have hzu := (base_bounds (h₃ (mem_bad.mp hz).1)).2
    omega
  refine ⟨A₃, h₃, bad_eq_empty hempty, ?_⟩
  have hbase : A₀.card = 112320 * k := base_card k
  have hb₀ : (bad A₀).card ≤ 12 * 256 := initial_card k
  have hb₁ : (bad A₁).card ≤ (bad A₀).card * 256 := next_card (Subset.rfl : A₀ ⊆ base k)
  have hb₂ : (bad A₂).card ≤ (bad A₁).card * 256 := next_card h₁
  have hc (A : Finset ℕ) : A.card ≤ (prune A).card + (bad A).card :=
    card_le_card_sdiff_add_card
  have hc₀ : A₀.card ≤ A₁.card + (bad A₀).card := hc A₀
  have hc₁ : A₁.card ≤ A₂.card + (bad A₁).card := hc A₁
  have hc₂ : A₂.card ≤ A₃.card + (bad A₂).card := hc A₂
  omega

end CoppersmithPhillips

theorem OMA.solution :
    type_of% @Erdos867.erdos_867.variants.coppersmith_phillips_lower_bound := by
  refine ⟨203112320, fun N => ?_⟩
  let k := N / 207360
  obtain ⟨A, hA, hf, hcard⟩ := CoppersmithPhillips.cleaned k
  have hkle : 207360 * k ≤ N := by dsimp [k]; omega
  have hklt : N < 207360 * (k + 1) := by dsimp [k]; omega
  refine ⟨A, ?_, hf, ?_⟩
  · intro x hx
    have := CoppersmithPhillips.base_bounds (hA hx)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hkltR : (N : ℝ) < 207360 * ((k : ℝ) + 1) := by exact_mod_cast hklt
  have hcardR : 112320 * (k : ℝ) ≤ (A.card : ℝ) + 203000000 := by exact_mod_cast hcard
  linarith