import FormalConjectures.ErdosProblems.«750»

/-! The shift graph witnesses the Erdős–Hajnal bound. Credit: @Genbox. -/

open Finset
open scoped BigOperators

namespace OMA

universe u

private abbrev Vertex := ULift.{u} {p : ℕ × ℕ // p.1 < p.2}

private def shiftGraph : SimpleGraph Vertex where
  Adj u v := u.down.1.2 = v.down.1.1 ∨ v.down.1.2 = u.down.1.1
  symm := by constructor; intro _ _ h; exact h.symm
  loopless := by constructor; intro u h; exact u.down.2.ne (h.elim Eq.symm Eq.symm)

private theorem shiftGraph_infinite_chromatic : shiftGraph.chromaticNumber = ⊤ := by
  classical
  by_contra h
  obtain ⟨k, ⟨color⟩⟩ := shiftGraph.chromaticNumber_ne_top_iff_exists.mp h
  let palette (a : ℕ) : Set (Fin k) :=
    {cl | ∃ b : ℕ, ∃ hab : a < b, color ⟨⟨(a, b), hab⟩⟩ = cl}
  have separates (a b : ℕ) (hab : a < b) : palette a ≠ palette b := by
    intro heq
    have hmem : color ⟨⟨(a, b), hab⟩⟩ ∈ palette a := ⟨b, hab, rfl⟩
    rw [heq] at hmem
    obtain ⟨d, hbd, he⟩ := hmem
    exact color.valid (v := ⟨⟨(b, d), hbd⟩⟩) (w := ⟨⟨(a, b), hab⟩⟩) (Or.inr rfl) he
  have hinj : Function.Injective palette := by
    intro a b h
    rcases lt_trichotomy a b with hab | eq | hba
    · exact False.elim (separates a b hab h)
    · exact eq
    · exact False.elim (separates b a hba h.symm)
  have : Finite ℕ := Finite.of_injective palette hinj
  exact not_finite ℕ

-- Once membership of two distinct endpoints is prescribed, the other choices are free.
private theorem card_cuts (t : Finset ℕ) {a b : ℕ}
    (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b) :
    (t.powerset.filter (fun d => a ∈ d ∧ b ∉ d)).card = 2 ^ (t.card - 2) := by
  classical
  let u := (t.erase a).erase b
  have hua : a ∉ u := fun h => (notMem_erase a _) (mem_of_mem_erase h)
  have hub : b ∉ u := notMem_erase b _
  have hinj : Set.InjOn (fun d : Finset ℕ => insert a d) u.powerset := by
    intro d hd e he h
    have hda : a ∉ d := notMem_mono (mem_powerset.mp hd) hua
    have hea : a ∉ e := notMem_mono (mem_powerset.mp he) hua
    simpa [hda, hea] using congrArg (fun f : Finset ℕ => f.erase a) h
  have himage :
      u.powerset.image (fun d => insert a d) =
        t.powerset.filter (fun d => a ∈ d ∧ b ∉ d) := by
    ext d
    constructor
    · intro hd
      obtain ⟨e, he, rfl⟩ := mem_image.mp hd
      have he' := mem_powerset.mp he
      exact mem_filter.mpr ⟨mem_powerset.mpr (insert_subset ha
        (he'.trans ((erase_subset _ _).trans (erase_subset _ _)))),
        mem_insert_self _ _, by simpa [Ne.symm hab] using notMem_mono he' hub⟩
    · intro hd
      obtain ⟨hdt, hda, hdb⟩ := mem_filter.mp hd
      refine mem_image.mpr ⟨d.erase a, mem_powerset.mpr ?_, insert_erase hda⟩
      intro x hx
      have hxd := mem_of_mem_erase hx
      exact mem_erase.mpr ⟨fun h => hdb (h ▸ hxd),
        mem_erase.mpr ⟨(mem_erase.mp hx).1, mem_powerset.mp hdt hxd⟩⟩
  rw [← himage, card_image_of_injOn hinj, card_powerset]
  rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hab, hb⟩), card_erase_of_mem ha]
  simp [Nat.sub_sub]


end OMA

open OMA

theorem OMA.solution : type_of% @Erdos750.erdos_750.variants.c_gt_quarter := by
  classical
  intro c hc
  refine ⟨Vertex, shiftGraph, shiftGraph_infinite_chromatic, ?_⟩
  intro m S hm hSm
  have hf : S.Finite := Set.finite_of_ncard_ne_zero (by omega)
  let s := hf.toFinset
  have hs : s.card = m := (Set.ncard_eq_toFinset_card S hf).symm.trans hSm
  let t := s.image (fun v => v.down.1.1) ∪ s.image (fun v => v.down.1.2)
  let cut (d : Finset ℕ) := s.filter (fun v => v.down.1.1 ∈ d ∧ v.down.1.2 ∉ d)
  have left_mem (v : Vertex) (hv : v ∈ s) : v.down.1.1 ∈ t :=
    mem_union_left _ (mem_image_of_mem _ hv)
  have right_mem (v : Vertex) (hv : v ∈ s) : v.down.1.2 ∈ t :=
    mem_union_right _ (mem_image_of_mem _ hv)
  have ht : 2 ≤ t.card := by
    obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < s.card)
    calc
      2 = ({v.down.1.1, v.down.1.2} : Finset ℕ).card := (card_pair v.down.2.ne).symm
      _ ≤ t.card := card_le_card (by
        intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact left_mem v hv
        · rw [mem_singleton.mp hx]
          exact right_mem v hv)
  have hsum : ∑ d ∈ t.powerset, (cut d).card = m * 2 ^ (t.card - 2) := calc
    _ = ∑ v ∈ s, (t.powerset.filter (fun d => v.down.1.1 ∈ d ∧ v.down.1.2 ∉ d)).card := by
      simp only [cut, card_filter]
      rw [sum_comm]
    _ = _ := by
      rw [← hs]
      calc
        _ = ∑ _v ∈ s, 2 ^ (t.card - 2) :=
          sum_congr rfl (fun v hv => card_cuts t (left_mem v hv) (right_mem v hv) v.down.2.ne)
        _ = _ := by simp
  have h4 : 2 ^ t.card = 4 * 2 ^ (t.card - 2) := by
    conv_lhs => rw [show t.card = 2 + (t.card - 2) by omega, pow_add]
    norm_num
  obtain ⟨d, hd, hdc⟩ : ∃ d ∈ t.powerset, m ≤ 4 * (cut d).card := by
    apply exists_le_of_sum_le (powerset_nonempty _)
    simp only [sum_const, card_powerset, nsmul_eq_mul, ← mul_sum, hsum, h4]
    exact le_of_eq (by ac_rfl)
  refine ⟨(cut d : Set Vertex), ?_, ?_, ?_⟩
  · intro v hv
    exact hf.mem_toFinset.mp (mem_filter.mp hv).1
  · rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv _ hadj
    obtain ⟨_, hua, hub⟩ := mem_filter.mp hu
    obtain ⟨_, hva, hvb⟩ := mem_filter.mp hv
    rcases hadj with h | h
    · exact hub (h ▸ hva)
    · exact hvb (h ▸ hua)
  · have hdc' : (m : ℝ) ≤ 4 * ((cut d).card : ℝ) := by exact_mod_cast hdc
    rw [tsub_le_iff_right]
    rw [Set.ncard_coe_finset]
    have hc' : (1 / 4 : ℝ) < (c : ℝ) := by exact_mod_cast hc
    exact_mod_cast (show (m : ℝ) / 2 ≤ ((cut d).card : ℝ) + (c : ℝ) * m from by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc'.le) (Nat.cast_nonneg (α := ℝ) m)])