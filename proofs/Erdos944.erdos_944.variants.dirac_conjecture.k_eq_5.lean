import FormalConjectures.ErdosProblems.«944»
import Mathlib

/-!
# A five-chromatic vertex-critical graph without critical edges

We specialize the circulant grid construction and the color-class counting argument
from @desenyon's composite-case proof in open-math-agents PR #53. On 17 vertices,
the local colorings can be certified by finite enumeration in the kernel.
-/

namespace DiracFive

open SimpleGraph
open scoped Fin.CommRing

-- The complement of the king's moves on a grid of width four, modulo 17.
def far (x y : Fin 17) : Prop :=
  let d := (x - y).val
  d = 2 ∨ (6 ≤ d ∧ d ≤ 11) ∨ d = 15

instance (x y : Fin 17) : Decidable (far x y) := by unfold far; infer_instance

def grid : SimpleGraph (Fin 17) where
  Adj := far
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel grid.Adj := fun x y => inferInstanceAs (Decidable (far x y))

lemma translate (x y v : Fin 17) : grid.Adj (x - v) (y - v) ↔ grid.Adj x y := by
  change far (x - v) (y - v) ↔ far x y
  simp [far, sub_sub_sub_cancel_right]

-- The nine non-neighbors of zero (including zero) lie on a three-by-three patch.
-- Three parity colorings of this patch allow one exceptional pair to be separated.
def paint (mode : Fin 3) (z : Fin 17) : Fin 4 :=
  let i := ((z.val + 5) % 17) % 4
  let j := ((z.val + 5) % 17) / 4
  ⟨(i + (if mode = 1 then j / 2 else 0)) % 2 +
   2 * ((j + (if mode = 2 then i / 2 else 0)) % 2), by omega⟩

set_option maxRecDepth 4096 in
lemma paint_proper : ∀ (m : Fin 3) (p q : Fin 17),
    ¬grid.Adj p 0 → ¬grid.Adj q 0 → ¬grid.Adj p q → paint m p = paint m q → p = q := by decide

set_option maxRecDepth 4096 in
lemma paint_separates : ∀ (p q : Fin 17), ∃ m : Fin 3,
    ¬grid.Adj p 0 → ¬grid.Adj q 0 → p ≠ q → paint m p ≠ paint m q := by decide

lemma independent_bound (e : Sym2 (Fin 17)) (S : Finset (Fin 17))
    (ind : (grid.deleteEdges {e}).IsIndepSet (S : Set _)) : S.card ≤ 4 := by
  classical
  induction e using Sym2.inductionOn with
  | _ l r =>
    have exception {x y} (hx : x ∈ S) (hy : y ∈ S) (h : grid.Adj x y) :
        x = l ∧ y = r ∨ x = r ∧ y = l := by
      apply Sym2.eq_iff.mp
      by_contra hn
      exact ind hx hy h.ne (deleteEdges_adj.mpr ⟨h, hn⟩)
    by_cases small : S ⊆ {l, r}
    · have h := Finset.card_le_card small
      have hr := Finset.card_insert_le l ({r} : Finset _)
      simp only [Finset.card_singleton] at hr
      omega
    obtain ⟨v, hv, hnot⟩ : ∃ x ∈ S, x ∉ ({l, r} : Finset _) := by
      by_contra! h
      exact small h
    have near (x : Fin 17) (hx : x ∈ S) : ¬grid.Adj (x - v) 0 := by
      intro h
      have adj := (translate x v v).mp (by simpa using h)
      rcases exception hx hv adj with h | h <;> simp_all
    obtain ⟨m, sep⟩ := paint_separates (l - v) (r - v)
    have inj : Function.Injective (fun x : S => paint m (x.val - v)) := by
      intro x y eq
      by_cases adj : grid.Adj x.val y.val
      · rcases exception x.property y.property adj with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · rw [← hx, ← hy] at sep
          exact (sep (near x x.property) (near y y.property)
            (fun h => adj.ne (sub_left_inj.mp h)) eq).elim
        · rw [← hy, ← hx] at sep
          exact (sep (near y y.property) (near x x.property)
            (fun h => adj.ne.symm (sub_left_inj.mp h)) eq.symm).elim
      · apply Subtype.ext
        exact sub_left_inj.mp (paint_proper m _ _ (near x x.property) (near y y.property)
          (fun h => adj ((translate _ _ v).mp h)) eq)
    simpa using Fintype.card_le_of_injective _ inj

-- Remove zero and tile the remaining four-by-four board by four two-by-two blocks.
def tileColor (x : Fin 17) : Fin 4 :=
  let i := x.val - 1
  ⟨(i % 4) / 2 + 2 * (i / 8), by have := x.isLt; dsimp [i]; omega⟩

set_option maxRecDepth 4096 in
lemma tile_proper : ∀ x y : Fin 17,
    x ≠ 0 → y ≠ 0 → grid.Adj x y → tileColor x ≠ tileColor y := by decide

lemma tiling (v : Fin 17) : ∃ c : Fin 17 → Fin 4,
    ∀ x y, x ≠ v → y ≠ v → grid.Adj x y → c x ≠ c y := by
  exact ⟨fun x => tileColor (x - v), fun x y hx hy h =>
    tile_proper _ _ (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hy) ((translate x y v).mpr h)⟩

universe u

lemma witness_of_four_vertex_classes {W : Type} [Fintype W] [Nonempty W]
    (G : SimpleGraph W) (q : ℕ) (size : Fintype.card W = 4 * q + 1)
    (tile : ∀ v, ∃ c : W → Fin q, ∀ x y, x ≠ v → y ≠ v → G.Adj x y → c x ≠ c y)
    (bound : ∀ (e : Sym2 W) (S : Finset W),
      (G.deleteEdges {e}).IsIndepSet (S : Set W) → S.card ≤ 4) :
    ∃ (V : Type u) (J : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 J (q + 1) 1 := by
  classical
  let V := ULift.{u} W
  let point : V := ULift.up (Classical.choice (inferInstance : Nonempty W))
  letI : Nonempty (Sym2 V) := ⟨Sym2.mk point point⟩
  let J := G.comap (ULift.down : V → W)
  refine ⟨V, J, ?_⟩
  have lower (E : Set (Sym2 V)) (hE : E.ncard ≤ 1) : ¬ (J.deleteEdges E).Colorable q := by
    obtain ⟨e, he⟩ := (Set.ncard_le_one_iff_subset_singleton).mp hE
    rintro ⟨c⟩
    let f : W → Fin q := fun x => c (ULift.up x)
    obtain ⟨i, hi⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (n := 4)
      (by rw [Fintype.card_fin, size, Nat.mul_comm q 4]; omega)
    apply (Nat.not_lt_of_ge (bound (e.map ULift.down) (Finset.univ.filter (fun x => f x = i)) ?_)) hi
    intro x hx y hy _ hadj
    have hxy : (J.deleteEdges E).Adj (ULift.up x) (ULift.up y) := by
      refine deleteEdges_adj.mpr ⟨(deleteEdges_adj.mp hadj).1, ?_⟩
      intro hm
      apply (deleteEdges_adj.mp hadj).2
      exact congrArg (Sym2.map ULift.down) (Set.mem_singleton_iff.mp (he hm))
    exact c.valid hxy (((Finset.mem_filter.mp hx).2).trans ((Finset.mem_filter.mp hy).2).symm)
  obtain ⟨c, hc⟩ := tile (Classical.choice (inferInstance : Nonempty W))
  let v := Classical.choice (inferInstance : Nonempty W)
  have upper : J.Colorable (q + 1) := by
    refine ⟨Coloring.mk (fun x : V => if x.down = v then Fin.last q else (c x.down).castSucc) ?_⟩
    intro x y hxy
    change G.Adj x.down y.down at hxy
    split_ifs with hx hy hy
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · exact (Fin.castSucc_ne_last _).symm
    · exact Fin.castSucc_ne_last _
    · exact fun h => hc _ _ hx hy hxy (Fin.castSucc_injective _ h)
  have chi : J.chromaticNumber = (q : ℕ∞) + 1 :=
    chromaticNumber_eq_iff_colorable_not_colorable.mpr
      ⟨upper, by simpa only [deleteEdges_empty] using lower ∅ (by simp)⟩
  constructor
  · refine ⟨by simpa using chi, ?_⟩
    intro x
    obtain ⟨d, hd⟩ := tile x.down
    let K := (⊤ : J.Subgraph).deleteVerts {x}
    have hK : K.coe.Colorable q := by
      refine ⟨Coloring.mk (fun y : K.verts => d y.val.down) ?_⟩
      intro y z hyz
      apply hd
      · exact fun h => y.property.2 (ULift.ext _ _ h)
      · exact fun h => z.property.2 (ULift.ext _ _ h)
      · exact K.adj_sub hyz
    change K.coe.chromaticNumber < (⊤ : J.Subgraph).coe.chromaticNumber
    rw [chromaticNumber_congr (Subgraph.topIso (G := J)), chi]
    exact lt_of_le_of_lt hK.chromaticNumber_le (by exact_mod_cast Nat.lt_succ_self q)
  · intro E hcrit
    by_contra! hE
    have hle : ((q + 1 : ℕ) : ℕ∞) ≤ (J.deleteEdges E).chromaticNumber := by
      apply (le_chromaticNumber_iff_not_colorable (by omega : q + 1 ≠ 0)).mpr
      simpa using lower E hE
    exact (not_lt_of_ge (show J.chromaticNumber ≤ _ by simpa [chi] using hle)) hcrit

end DiracFive

theorem OMA.solution : type_of% @Erdos944.erdos_944.variants.dirac_conjecture.k_eq_5 := by
  exact DiracFive.witness_of_four_vertex_classes DiracFive.grid 4 (by decide)
    DiracFive.tiling DiracFive.independent_bound
