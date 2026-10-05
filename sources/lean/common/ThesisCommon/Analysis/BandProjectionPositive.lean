import ThesisCommon.Analysis.PositiveConeExtension
import ThesisCommon.Analysis.PositiveOperatorOrder
import ThesisCommon.Analysis.RieszDecomposition
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Constructing the positive part of a band projection from solidity and
closure under existing positive directed suprema. No projection is assumed. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E]

/-- The order conditions defining the ideals used for band projections. -/
structure IsOrderClosedIdeal (I : Submodule ℝ E) : Prop where
  solid : ∀ {x y : E}, y ∈ I → |x| ≤ |y| → x ∈ I
  closed : ∀ {s : Set E}, s.Nonempty → (∀ x ∈ s, x ∈ I) → (∀ x ∈ s, 0 ≤ x) →
    DirectedOn (· ≤ ·) s → ∀ {x : E}, IsLUB s x → x ∈ I

def idealPositiveBelow (I : Submodule ℝ E) (x : E) : Set E :=
  {y | y ∈ I ∧ 0 ≤ y ∧ y ≤ x}

def idealPositiveProjection (I : Submodule ℝ E) (x : E) : E := sSup (idealPositiveBelow I x)

omit [IsOrderedAddMonoid E] in
theorem idealPositiveBelow_nonempty (I : Submodule ℝ E) (x : E) (hx : 0 ≤ x) :
    (idealPositiveBelow I x).Nonempty := ⟨0, I.zero_mem, le_rfl, hx⟩

namespace IsOrderClosedIdeal
variable {I : Submodule ℝ E} (hI : IsOrderClosedIdeal I)
include hI

theorem nonneg_le_mem {x y : E} (hy : y ∈ I) (hx : 0 ≤ x) (hxy : x ≤ y) : x ∈ I :=
  hI.solid hy (by simpa only [abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy)] using hxy)

theorem abs_mem {x : E} (hx : x ∈ I) : |x| ∈ I := hI.solid hx (by simp)

theorem posPart_mem {x : E} (hx : x ∈ I) : x⁺ ∈ I := by
  apply hI.nonneg_le_mem (hI.abs_mem hx) (posPart_nonneg x)
  exact sup_le (le_abs_self x) (abs_nonneg x)

theorem negPart_mem {x : E} (hx : x ∈ I) : x⁻ ∈ I := by
  simpa only [posPart_neg] using hI.posPart_mem (I.neg_mem hx)

theorem positiveBelow_directed (x : E) : DirectedOn (· ≤ ·) (idealPositiveBelow I x) := by
  intro u hu v hv
  have hsup : u ⊔ v ∈ I := hI.nonneg_le_mem (I.add_mem hu.1 hv.1)
    (hu.2.1.trans le_sup_left) (sup_le (le_add_of_nonneg_right hv.2.1) (le_add_of_nonneg_left hu.2.1))
  exact ⟨u ⊔ v, ⟨hsup, hu.2.1.trans le_sup_left, sup_le hu.2.2 hv.2.2⟩, le_sup_left, le_sup_right⟩

theorem positiveProjection_isLUB (x : E) (hx : 0 ≤ x) :
    IsLUB (idealPositiveBelow I x) (idealPositiveProjection I x) :=
  isLUB_csSup (idealPositiveBelow_nonempty I x hx) ⟨x, fun _ hy => hy.2.2⟩

theorem positiveProjection_nonneg (x : E) (hx : 0 ≤ x) : 0 ≤ idealPositiveProjection I x :=
  (hI.positiveProjection_isLUB x hx).1 ⟨I.zero_mem, le_rfl, hx⟩

theorem positiveProjection_le (x : E) (hx : 0 ≤ x) : idealPositiveProjection I x ≤ x :=
  (hI.positiveProjection_isLUB x hx).2 (fun _ hy => hy.2.2)

theorem positiveProjection_mem (x : E) (hx : 0 ≤ x) : idealPositiveProjection I x ∈ I :=
  hI.closed (idealPositiveBelow_nonempty I x hx) (fun _ hy => hy.1) (fun _ hy => hy.2.1)
    (hI.positiveBelow_directed x) (hI.positiveProjection_isLUB x hx)

theorem positiveProjection_eq_self {x : E} (hxI : x ∈ I) (hx : 0 ≤ x) :
    idealPositiveProjection I x = x :=
  le_antisymm (hI.positiveProjection_le x hx)
    ((hI.positiveProjection_isLUB x hx).1 ⟨hxI, hx, le_rfl⟩)

theorem positiveProjection_add (x y : E) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    idealPositiveProjection I (x + y) = idealPositiveProjection I x + idealPositiveProjection I y := by
  apply le_antisymm
  · apply (hI.positiveProjection_isLUB (x + y) (add_nonneg hx hy)).2
    intro z hz
    obtain ⟨u, v, hu, hux, hv, hvy, huv⟩ := riesz_split_pair hz.2.1 hx hy hz.2.2
    have huI : u ∈ I := hI.nonneg_le_mem hz.1 hu (by rw [← huv]; exact le_add_of_nonneg_right hv)
    have hvI : v ∈ I := hI.nonneg_le_mem hz.1 hv (by rw [← huv]; exact le_add_of_nonneg_left hu)
    rw [← huv]
    exact add_le_add ((hI.positiveProjection_isLUB x hx).1 ⟨huI, hu, hux⟩)
      ((hI.positiveProjection_isLUB y hy).1 ⟨hvI, hv, hvy⟩)
  · apply (hI.positiveProjection_isLUB (x + y) (add_nonneg hx hy)).1
    exact ⟨I.add_mem (hI.positiveProjection_mem x hx) (hI.positiveProjection_mem y hy),
      add_nonneg (hI.positiveProjection_nonneg x hx) (hI.positiveProjection_nonneg y hy),
      add_le_add (hI.positiveProjection_le x hx) (hI.positiveProjection_le y hy)⟩

theorem norm_positiveProjection_le [HasSolidNorm E] (x : E) (hx : 0 ≤ x) :
    ‖idealPositiveProjection I x‖ ≤ ‖x‖ := by
  apply norm_le_norm_of_abs_le_abs
  simpa only [abs_of_nonneg (hI.positiveProjection_nonneg x hx), abs_of_nonneg hx] using
    hI.positiveProjection_le x hx

end IsOrderClosedIdeal
end ThesisCommon
