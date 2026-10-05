import ThesisCommon.Analysis.BandProjectionPositive
import Mathlib.LinearAlgebra.Projection

/-! The actual contractive linear band projection and its disjoint residual,
constructed from order closure in a Dedekind complete normed lattice. -/
noncomputable section
open Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]
variable {I : Submodule ℝ E}

def bandProjection (hI : IsOrderClosedIdeal I) : E →L[ℝ] E :=
  positiveConeExtension (fun x _ => idealPositiveProjection I x)
    (fun x y hx hy => hI.positiveProjection_add x y hx hy) zero_le_one
    (fun x hx => by simpa only [one_mul] using hI.norm_positiveProjection_le x hx)

namespace IsOrderClosedIdeal
variable (hI : IsOrderClosedIdeal I)

theorem bandProjection_apply_of_nonneg (x : E) (hx : 0 ≤ x) :
    bandProjection hI x = idealPositiveProjection I x :=
  positiveConeExtension_apply_of_nonneg _ _ _ _ x hx

theorem bandProjection_apply (x : E) : bandProjection hI x =
    idealPositiveProjection I x⁺ - idealPositiveProjection I x⁻ := rfl

theorem bandProjection_nonneg : 0 ≤ bandProjection hI := by
  intro x hx
  change 0 ≤ bandProjection hI x
  rw [hI.bandProjection_apply_of_nonneg x hx]
  exact hI.positiveProjection_nonneg x hx

theorem bandProjection_le_id : bandProjection hI ≤ ContinuousLinearMap.id ℝ E := by
  intro x hx
  change bandProjection hI x ≤ x
  rw [hI.bandProjection_apply_of_nonneg x hx]
  exact hI.positiveProjection_le x hx

theorem bandProjection_mem (x : E) : bandProjection hI x ∈ I := by
  rw [hI.bandProjection_apply]
  exact I.sub_mem (hI.positiveProjection_mem x⁺ (posPart_nonneg x))
    (hI.positiveProjection_mem x⁻ (negPart_nonneg x))

theorem bandProjection_eq_self {x : E} (hx : x ∈ I) : bandProjection hI x = x := by
  rw [hI.bandProjection_apply,
    hI.positiveProjection_eq_self (hI.posPart_mem hx) (posPart_nonneg x),
    hI.positiveProjection_eq_self (hI.negPart_mem hx) (negPart_nonneg x), posPart_sub_negPart]

theorem bandProjection_idempotent (x : E) : bandProjection hI (bandProjection hI x) = bandProjection hI x :=
  hI.bandProjection_eq_self (hI.bandProjection_mem x)

end IsOrderClosedIdeal

omit [HasSolidNorm E] in
theorem abs_apply_le_of_positive {T : E →L[ℝ] E} (hT : 0 ≤ T) (x : E) : |T x| ≤ T |x| := by
  change T x ⊔ -T x ≤ T |x|
  apply sup_le
  · exact positive_operator_monotone hT (le_abs_self x)
  · have h := positive_operator_monotone hT (show -x ≤ |x| from le_sup_right)
    simpa only [map_neg] using h

namespace IsOrderClosedIdeal
variable (hI : IsOrderClosedIdeal I)
include hI

theorem abs_bandProjection_le (x : E) : |bandProjection hI x| ≤ |x| :=
  (abs_apply_le_of_positive hI.bandProjection_nonneg x).trans (hI.bandProjection_le_id |x| (abs_nonneg x))

theorem norm_bandProjection_le_one : ‖bandProjection hI‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using norm_le_norm_of_abs_le_abs (hI.abs_bandProjection_le x)

theorem le_residual_eq_zero {x y : E} (hx : 0 ≤ x) (hyI : y ∈ I)
    (hy : 0 ≤ y) (hyx : y ≤ x - bandProjection hI x) : y = 0 := by
  have hsum : bandProjection hI x + y ∈ idealPositiveBelow I x := by
    refine ⟨I.add_mem (hI.bandProjection_mem x) hyI,
      add_nonneg (hI.bandProjection_nonneg x hx) hy, ?_⟩
    simpa only [add_comm] using le_sub_iff_add_le.mp hyx
  have hle := (hI.positiveProjection_isLUB x hx).1 hsum
  rw [← hI.bandProjection_apply_of_nonneg x hx] at hle
  exact le_antisymm (by simpa only [add_le_iff_nonpos_right] using hle) hy

theorem residual_disjoint (x : E) {y : E} (hy : y ∈ I) :
    |x - bandProjection hI x| ⊓ |y| = 0 := by
  let R : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - bandProjection hI
  have hR : 0 ≤ R := sub_nonneg.mpr hI.bandProjection_le_id
  have hle : |x - bandProjection hI x| ≤ |x| - bandProjection hI |x| :=
    abs_apply_le_of_positive hR x
  exact hI.le_residual_eq_zero (abs_nonneg x)
    (hI.nonneg_le_mem (hI.abs_mem hy) (le_inf (abs_nonneg _) (abs_nonneg _)) inf_le_right)
    (le_inf (abs_nonneg _) (abs_nonneg _)) (inf_le_left.trans hle)

theorem bandProjection_eq_zero_iff (x : E) : bandProjection hI x = 0 ↔ ∀ y ∈ I, |x| ⊓ |y| = 0 := by
  constructor
  · intro hx y hy
    simpa only [hx, sub_zero] using hI.residual_disjoint x hy
  · intro hx
    have hz := hx (bandProjection hI x) (hI.bandProjection_mem x)
    rw [inf_eq_right.mpr (hI.abs_bandProjection_le x)] at hz
    apply norm_eq_zero.mp
    rw [← norm_abs_eq_norm, hz, norm_zero]

theorem bandProjection_isProj : LinearMap.IsProj I (bandProjection hI).toLinearMap :=
  ⟨hI.bandProjection_mem, fun _ hx => hI.bandProjection_eq_self hx⟩

theorem bandProjection_isCompl : IsCompl I (LinearMap.ker (bandProjection hI).toLinearMap) :=
  hI.bandProjection_isProj.isCompl

theorem exists_unique_band_decomposition (x : E) :
    ∃! p : E × E, p.1 ∈ I ∧ (∀ y ∈ I, |p.2| ⊓ |y| = 0) ∧ x = p.1 + p.2 := by
  refine ⟨(bandProjection hI x, x - bandProjection hI x),
    ⟨hI.bandProjection_mem x, fun _ hy => hI.residual_disjoint x hy, by dsimp; abel⟩, ?_⟩
  intro p hp
  have hpzero := (hI.bandProjection_eq_zero_iff p.2).mpr hp.2.1
  have hfirst : bandProjection hI x = p.1 := by
    rw [hp.2.2, map_add, hI.bandProjection_eq_self hp.1, hpzero, add_zero]
  apply Prod.ext
  · exact hfirst.symm
  · dsimp
    rw [hfirst, hp.2.2]
    abel

end IsOrderClosedIdeal
end ThesisCommon
