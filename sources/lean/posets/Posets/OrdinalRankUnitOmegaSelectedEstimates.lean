import Posets.OrdinalRankUnitOmegaSelectedGeometry
import Posets.OrdinalClosedCopySeparatedAmbientCells

/-! Estimates on the original coloured leaves of the selected cells.
The lower cell and its indicator are the ones used by the global operator. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

variable {𝕜 : Type*} [RCLike 𝕜] {ρ : Ordinal.{u}} {hρ : Ordinal.omega0 ≤ ρ}
  {M : JLMS.AtomicDualModel 𝕜 (Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0))}
  {T S : JLMS.CZero 𝕜 (Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0))} {N : ℕ} {ε δ : ℝ}

namespace OrdinalRankUnitOmegaColouredCores

variable (F : OrdinalRankUnitOmegaColouredCores ρ hρ M T S N ε δ)

theorem selected_leaf_estimates (i : ℕ) {y : Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0)}
    (hy : y ∈ F.selectedLeaves i) :
    ∃ hV : IsClopen (F.selectedV i y), ∃ hcV : IsCompact (F.selectedV i y),
      F.selectedV i y ⊆ F.selectedH i ∧
      wolfeMass M (wolfeOperatorRow (if F.colour then T else S) y)
        (F.selectedH i \ F.selectedV i y) < ε ∧
      (1 / 2 : ℝ) ≤ ‖(if F.colour then T else S)
        (JLMS.clopenIndicator (F.selectedV i y) hV hcV) y‖ := by
  have hy' := hy
  rw [F.selectedLeaves_upper_image i] at hy'
  have h := ordinalAmbientBandLeaf_image_estimates
    (ordinalRankUnitOmegaSource_top_level ρ hρ N (F.index i))
    (ordinalRankUnitOmegaSourceEmbedding ρ hρ N (F.index i))
    (ordinalRankUnitOmegaSourceEmbedding_isOpen ρ hρ N (F.index i)) M T S
    (ordinalRankUnitOmegaBandLevels ρ N (F.index i+2))
    (ordinalRankUnitOmegaBandLevels_monotone ρ N (F.index i+2))
    (F.band i).val F.colour ε (F.bandGeometry i).upperPoint.val hy'
  dsimp only at h
  rw [← F.selectedH_upper_cell i] at h
  exact h

theorem selectedV_clopen (i : ℕ) (y : Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0))
    (hy : y ∈ F.selectedLeaves i) : IsClopen (F.selectedV i y) :=
  (F.selected_leaf_estimates i hy).choose

theorem selectedV_compact (i : ℕ) (y : Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0))
    (hy : y ∈ F.selectedLeaves i) : IsCompact (F.selectedV i y) :=
  (F.selected_leaf_estimates i hy).choose_spec.choose

theorem selectedV_subset (i : ℕ) (y : Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0))
    (hy : y ∈ F.selectedLeaves i) : F.selectedV i y ⊆ F.selectedH i :=
  (F.selected_leaf_estimates i hy).choose_spec.choose_spec.1

theorem selected_leaf_restriction_mass (i : ℕ) (y : Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0))
    (hy : y ∈ F.selectedLeaves i) :
    ‖JLMS.atomicRestriction M (F.selectedH i \ F.selectedV i y)
      ((JLMS.evaluation y).comp (if F.colour then T else S))‖ ≤ ε := by
  exact (F.selected_leaf_estimates i hy).choose_spec.choose_spec.2.1.le

theorem selected_leaf_diagonal (i : ℕ) (y : Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0))
    (hy : y ∈ F.selectedLeaves i) :
    (1 / 2 : ℝ) ≤ ‖(if F.colour then T else S)
      (JLMS.clopenIndicator (F.selectedV i y) (F.selectedV_clopen i y hy)
        (F.selectedV_compact i y hy)) y‖ :=
  (F.selected_leaf_estimates i hy).choose_spec.choose_spec.2.2

theorem selectedP_constant_on_V (i : ℕ) (y : Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0))
    (hy : y ∈ F.selectedLeaves i) (z : Iio ((ordinalRankUnitOmegaBase ρ) ^ Ordinal.omega0))
    (hz : z ∈ F.selectedV i y) :
    F.selectedP i ⟨z, F.selectedV_subset i y hy hz⟩ =
      F.selectedP i ⟨y, F.selectedLeaves_subset i hy⟩ := by
  apply ordinalOmegaPrefixCoordinate_constant
  apply Eq.symm
  apply ordinalSeparatedBandAmbientCoordinate_constant_on_ceilingCellAt
  change z ∈ ordinalAmbientCeilingCellAt
    (ordinalRankUnitOmegaSourceEmbedding ρ hρ N (F.index i))
    (ρ * (((F.band i).val * (F.index i+2) : ℕ) : Ordinal)) y
  rw [← F.bandGeometry_lower_eq i]
  exact hz

end OrdinalRankUnitOmegaColouredCores
end Posets


