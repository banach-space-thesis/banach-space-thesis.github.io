import Posets.OrdinalOmegaSelectedGeometry
import Posets.OrdinalClosedCopySeparatedAmbientCells

/-! Estimates on the original coloured leaves of the selected cells.
The lower cell and its indicator are the ones used by the global operator. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

variable {𝕜 : Type*} [RCLike 𝕜] {c : Cardinal.{u}} {hc : Cardinal.aleph0 < c}
  {M : JLMS.AtomicDualModel 𝕜 (Iio (c.ord ^ Ordinal.omega0))}
  {T S : JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0))} {N : ℕ} {ε δ : ℝ}

namespace OrdinalRegularOmegaColouredCores

variable (F : OrdinalRegularOmegaColouredCores c hc M T S N ε δ)

theorem lossSelected_leaf_estimates (i : ℕ) {y : Iio (c.ord ^ Ordinal.omega0)}
    (hy : y ∈ F.lossSelectedLeaves i) :
    ∃ hV : IsClopen (F.lossSelectedV i y), ∃ hcV : IsCompact (F.lossSelectedV i y),
      F.lossSelectedV i y ⊆ F.lossSelectedH i ∧
      wolfeMass M (wolfeOperatorRow (if F.colour then T else S) y)
        (F.lossSelectedH i \ F.lossSelectedV i y) < ε ∧
      (1 / 2 : ℝ) ≤ ‖(if F.colour then T else S)
        (JLMS.clopenIndicator (F.lossSelectedV i y) hV hcV) y‖ := by
  have hy' := hy
  rw [F.lossSelectedLeaves_upper_image i] at hy'
  have h := ordinalAmbientBandLeaf_image_estimates
    (ordinalRegularOmegaSource_top_level c hc N (F.index i))
    (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
    (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)) M T S
    (ordinalRegularOmegaBandLevels c N (F.index i+2))
    (ordinalRegularOmegaBandLevels_monotone c N (F.index i+2))
    (F.band i).val F.colour ε (F.lossGeometry i).upperPoint.val hy'
  dsimp only at h
  rw [← F.lossSelectedH_upper_cell i] at h
  exact h

theorem lossSelectedV_clopen (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0))
    (hy : y ∈ F.lossSelectedLeaves i) : IsClopen (F.lossSelectedV i y) :=
  (F.lossSelected_leaf_estimates i hy).choose

theorem lossSelectedV_compact (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0))
    (hy : y ∈ F.lossSelectedLeaves i) : IsCompact (F.lossSelectedV i y) :=
  (F.lossSelected_leaf_estimates i hy).choose_spec.choose

theorem lossSelectedV_subset (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0))
    (hy : y ∈ F.lossSelectedLeaves i) : F.lossSelectedV i y ⊆ F.lossSelectedH i :=
  (F.lossSelected_leaf_estimates i hy).choose_spec.choose_spec.1

theorem lossSelected_leaf_restriction_mass (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0))
    (hy : y ∈ F.lossSelectedLeaves i) :
    ‖JLMS.atomicRestriction M (F.lossSelectedH i \ F.lossSelectedV i y)
      ((JLMS.evaluation y).comp (if F.colour then T else S))‖ ≤ ε := by
  exact (F.lossSelected_leaf_estimates i hy).choose_spec.choose_spec.2.1.le

theorem lossSelected_leaf_diagonal (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0))
    (hy : y ∈ F.lossSelectedLeaves i) :
    (1 / 2 : ℝ) ≤ ‖(if F.colour then T else S)
      (JLMS.clopenIndicator (F.lossSelectedV i y) (F.lossSelectedV_clopen i y hy)
        (F.lossSelectedV_compact i y hy)) y‖ :=
  (F.lossSelected_leaf_estimates i hy).choose_spec.choose_spec.2.2

theorem lossSelectedP_constant_on_V (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0))
    (hy : y ∈ F.lossSelectedLeaves i) (z : Iio (c.ord ^ Ordinal.omega0))
    (hz : z ∈ F.lossSelectedV i y) :
    F.lossSelectedP i ⟨z, F.lossSelectedV_subset i y hy hz⟩ =
      F.lossSelectedP i ⟨y, F.lossSelectedLeaves_subset i hy⟩ := by
  apply ordinalOmegaPrefixCoordinate_constant
  apply Eq.symm
  apply ordinalSeparatedBandAmbientCoordinate_constant_on_ceilingCellAt
  change z ∈ ordinalAmbientCeilingCellAt
    (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
    (c.ord * (((F.band i).val * (F.index i+2) : ℕ) : Ordinal)) y
  rw [← F.lossGeometry_lower_eq i]
  exact hz

end OrdinalRegularOmegaColouredCores
end Posets

