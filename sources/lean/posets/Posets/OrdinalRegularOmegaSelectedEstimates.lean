import Posets.OrdinalRegularOmegaSelectedGeometry
import Posets.OrdinalClosedCopyAmbientCells

/-! Estimates on the original coloured leaves of the actual selected cells.
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

variable (F : OrdinalRegularOmegaColouredCores c hc M T S N ε δ) (hr : c.IsRegular)

theorem selected_leaf_estimates (i : ℕ) {y : Iio (c.ord ^ Ordinal.omega0)}
    (hy : y ∈ F.selectedLeaves hr i) :
    ∃ hV : IsClopen (F.selectedV i y), ∃ hcV : IsCompact (F.selectedV i y),
      F.selectedV i y ⊆ F.selectedH hr i ∧
      wolfeMass M (wolfeOperatorRow (if F.colour then T else S) y)
        (F.selectedH hr i \ F.selectedV i y) < ε ∧
      (1 / 2 : ℝ) ≤ ‖(if F.colour then T else S)
        (JLMS.clopenIndicator (F.selectedV i y) hV hcV) y‖ := by
  have hy' := hy
  rw [F.selectedLeaves_upper_image hr i] at hy'
  have h := ordinalAmbientBandLeaf_image_estimates
    (ordinalRegularOmegaSource_top_level c hc N (F.index i))
    (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
    (ordinalRegularOmegaSourceEmbedding_isOpen c hc N (F.index i)) M T S
    (ordinalRegularOmegaBandLevels c N (F.index i+2))
    (ordinalRegularOmegaBandLevels_monotone c N (F.index i+2))
    (F.band i).val F.colour ε (F.bandGeometry hr i).upperPoint.val hy'
  dsimp only at h
  rw [← F.selectedH_upper_cell hr i] at h
  exact h

theorem selectedV_clopen (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0))
    (hy : y ∈ F.selectedLeaves hr i) : IsClopen (F.selectedV i y) :=
  (F.selected_leaf_estimates hr i hy).choose

theorem selectedV_compact (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0))
    (hy : y ∈ F.selectedLeaves hr i) : IsCompact (F.selectedV i y) :=
  (F.selected_leaf_estimates hr i hy).choose_spec.choose

theorem selectedV_subset (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0))
    (hy : y ∈ F.selectedLeaves hr i) : F.selectedV i y ⊆ F.selectedH hr i :=
  (F.selected_leaf_estimates hr i hy).choose_spec.choose_spec.1

theorem selected_leaf_restriction_mass (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0))
    (hy : y ∈ F.selectedLeaves hr i) :
    ‖JLMS.atomicRestriction M (F.selectedH hr i \ F.selectedV i y)
      ((JLMS.evaluation y).comp (if F.colour then T else S))‖ ≤ ε := by
  exact (F.selected_leaf_estimates hr i hy).choose_spec.choose_spec.2.1.le

theorem selected_leaf_diagonal (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0))
    (hy : y ∈ F.selectedLeaves hr i) :
    (1 / 2 : ℝ) ≤ ‖(if F.colour then T else S)
      (JLMS.clopenIndicator (F.selectedV i y) (F.selectedV_clopen hr i y hy)
        (F.selectedV_compact hr i y hy)) y‖ :=
  (F.selected_leaf_estimates hr i hy).choose_spec.choose_spec.2.2

theorem selectedP_constant_on_selectedV (i : ℕ) (y : Iio (c.ord ^ Ordinal.omega0))
    (hy : y ∈ F.selectedLeaves hr i) (z : Iio (c.ord ^ Ordinal.omega0))
    (hz : z ∈ F.selectedV i y) :
    F.selectedP hr i ⟨z, F.selectedV_subset hr i y hy hz⟩ =
      F.selectedP hr i ⟨y, F.selectedLeaves_subset hr i hy⟩ := by
  apply ordinalOmegaPrefixCoordinate_constant
  apply Eq.symm
  apply ordinalBandAmbientCoordinate_constant_on_ceilingCellAt
  change z ∈ ordinalAmbientCeilingCellAt
    (ordinalRegularOmegaSourceEmbedding c hc N (F.index i))
    (c.ord * (((F.band i).val * (F.index i+2) : ℕ) : Ordinal)) y
  rw [← F.bandGeometry_lower_eq i]
  exact hz

end OrdinalRegularOmegaColouredCores
end Posets
