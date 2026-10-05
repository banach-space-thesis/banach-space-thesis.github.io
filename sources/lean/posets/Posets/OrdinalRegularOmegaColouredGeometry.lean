import Posets.OrdinalRegularOmegaColouredCoresSource
import Posets.OrdinalRegularOmegaBandExtraction

/-! Actual upper cells, lower-image ordinal models and continuous reading
sections extracted from every selected coloured core. -/

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

def bandGeometry (hr : c.IsRegular) (i : ℕ) :
    OrdinalBandCoreGeometry (F.ordinalCore i) (ordinalRegularOmegaSource c N (F.index i))
      (c.ord * (((F.band i).val * (F.index i+2) : ℕ) : Ordinal))
      (c.ord * ((F.index i+2 : ℕ) : Ordinal)) :=
  (ordinalRegularOmega_exists_band_geometry hr hc N (F.index i+2) (F.band i).val
    (by omega) (F.band i).isLt (F.ordinalCore i) (F.ordinalCore_compact i)
    (F.ordinalCore_subset i) ⟨_, F.ordinalCore_rank i⟩).some

theorem bandGeometry_model_large (hr : c.IsRegular) (i : ℕ) :
    c.ord ^ ((F.index i+2 : ℕ) : Ordinal) ≤ (F.bandGeometry hr i).modelOrdinal := by
  simpa only [ordinal_uncountable_initial_power_rank hc] using (F.bandGeometry hr i).model_large

theorem bandGeometry_lower_eq (i : ℕ) :
    (ordinalRegularOmegaBandLevels c N (F.index i+2) (F.band i).val).val =
      c.ord * (((F.band i).val * (F.index i+2) : ℕ) : Ordinal) :=
  ordinalRegularOmegaBandLevels_apply_le c N (F.index i+2) _ (F.band i).isLt.le

theorem bandGeometry_upper_eq (i : ℕ) :
    (ordinalRegularOmegaBandLevels c N (F.index i+2) ((F.band i).val+1)).val =
      c.ord * (((F.band i).val * (F.index i+2) : ℕ) : Ordinal) +
        c.ord * ((F.index i+2 : ℕ) : Ordinal) := by
  rw [← ordinalRegularOmegaBandLevels_gap c N (F.index i+2) _ (F.band i).isLt,
    F.bandGeometry_lower_eq i]

theorem bandGeometry_cell_eq (hr : c.IsRegular) (i : ℕ) :
    (F.bandGeometry hr i).H = Iic (ordinalRegularOmegaSource c N (F.index i)) ∩
      {x | ordinalCeiling (ordinalTowerLevel (ordinalRegularOmegaSource c N (F.index i))
        (ordinalRegularOmegaBandLevels c N (F.index i+2) ((F.band i).val+1)).val) x =
          (F.bandGeometry hr i).upperPoint.val} := by
  rw [F.bandGeometry_upper_eq i]
  exact (F.bandGeometry hr i).cell_eq

end OrdinalRegularOmegaColouredCores
end Posets
