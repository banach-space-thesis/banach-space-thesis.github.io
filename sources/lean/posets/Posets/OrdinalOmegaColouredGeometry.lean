import Posets.OrdinalOmegaColouredCoresTail
import Posets.OrdinalInitialOmegaBandExtraction

/-! Concrete band geometry for arbitrary uncountable initial ordinals.
The lower coordinate retains all but one of the finite power exponents. -/

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

def lossGeometry (i : ℕ) :
    OrdinalSeparatedBandCoreGeometry (F.ordinalCore i)
      (ordinalRegularOmegaSource c N (F.index i))
      (c.ord * ((((F.band i).val+1) * (F.index i+2) : ℕ) : Ordinal))
      (c.ord * (((F.band i).val * (F.index i+2) : ℕ) : Ordinal))
      (c.ord * (((F.index i+2)-1 : ℕ) : Ordinal)) :=
  (ordinalInitialOmega_exists_band_geometry_height_loss hc N (F.index i+2)
    (F.band i).val (by omega) (F.band i).isLt (F.ordinalCore i)
    (F.ordinalCore_compact i) (F.ordinalCore_subset i) ⟨_, F.ordinalCore_rank i⟩).some

theorem lossGeometry_model_large (i : ℕ) :
    c.ord ^ ((F.index i+1 : ℕ) : Ordinal) ≤ (F.lossGeometry i).modelOrdinal := by
  have h : (F.index i+2)-1 = F.index i+1 := by omega
  simpa only [ordinal_uncountable_initial_power_rank hc, h] using (F.lossGeometry i).model_large

theorem lossGeometry_lower_eq (i : ℕ) :
    (ordinalRegularOmegaBandLevels c N (F.index i+2) (F.band i).val).val =
      c.ord * (((F.band i).val * (F.index i+2) : ℕ) : Ordinal) :=
  ordinalRegularOmegaBandLevels_apply_le c N (F.index i+2) _ (F.band i).isLt.le

theorem lossGeometry_upper_eq (i : ℕ) :
    (ordinalRegularOmegaBandLevels c N (F.index i+2) ((F.band i).val+1)).val =
      c.ord * ((((F.band i).val+1) * (F.index i+2) : ℕ) : Ordinal) :=
  ordinalRegularOmegaBandLevels_apply_le c N (F.index i+2) _ (F.band i).isLt

theorem lossGeometry_cell_eq (i : ℕ) :
    (F.lossGeometry i).H = Iic (ordinalRegularOmegaSource c N (F.index i)) ∩
      {x | ordinalCeiling (ordinalTowerLevel (ordinalRegularOmegaSource c N (F.index i))
        (ordinalRegularOmegaBandLevels c N (F.index i+2) ((F.band i).val+1)).val) x =
          (F.lossGeometry i).upperPoint.val} := by
  rw [F.lossGeometry_upper_eq i]
  exact (F.lossGeometry i).cell_eq

end OrdinalRegularOmegaColouredCores
end Posets
