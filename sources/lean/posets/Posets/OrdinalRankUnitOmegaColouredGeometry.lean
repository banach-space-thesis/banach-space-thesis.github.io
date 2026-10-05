import Posets.OrdinalRankUnitOmegaColouredCoresTail
import Posets.OrdinalRankUnitBandExtraction

/-! Concrete band geometry for powers of an arbitrary ordinal rank unit.
The lower coordinate retains all but one finite coefficient. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

variable {𝕜 : Type*} [RCLike 𝕜] {ρ : Ordinal.{u}} {hρ : Ordinal.omega0 ≤ ρ}
  {M : JLMS.AtomicDualModel 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0))}
  {T S : JLMS.CZero 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio (ordinalRankUnitOmegaBase ρ ^ Ordinal.omega0))} {N : ℕ} {ε δ : ℝ}

namespace OrdinalRankUnitOmegaColouredCores

variable (F : OrdinalRankUnitOmegaColouredCores ρ hρ M T S N ε δ)

def bandGeometry (i : ℕ) :
    OrdinalSeparatedBandCoreGeometry (F.ordinalCore i)
      (ordinalRankUnitOmegaSource ρ N (F.index i))
      (ρ * ((((F.band i).val+1) * (F.index i+2) : ℕ) : Ordinal))
      (ρ * (((F.band i).val * (F.index i+2) : ℕ) : Ordinal))
      (ρ * (((F.index i+2)-1 : ℕ) : Ordinal)) :=
  (ordinalRankUnit_exists_band_geometry ρ hρ N (F.index i+2)
    (F.band i).val (by omega) (F.band i).isLt (F.ordinalCore i)
    (F.ordinalCore_compact i) (F.ordinalCore_subset i) ⟨_, F.ordinalCore_rank i⟩).some

theorem bandGeometry_model_large (i : ℕ) :
    ordinalRankUnitOmegaBase ρ ^ ((F.index i+1 : ℕ) : Ordinal) ≤
      (F.bandGeometry i).modelOrdinal := by
  have h : (F.index i+2)-1 = F.index i+1 := by omega
  simpa only [Ordinal.opow_mul, ordinalRankUnitOmegaBase, h] using (F.bandGeometry i).model_large

theorem bandGeometry_lower_eq (i : ℕ) :
    (ordinalRankUnitOmegaBandLevels ρ N (F.index i+2) (F.band i).val).val =
      ρ * (((F.band i).val * (F.index i+2) : ℕ) : Ordinal) :=
  ordinalRankUnitOmegaBandLevels_apply_le ρ N (F.index i+2) _ (F.band i).isLt.le

theorem bandGeometry_upper_eq (i : ℕ) :
    (ordinalRankUnitOmegaBandLevels ρ N (F.index i+2) ((F.band i).val+1)).val =
      ρ * ((((F.band i).val+1) * (F.index i+2) : ℕ) : Ordinal) :=
  ordinalRankUnitOmegaBandLevels_apply_le ρ N (F.index i+2) _ (F.band i).isLt

theorem bandGeometry_cell_eq (i : ℕ) :
    (F.bandGeometry i).H = Iic (ordinalRankUnitOmegaSource ρ N (F.index i)) ∩
      {x | ordinalCeiling (ordinalTowerLevel (ordinalRankUnitOmegaSource ρ N (F.index i))
        (ordinalRankUnitOmegaBandLevels ρ N (F.index i+2) ((F.band i).val+1)).val) x =
          (F.bandGeometry i).upperPoint.val} := by
  rw [F.bandGeometry_upper_eq i]
  exact (F.bandGeometry i).cell_eq

end OrdinalRankUnitOmegaColouredCores
end Posets
