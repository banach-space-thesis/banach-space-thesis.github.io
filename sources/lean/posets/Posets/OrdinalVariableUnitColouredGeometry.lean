import Posets.OrdinalVariableUnitColouredCoresSource
import Posets.OrdinalRankUnitBandExtraction

/-! Actual separated band geometry in each selected variable-unit block.
Two copies of its rank unit provide the full one-copy target coordinate. -/

noncomputable section
open Set Topology
universe u
namespace Posets
open ThesisCommon

variable {𝕜 : Type*} [RCLike 𝕜] {γ : Ordinal.{u}} {N : ℕ}
  {P : OrdinalVariableUnitParameters γ N}
  {M : JLMS.AtomicDualModel 𝕜 (Iio (Ordinal.omega0 ^ γ))}
  {T S : JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ))} {ε δ : ℝ}

namespace OrdinalVariableUnitColouredCores

variable (F : OrdinalVariableUnitColouredCores P M T S ε δ)

def bandLevels (i : ℕ) := ordinalRankUnitOmegaBandLevels (P.sourceUnit (F.index i)) N 2

theorem bandLevels_monotone (i : ℕ) : Monotone (F.bandLevels i) :=
  ordinalRankUnitOmegaBandLevels_monotone _ _ _

def bandGeometry (i : ℕ) :
    OrdinalSeparatedBandCoreGeometry (F.ordinalCore i) (P.source (F.index i))
      (P.sourceUnit (F.index i) * ((((F.band i).val+1) * 2 : ℕ) : Ordinal))
      (P.sourceUnit (F.index i) * (((F.band i).val * 2 : ℕ) : Ordinal))
      (P.sourceUnit (F.index i) * ((2-1 : ℕ) : Ordinal)) := by
  rw [P.source_eq_rank_unit_power]
  exact (ordinalRankUnit_exists_band_geometry (P.sourceUnit (F.index i))
    (P.unit_large (F.index i+1)) N 2 (F.band i).val (by omega) (F.band i).isLt
    (F.ordinalCore i) (F.ordinalCore_compact i)
    (by simpa only [P.source_eq_rank_unit_power, ordinalRankUnitOmegaBase]
      using F.ordinalCore_subset i)
    ⟨_, F.ordinalCore_rank i⟩).some

theorem bandGeometry_model_large (i : ℕ) :
    Ordinal.omega0 ^ P.sourceUnit (F.index i) ≤ (F.bandGeometry i).modelOrdinal := by
  simpa only [show (2-1 : ℕ) = 1 by decide, Nat.cast_one, mul_one]
    using (F.bandGeometry i).model_large

theorem bandGeometry_lower_eq (i : ℕ) :
    (F.bandLevels i (F.band i).val).val =
      P.sourceUnit (F.index i) * (((F.band i).val * 2 : ℕ) : Ordinal) :=
  ordinalRankUnitOmegaBandLevels_apply_le _ N 2 _ (F.band i).isLt.le

theorem bandGeometry_upper_eq (i : ℕ) :
    (F.bandLevels i ((F.band i).val+1)).val =
      P.sourceUnit (F.index i) * ((((F.band i).val+1) * 2 : ℕ) : Ordinal) :=
  ordinalRankUnitOmegaBandLevels_apply_le _ N 2 _ (F.band i).isLt

theorem bandGeometry_cell_eq (i : ℕ) :
    (F.bandGeometry i).H = Iic (P.source (F.index i)) ∩
      {x | ordinalCeiling (ordinalTowerLevel (P.source (F.index i))
        (F.bandLevels i ((F.band i).val+1)).val) x = (F.bandGeometry i).upperPoint.val} := by
  rw [F.bandGeometry_upper_eq i]
  exact (F.bandGeometry i).cell_eq

end OrdinalVariableUnitColouredCores
end Posets
