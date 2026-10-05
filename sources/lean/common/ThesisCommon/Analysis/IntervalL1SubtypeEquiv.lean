import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Topology.Order.ProjIcc

/-! Actual isometry between subtype Lebesgue L1 and the restricted real-domain
model. Adapted from the workspace PL1/IntervalSubtype construction. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal unitInterval

namespace ThesisCommon.IntervalL1Subtype

def clamp : ℝ → unitInterval := Set.projIcc 0 1 zero_le_one

theorem clamp_coe (x : unitInterval) : clamp (x : ℝ) = x :=
  Set.projIcc_of_mem zero_le_one x.property

theorem measurePreserving_clamp :
    MeasurePreserving clamp (volume.restrict (Icc (0 : ℝ) 1)) (volume : Measure unitInterval) where
  measurable := continuous_projIcc.measurable
  map_eq := by
    change Measure.map clamp (volume.restrict (Icc (0 : ℝ) 1)) = _
    rw [← unitInterval.measurePreserving_coe.map_eq,
      Measure.map_map (show Measurable clamp from continuous_projIcc.measurable)
        measurable_subtype_coe]
    have h : clamp ∘ ((↑) : unitInterval → ℝ) = id := funext clamp_coe
    rw [h, Measure.map_id]

variable (K : Type*) [RCLike K]

/-- Extend a subtype function using the interval clamp; values outside the interval are ignored. -/
def toInterval : Lp K 1 (volume : Measure unitInterval) →ₗᵢ[K] IntervalLp K ⟨1, le_rfl⟩ :=
  Lp.compMeasurePreservingₗᵢ K clamp measurePreserving_clamp

/-- Restrict the actual real-domain L1 class to the interval subtype. -/
def fromInterval : IntervalLp K ⟨1, le_rfl⟩ →ₗᵢ[K] Lp K 1 (volume : Measure unitInterval) :=
  Lp.compMeasurePreservingₗᵢ K ((↑) : unitInterval → ℝ) unitInterval.measurePreserving_coe

theorem toInterval_fromInterval (f : IntervalLp K ⟨1, le_rfl⟩) :
    toInterval K (fromInterval K f) = f := by
  apply Lp.ext
  have hfrom := measurePreserving_clamp.quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving f unitInterval.measurePreserving_coe)
  filter_upwards [Lp.coeFn_compMeasurePreserving (fromInterval K f) measurePreserving_clamp,
    hfrom, ae_restrict_mem measurableSet_Icc] with x hto hf hx
  change toInterval K (fromInterval K f) x = _ at hto ⊢
  rw [hto]
  change fromInterval K f (clamp x) = f x
  change fromInterval K f (clamp x) = f (clamp x : ℝ) at hf
  rw [hf]
  rw [clamp, Set.projIcc_of_mem zero_le_one hx]

/-- The actual isometric identification, oriented from subtype L1 to the reviewed IntervalL1. -/
def equiv : Lp K 1 (volume : Measure unitInterval) ≃ₗᵢ[K] IntervalLp K ⟨1, le_rfl⟩ :=
  LinearIsometryEquiv.ofSurjective (toInterval K)
    (fun f => ⟨fromInterval K f, toInterval_fromInterval K f⟩)

theorem equiv_apply (f : Lp K 1 (volume : Measure unitInterval)) :
    equiv K f = toInterval K f := rfl

end ThesisCommon.IntervalL1Subtype

