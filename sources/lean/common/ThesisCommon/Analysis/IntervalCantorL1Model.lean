import ThesisCommon.Analysis.AtomlessStandardBorelL1Equiv

/-! An actual atomless probability measure on compact Cantor space whose
L1 space is linearly isometric to Lebesgue L1 on the unit interval. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon

def intervalCantorBorelEquiv : unitInterval ≃ᵐ (ℕ → Bool) :=
  PolishSpace.measurableEquivNatBoolOfNotCountable
    (not_countable_of_atomless_measure (volume : Measure unitInterval)
      (MeasureTheory.IsProbabilityMeasure.ne_zero _))

def intervalCantorMeasure : Measure (ℕ → Bool) :=
  (volume : Measure unitInterval).map intervalCantorBorelEquiv

instance intervalCantorMeasure_isProbability : IsProbabilityMeasure intervalCantorMeasure :=
  Measure.isProbabilityMeasure_map intervalCantorBorelEquiv.measurable.aemeasurable

instance intervalCantorMeasure_noAtoms : NoAtoms intervalCantorMeasure :=
  noAtoms_map_measurableEquiv intervalCantorBorelEquiv volume

def intervalCantorL1Equiv (𝕜 : Type*) [RCLike 𝕜] :
    Lp 𝕜 1 intervalCantorMeasure ≃ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩ :=
  (lpComapEquiv (𝕜 := 𝕜) volume intervalCantorBorelEquiv
    intervalCantorBorelEquiv.measurable intervalCantorBorelEquiv.measurableEmbedding.comap_eq 1).trans
    (IntervalL1Subtype.equiv 𝕜)

def intervalCantorRestrictedL1Equiv (𝕜 : Type*) [RCLike 𝕜]
    (D : Set (ℕ → Bool)) (hD : 0 < intervalCantorMeasure D) :
    Lp 𝕜 1 (intervalCantorMeasure.restrict D) ≃ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩ :=
  atomlessRestrictedL1Equiv 𝕜 intervalCantorMeasure D hD

end ThesisCommon
