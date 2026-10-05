import ThesisCommon.Analysis.IntervalAtomlessFiniteL1Equiv
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Nonzero atomless finite measures on any standard Borel space give the
actual Lebesgue L1 space. A Borel isomorphism transports the measure to the
interval, and the atomless interval isometry supplies the final equivalence. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem not_countable_of_atomless_measure (μ : Measure X) [NoAtoms μ] (hμ : μ ≠ 0) :
    ¬Countable X := by
  intro h
  letI := h
  exact hμ (Measure.measure_univ_eq_zero.mp ((Set.to_countable (univ : Set X)).measure_zero μ))

theorem noAtoms_map_measurableEquiv (e : X ≃ᵐ Y) (μ : Measure X) [NoAtoms μ]
    [MeasurableSingletonClass Y] : NoAtoms (μ.map e) := by
  constructor
  intro y
  rw [Measure.map_apply e.measurable (measurableSet_singleton y)]
  have he : e ⁻¹' {y} = {e.symm y} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      simpa only [e.symm_apply_apply] using congrArg e.symm h
    · intro h
      rw [h, e.apply_symm_apply]
  rw [he, measure_singleton]

def atomlessStandardBorelL1Equiv (𝕜 : Type*) [RCLike 𝕜]
    [StandardBorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [NoAtoms μ] (hμ : μ ≠ 0) :
    Lp 𝕜 1 μ ≃ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩ := by
  let e : X ≃ᵐ unitInterval := PolishSpace.measurableEquivOfNotCountable
    (not_countable_of_atomless_measure μ hμ)
    (not_countable_of_atomless_measure (volume : Measure unitInterval) (by
      exact MeasureTheory.IsProbabilityMeasure.ne_zero _))
  let ν := μ.map e
  letI : NoAtoms ν := noAtoms_map_measurableEquiv e μ
  have hν : ν ≠ 0 := (Measure.map_ne_zero_iff e.measurable.aemeasurable).mpr hμ
  exact (lpComapEquiv (𝕜 := 𝕜) μ e e.measurable e.measurableEmbedding.comap_eq 1).symm.trans
    (intervalAtomlessFiniteL1Equiv 𝕜 ν hν)

theorem exists_atomlessStandardBorelL1_equiv (𝕜 : Type*) [RCLike 𝕜]
    [StandardBorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [NoAtoms μ] (hμ : μ ≠ 0) :
    Nonempty (Lp 𝕜 1 μ ≃ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩) :=
  ⟨atomlessStandardBorelL1Equiv 𝕜 μ hμ⟩

def atomlessRestrictedL1Equiv (𝕜 : Type*) [RCLike 𝕜]
    [StandardBorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [NoAtoms μ]
    (D : Set X) (hD : 0 < μ D) :
    Lp 𝕜 1 (μ.restrict D) ≃ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩ :=
  atomlessStandardBorelL1Equiv 𝕜 (μ.restrict D) (by
    intro he
    have hz : μ D = 0 := by
      rw [← Measure.restrict_apply_univ, he]
      rfl
    exact hD.ne' hz)

end ThesisCommon
