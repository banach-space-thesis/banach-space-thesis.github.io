import ThesisCommon.Analysis.MeasureAlgebraBandSides
import ThesisCommon.Analysis.IntegralKernelMeasureAlgebraSides

/-! Lemma 4.3: both arbitrary measure-algebra transport clauses, including
singularity, an actual jointly measurable kernel and equality of the
actual truncated operators. Countable generation belongs only to the
original spaces. Replacement finiteness is derived from the isomorphisms. -/
noncomputable section
open MeasureTheory MeasurableSpace ThesisCommon
namespace PEMS
variable {X Y X' Y' : Type*}
variable [MeasurableSpace X] [MeasurableSpace Y]
variable [MeasurableSpace X'] [MeasurableSpace Y']
variable {μ : Measure X} {ν : Measure Y}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable [CountablyGenerated X] [CountablyGenerated Y]

/-- The real-kernel formulation of both clauses of Lemma 4.3. The source
Definition 3.11 specifies real kernels. Each clause uses the same transported
kernel at every threshold; its integral representation is not assumed. -/
def Lemma_4_3 (μ' : Measure X') (ν' : Measure Y')
    (Φ : MeasureAlgebraIso μ' μ) (Ψ : MeasureAlgebraIso ν ν')
    (S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (k : X × Y → ℝ) : Prop :=
  letI := Φ.symm.isFiniteMeasure_of_source
  letI := Ψ.isFiniteMeasure_of_source
  IsSingularOperator S → ∀ hk : IsIntegralKernel k K,
    (IsSingularOperator (S.comp Φ.lOneEquiv.toLinearIsometry.toContinuousLinearMap) ∧
      ∃ (h : X' × Y → ℝ)
        (hh : IsIntegralKernel h (K.comp Φ.lOneEquiv.toLinearIsometry.toContinuousLinearMap)),
        ∀ r : ℝ, hh.truncatedOperator r =
          (hk.truncatedOperator r).comp Φ.lOneEquiv.toLinearIsometry.toContinuousLinearMap) ∧
    (IsSingularOperator (Ψ.lOneEquiv.toLinearIsometry.toContinuousLinearMap.comp S) ∧
      ∃ (h : X × Y' → ℝ)
        (hh : IsIntegralKernel h (Ψ.lOneEquiv.toLinearIsometry.toContinuousLinearMap.comp K)),
        ∀ r : ℝ, hh.truncatedOperator r =
          Ψ.lOneEquiv.toLinearIsometry.toContinuousLinearMap.comp (hk.truncatedOperator r))

theorem lemma_4_3_proof (μ' : Measure X') (ν' : Measure Y')
    (Φ : MeasureAlgebraIso μ' μ) (Ψ : MeasureAlgebraIso ν ν')
    (S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (k : X × Y → ℝ) :
    Lemma_4_3 μ' ν' Φ Ψ S K k := by
  letI := Φ.symm.isFiniteMeasure_of_source
  letI := Ψ.isFiniteMeasure_of_source
  intro hS hk
  exact ⟨⟨hS.measureAlgebra_precomp Φ, hk.exists_measureAlgebra_precomp Φ⟩,
    ⟨hS.measureAlgebra_postcomp Ψ, hk.exists_measureAlgebra_postcomp Ψ⟩⟩

end PEMS
