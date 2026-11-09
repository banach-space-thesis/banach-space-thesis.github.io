import NonCalkinAlgebra.CompactSpectral
import NonCalkinAlgebra.QuotientConventionReduction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open Module
universe v
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem eigenspace_isClosed (T : X →L[ℂ] X) (μ : ℂ) :
    IsClosed (Module.End.eigenspace (T : End ℂ X) μ : Set X) := by
  rw [Module.End.eigenspace_def]
  exact ContinuousLinearMap.isClosed_ker (T - μ • 1)

/-- Each nonzero eigenspace of a compact operator is finite-dimensional.
The proof restricts the actual compact operator to its closed eigenspace,
where multiplication by μ⁻¹ makes it the identity, and applies Riesz's theorem. -/
theorem compact_eigenspace_finiteDimensional (T : X →L[ℂ] X)
    (hT : IsCompactOperator T) (μ : ℂ) (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (Module.End.eigenspace (T : End ℂ X) μ) := by
  let V := Module.End.eigenspace (T : End ℂ X) μ
  have hVclosed : IsClosed (V : Set X) := eigenspace_isClosed T μ
  letI : CompleteSpace V := hVclosed.completeSpace_coe
  have hmaps : ∀ x : V, T x ∈ V := by
    intro x
    apply Module.End.mem_eigenspace_iff.mpr
    change T (T x.val) = μ • T x.val
    have hx : T x.val = μ • x.val := Module.End.mem_eigenspace_iff.mp x.property
    calc
      T (T x.val) = T (μ • x.val) := congrArg T hx
      _ = μ • T x.val := T.map_smul μ x.val
  let S : V →L[ℂ] V := (T.comp V.subtypeL).codRestrict V hmaps
  have hS : IsCompactOperator S := (hT.comp_clm V.subtypeL).codRestrict hmaps hVclosed
  have heq : μ⁻¹ • S = (1 : V →L[ℂ] V) := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change μ⁻¹ • T x.val = x.val
    have hx : T x.val = μ • x.val := Module.End.mem_eigenspace_iff.mp x.property
    rw [hx, inv_smul_smul₀ hμ]
  have hid : IsCompactOperator (1 : V →L[ℂ] V) := by
    rw [← heq]
    exact hS.smul μ⁻¹
  exact finiteDimensional_of_compact_identity V hid

end NonCalkinAlgebra
