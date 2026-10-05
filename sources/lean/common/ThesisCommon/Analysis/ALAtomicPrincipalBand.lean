import ThesisCommon.Analysis.ALPrincipalFragmentDensity
import ThesisCommon.Analysis.ALAtomicRepresentationAtoms
import ThesisCommon.Analysis.ALFragmentNormalization
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The actual principal band of a positive atom is one dimensional.
Its normalized positive generator gives an onto scalar linear isometry. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [HasSolidNorm E] [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)

include hAL in
theorem principalBand_eq_span_of_positive_atom {e : E} (he : IsPositiveLatticeAtom e) :
    principalBand e = Submodule.span ℝ {e} := by
  apply le_antisymm
  · rw [← positiveFragmentSpan_closure_eq_principalBand hAL he.1]
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro x hx
      obtain ⟨r, _, hr⟩ := he.2.2 x hx.1 hx.2.1
      exact Submodule.mem_span_singleton.mpr ⟨r, hr.symm⟩
    · exact (Submodule.span ℝ ({e} : Set E)).closed_of_finiteDimensional
  · apply Submodule.span_le.mpr
    intro x hx
    simpa only [Set.mem_singleton_iff.mp hx] using (self_mem_principalBand e)

def positiveAtomScalarIsometry {e : E} (he : IsPositiveLatticeAtom e) :
    ℝ →ₗᵢ[ℝ] principalBand e where
  toLinearMap := LinearMap.toSpanSingleton ℝ (principalBand e)
    ⟨normalizedPositiveVector e, (principalBand e).smul_mem _ (self_mem_principalBand e)⟩
  norm_map' r := by
    change ‖r • normalizedPositiveVector e‖ = ‖r‖
    rw [norm_smul, norm_normalizedPositiveVector e he.2.1, mul_one]

include hAL in
theorem positiveAtomScalarIsometry_surjective {e : E} (he : IsPositiveLatticeAtom e) :
    Function.Surjective (positiveAtomScalarIsometry he) := by
  intro x
  have hx : (x : E) ∈ Submodule.span ℝ {e} := by
    rw [← principalBand_eq_span_of_positive_atom hAL he]
    exact x.property
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
  refine ⟨r * ‖e‖, ?_⟩
  apply Subtype.ext
  change (r * ‖e‖) • (‖e‖⁻¹ • e) = (x : E)
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr he.2.1), mul_one]
  exact hr

def positiveAtomScalarEquiv {e : E} (he : IsPositiveLatticeAtom e) :
    ℝ ≃ₗᵢ[ℝ] principalBand e :=
  LinearIsometryEquiv.ofSurjective (positiveAtomScalarIsometry he)
    (positiveAtomScalarIsometry_surjective hAL he)

def positiveAtomPrincipalBandEquiv {e : E} (he : IsPositiveLatticeAtom e) :
    principalBand e ≃ₗᵢ[ℝ] ℝ := (positiveAtomScalarEquiv hAL he).symm

include hAL in
theorem finiteDimensional_principalBand_of_positive_atom {e : E}
    (he : IsPositiveLatticeAtom e) : FiniteDimensional ℝ (principalBand e) :=
  FiniteDimensional.of_injective (positiveAtomPrincipalBandEquiv hAL he).toLinearEquiv.toLinearMap
    (positiveAtomPrincipalBandEquiv hAL he).injective

end ThesisCommon
