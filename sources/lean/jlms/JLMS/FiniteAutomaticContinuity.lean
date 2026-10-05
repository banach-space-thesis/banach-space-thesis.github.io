import JLMS.MainStatements
import JLMS.FiniteRank

/-!
# Finite-dimensional automatic continuity

Every scalar-linear map from a finite-dimensional normed space is continuous.
Thus every algebra homomorphism out of its operator algebra is continuous.
This includes the finite ordinal case of Section 9, independently of the
Johnson and Ogden background results for infinite spaces.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]

theorem continuous_operator_hom_of_finiteDimensional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    (φ : (E →L[𝕜] E) →ₙₐ[𝕜] A) : Continuous φ := by
  let L : (E →L[𝕜] E) →ₗ[𝕜] A :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := φ.map_smul }
  exact L.continuous_of_finiteDimensional

theorem finiteDimensional_continuousMap_of_finite
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Finite K] :
    FiniteDimensional 𝕜 C(K, 𝕜) := by
  let L : C(K, 𝕜) →ₗ[𝕜] (K → 𝕜) :=
    { toFun f := f
      map_add' f g := rfl
      map_smul' c f := rfl }
  exact FiniteDimensional.of_injective L (by intro f g h; exact DFunLike.coe_injective h)

theorem theorem_1_3_of_finite (α : Ordinal) [Finite (OrdinalInterval α)] :
    Theorem_1_3 𝕜 α := by
  letI : FiniteDimensional 𝕜 (OrdinalC 𝕜 α) := finiteDimensional_continuousMap_of_finite
  intro A _ _ _ _ _ φ
  exact continuous_operator_hom_of_finiteDimensional φ

end JLMS
