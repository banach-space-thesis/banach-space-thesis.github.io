import SurveyStatements.P5HaarDiagonalBounds
import SurveyStatements.P5HaarDensity

/-! Product-Haar multipliers are actual bounded operators on the doubly
cancellative Bochner space, characterized by their values on Haar vectors. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory Set
open scoped ENNReal

namespace SurveyStatements.P5

attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def IsProductHaarMultiplier
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜) : Prop :=
  ∀ I J, T (cancellativeHaar 𝕜 p I J) = d I J • cancellativeHaar 𝕜 p I J

theorem cancellativeHaar_ne_zero (hp : p ≠ ∞) (I J : DyadicIndex) :
    cancellativeHaar 𝕜 p I J ≠ 0 := by
  intro hz
  have h := cancellativeHaarCoordinate_biorthogonal 𝕜 p hp I J I J
  rw [if_pos rfl, hz, map_zero] at h
  exact zero_ne_one h

theorem IsProductHaarMultiplier.diagonal (hp : p ≠ ∞)
    {T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p}
    {d : DyadicIndex → DyadicIndex → 𝕜} (hT : IsProductHaarMultiplier T d)
    (I J : DyadicIndex) :
    cancellativeHaarCoordinate 𝕜 p I J (T (cancellativeHaar 𝕜 p I J)) = d I J := by
  rw [hT I J, map_smul, cancellativeHaarCoordinate_biorthogonal 𝕜 p hp,
    if_pos rfl, smul_eq_mul, mul_one]

theorem IsProductHaarMultiplier.symbol_norm_le (hp : p ≠ ∞)
    {T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p}
    {d : DyadicIndex → DyadicIndex → 𝕜} (hT : IsProductHaarMultiplier T d)
    (I J : DyadicIndex) : ‖d I J‖ ≤ ‖T‖ := by
  have h := T.le_opNorm (cancellativeHaar 𝕜 p I J)
  rw [hT I J, norm_smul] at h
  exact (mul_le_mul_right (norm_pos_iff.mpr (cancellativeHaar_ne_zero hp I J))).mp h

theorem cancellativeOperators_eq_of_haar (hp : p ≠ ∞)
    (T U : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (hTU : ∀ I J, T (cancellativeHaar 𝕜 p I J) = U (cancellativeHaar 𝕜 p I J)) :
    T = U := by
  let F := T.comp (cancellativeProjection 𝕜 p)
  let G := U.comp (cancellativeProjection 𝕜 p)
  have hfix (x : DoublyZeroMean 𝕜 p) : cancellativeProjection 𝕜 p x.val = x := by
    exact congrArg (fun L : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p => L x)
      (cancellativeProjection_retraction 𝕜 p)
  have hgen : Set.EqOn F G
      (Set.range (fun IJ : DyadicIndex × DyadicIndex => productHaar 𝕜 p IJ.1 IJ.2)) := by
    rintro _ ⟨⟨I, J⟩, rfl⟩
    change T (cancellativeProjection 𝕜 p (cancellativeHaar 𝕜 p I J).val) =
      U (cancellativeProjection 𝕜 p (cancellativeHaar 𝕜 p I J).val)
    rw [hfix]
    exact hTU I J
  apply ContinuousLinearMap.ext
  intro x
  have hx : x.val ∈ closure (Submodule.span 𝕜
      (Set.range (fun IJ : DyadicIndex × DyadicIndex =>
        productHaar 𝕜 p IJ.1 IJ.2)) : Set (MixedNorm 𝕜 p)) := by
    change x.val ∈ ProductHaarSpace 𝕜 p
    rw [productHaarSpace_eq_doublyZeroMean hp]
    exact x.property
  have h := ContinuousLinearMap.eqOn_closure_span hgen hx
  change T (cancellativeProjection 𝕜 p x.val) = U (cancellativeProjection 𝕜 p x.val) at h
  simpa only [hfix] using h

theorem IsProductHaarMultiplier.unique (hp : p ≠ ∞)
    {T U : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p}
    {d : DyadicIndex → DyadicIndex → 𝕜}
    (hT : IsProductHaarMultiplier T d) (hU : IsProductHaarMultiplier U d) : T = U := by
  apply cancellativeOperators_eq_of_haar hp
  intro I J
  rw [hT I J, hU I J]

theorem IsProductHaarMultiplier.comp
    {T U : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p}
    {d e : DyadicIndex → DyadicIndex → 𝕜}
    (hT : IsProductHaarMultiplier T d) (hU : IsProductHaarMultiplier U e) :
    IsProductHaarMultiplier (T.comp U) (fun I J => e I J * d I J) := by
  intro I J
  change T (U (cancellativeHaar 𝕜 p I J)) = _
  rw [hU I J, map_smul, hT I J, smul_smul]

end SurveyStatements.P5
