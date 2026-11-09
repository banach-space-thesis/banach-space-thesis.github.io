import SurveyStatements.P5LowerBiTreeErrorSeries
import SurveyStatements.P5UpperBiTreeErrorSeries
import SurveyStatements.P5GridScalarApproximation
import SurveyStatements.P5CaponGridRigidity
import SurveyStatements.P5HaarMultipliers

/-! Assembly of the actual grid limits and bounded error series.
Localized rigidity forces the two grid limits to agree. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
open BiTree
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def extendCancellativeOperator
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (DoublyZeroMean 𝕜 p).subtypeL.comp (T.comp (cancellativeProjection 𝕜 p))

theorem extendCancellativeOperator_on_subspace
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (x : DoublyZeroMean 𝕜 p) : extendCancellativeOperator T x.val = (T x).val := by
  have hfix : cancellativeProjection 𝕜 p x.val = x :=
    congrArg (fun L : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p => L x)
      (cancellativeProjection_retraction 𝕜 p)
  change (T (cancellativeProjection 𝕜 p x.val)).val = _
  rw [hfix]

theorem extendCancellativeOperator_productHaar
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜) (hT : IsProductHaarMultiplier T d)
    (I J : DyadicIndex) :
    extendCancellativeOperator T (productHaar 𝕜 p I J) =
      d I J • productHaar 𝕜 p I J := by
  change extendCancellativeOperator T (cancellativeHaar 𝕜 p I J).val = _
  rw [extendCancellativeOperator_on_subspace, hT I J]
  rfl

theorem stable_multiplier_grid_limits_eq (hp : p ≠ ∞)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜) (hT : IsProductHaarMultiplier T d)
    (η : ℕ → ℕ → ℝ) {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j)
    (hld : Summable (fun k => 4 * (k + 1 : ℕ) * η k k))
    (hlc : Summable (fun k => 4 * ∑ j ∈ Finset.range (k + 1), η k j))
    (hud : Summable (upperDiagonalErrorBudget η))
    (huc : Summable (upperCoordinateErrorBudget η))
    (M1 M2 : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (hM1 : Tendsto (diagonalGrid (p := p) d) atTop (𝓝 M1))
    (hM2 : Tendsto (superdiagonalGrid (p := p) d) atTop (𝓝 M2)) : M1 = M2 := by
  let P := (DoublyZeroMean 𝕜 p).subtypeL.comp (cancellativeProjection 𝕜 p)
  let F := extendCancellativeOperator T - lowerBiTreeError (𝕜 := 𝕜) (p := p) hp d - upperBiTreeError (𝕜 := 𝕜) (p := p) hp d -
    M2.comp P
  have hP (I J : DyadicIndex) : P (productHaar 𝕜 p I J) = productHaar 𝕜 p I J := by
    have hfix : cancellativeProjection 𝕜 p (cancellativeHaar 𝕜 p I J).val =
        cancellativeHaar 𝕜 p I J :=
      congrArg (fun L : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p =>
        L (cancellativeHaar 𝕜 p I J)) (cancellativeProjection_retraction 𝕜 p)
    change (cancellativeProjection 𝕜 p (cancellativeHaar 𝕜 p I J).val).val = _
    rw [hfix]
    rfl
  have hF (I J : DyadicIndex) : F (productHaar 𝕜 p I J) =
      if J.1 ≤ I.1 then (M1 - M2) (productHaar 𝕜 p I J) else 0 := by
    dsimp only [F]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sub_apply, extendCancellativeOperator_productHaar T d hT,
      lowerBiTreeError_productHaar hp d η hs hη hld hlc M1 hM1,
      upperBiTreeError_productHaar hp d η hs hη hud huc M2 hM2,
      ContinuousLinearMap.comp_apply, hP]
    by_cases hji : J.1 ≤ I.1
    · rw [if_pos hji, if_pos hji, if_neg (Nat.not_lt.mpr hji),
        ContinuousLinearMap.sub_apply]
      abel
    · rw [if_neg hji, if_neg hji, if_pos (Nat.lt_of_not_ge hji)]
      abel
  have hzero : M1 - M2 = 0 := capon_square_grid_norm_closure_rigidity
    (𝕜 := 𝕜) (p := p) hp (M1 - M2) F
    (diagonal_superdiagonal_difference_square_approx (𝕜 := 𝕜) (p := p)
      d M1 M2 hM1 hM2) hF
  exact (sub_eq_zero (a := M1) (b := M2)).mp hzero

theorem stable_multiplier_norm_sub_scalar_le (hp : p ≠ ∞)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (d : DyadicIndex → DyadicIndex → 𝕜) (hT : IsProductHaarMultiplier T d)
    (η : ℕ → ℕ → ℝ) {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ i j, 0 ≤ η i j)
    (hld : Summable (fun k => 4 * (k + 1 : ℕ) * η k k))
    (hlc : Summable (fun k => 4 * ∑ j ∈ Finset.range (k + 1), η k j))
    (hud : Summable (upperDiagonalErrorBudget η))
    (huc : Summable (upperCoordinateErrorBudget η))
    (M1 M2 : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (hM1 : Tendsto (diagonalGrid (p := p) d) atTop (𝓝 M1))
    (hM2 : Tendsto (superdiagonalGrid (p := p) d) atTop (𝓝 M2)) (lam : 𝕜) :
    ‖T - lam • ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p)‖ ≤
      ‖lowerBiTreeError (𝕜 := 𝕜) (p := p) hp d‖ + ‖upperBiTreeError (𝕜 := 𝕜) (p := p) hp d‖ +
        ‖M1 - lam • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p)‖ := by
  have heq := stable_multiplier_grid_limits_eq hp T d hT η hs hη hld hlc hud huc
    M1 M2 hM1 hM2
  let E1 := lowerBiTreeError (𝕜 := 𝕜) (p := p) hp d
  let E2 := upperBiTreeError (𝕜 := 𝕜) (p := p) hp d
  have hgen : Set.EqOn (extendCancellativeOperator T - E1 - E2) M1
      (Set.range (fun IJ : DyadicIndex × DyadicIndex => productHaar 𝕜 p IJ.1 IJ.2)) := by
    rintro _ ⟨⟨I, J⟩, rfl⟩
    dsimp only [E1, E2]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      extendCancellativeOperator_productHaar T d hT,
      lowerBiTreeError_productHaar hp d η hs hη hld hlc M1 hM1,
      upperBiTreeError_productHaar hp d η hs hη hud huc M2 hM2, ← heq]
    by_cases hji : J.1 ≤ I.1
    · rw [if_pos hji, if_neg (Nat.not_lt.mpr hji)]
      abel
    · rw [if_neg hji, if_pos (Nat.lt_of_not_ge hji)]
      abel
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  intro x
  have hx : x.val ∈ closure (Submodule.span 𝕜
      (Set.range (fun IJ : DyadicIndex × DyadicIndex =>
        productHaar 𝕜 p IJ.1 IJ.2)) : Set (MixedNorm 𝕜 p)) := by
    change x.val ∈ ProductHaarSpace 𝕜 p
    rw [productHaarSpace_eq_doublyZeroMean hp]
    exact x.property
  have h := ContinuousLinearMap.eqOn_closure_span hgen hx
  simp only [ContinuousLinearMap.sub_apply, extendCancellativeOperator_on_subspace] at h
  rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add] at h
  have hpoint : (T x).val - lam • x.val =
      E1 x.val + E2 x.val + (M1 - lam • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p)) x.val := by
    rw [h, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    abel
  change ‖(T x).val - lam • x.val‖ ≤ _
  rw [hpoint]
  calc
    _ ≤ ‖E1 x.val + E2 x.val‖ +
        ‖(M1 - lam • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p)) x.val‖ := norm_add_le _ _
    _ ≤ ‖E1 x.val‖ + ‖E2 x.val‖ +
        ‖(M1 - lam • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p)) x.val‖ :=
      add_le_add_right (norm_add_le _ _) _
    _ ≤ ‖E1‖ * ‖x.val‖ + ‖E2‖ * ‖x.val‖ +
        ‖M1 - lam • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p)‖ * ‖x.val‖ :=
      add_le_add (add_le_add (E1.le_opNorm x.val) (E2.le_opNorm x.val))
        ((M1 - lam • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p)).le_opNorm x.val)
    _ = _ := by change _ = (‖E1‖ + ‖E2‖ + _) * ‖x.val‖; ring

end SurveyStatements.P5

