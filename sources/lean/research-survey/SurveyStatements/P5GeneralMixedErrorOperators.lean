import SurveyStatements.P5HaarMultipliers
import SurveyStatements.P5OperatorSeriesBounds

/-! Actual rank-one mixed-coordinate errors. Summability is required only
for the designated mixed remainder, with the full coordinate and vector norms. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def mixedCoordinateRankOne (source target : DyadicIndex × DyadicIndex) (a : 𝕜) :
    DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
  a • (cancellativeHaarCoordinate 𝕜 p source.1 source.2).smulRight
    (cancellativeHaar 𝕜 p target.1 target.2)

theorem norm_mixedCoordinateRankOne (source target : DyadicIndex × DyadicIndex) (a : 𝕜) :
    ‖mixedCoordinateRankOne (𝕜 := 𝕜) (p := p) source target a‖ =
      ‖a‖ * (‖cancellativeHaarCoordinate 𝕜 p source.1 source.2‖ *
        ‖cancellativeHaar 𝕜 p target.1 target.2‖) := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  rw [mixedCoordinateRankOne, norm_smul, ContinuousLinearMap.norm_smulRight_apply]

theorem mixedCoordinateRankOne_haar (hp : p ≠ ∞)
    (source target : DyadicIndex × DyadicIndex) (a : 𝕜) (K L : DyadicIndex) :
    mixedCoordinateRankOne (𝕜 := 𝕜) (p := p) source target a
      (cancellativeHaar 𝕜 p K L) =
      if source = (K, L) then a • cancellativeHaar 𝕜 p target.1 target.2 else 0 := by
  rw [mixedCoordinateRankOne, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,
    cancellativeHaarCoordinate_biorthogonal 𝕜 p hp]
  by_cases h : source = (K, L) <;> simp [h]

theorem mixedCoordinateRankOne_coordinate (hp : p ≠ ∞)
    (source target : DyadicIndex × DyadicIndex) (a : 𝕜) (I J K L : DyadicIndex) :
    cancellativeHaarCoordinate 𝕜 p I J
      (mixedCoordinateRankOne (𝕜 := 𝕜) (p := p) source target a
        (cancellativeHaar 𝕜 p K L)) =
      if source = (K, L) ∧ target = (I, J) then a else 0 := by
  rw [mixedCoordinateRankOne_haar hp]
  by_cases hs : source = (K, L)
  · rw [if_pos hs, map_smul, cancellativeHaarCoordinate_biorthogonal 𝕜 p hp]
    by_cases ht : target = (I, J)
    · have hpair : (I, J) = (target.1, target.2) := by simpa only [Prod.eta] using ht.symm
      simp only [if_pos hpair, if_pos (And.intro hs ht), smul_eq_mul, mul_one]
    · have hpair : (I, J) ≠ (target.1, target.2) := by
        intro h
        apply ht
        simpa only [Prod.eta] using h.symm
      have hnot : ¬(source = (K, L) ∧ target = (I, J)) := fun h => ht h.2
      simp only [if_neg hpair, if_neg hnot, smul_eq_mul, mul_zero]
  · rw [if_neg hs, map_zero, if_neg (fun h => hs h.1)]

def mixedNuclearError {ι : Type*}
    (source target : ι → DyadicIndex × DyadicIndex) (a : ι → 𝕜) :
    DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
  ∑' i, mixedCoordinateRankOne (𝕜 := 𝕜) (p := p) (source i) (target i) (a i)

theorem mixedNuclearError_summable {ι : Type*}
    (source target : ι → DyadicIndex × DyadicIndex) (a : ι → 𝕜)
    (b : ι → ℝ) (hb : Summable b)
    (hbound : ∀ i, ‖a i‖ *
      (‖cancellativeHaarCoordinate 𝕜 p (source i).1 (source i).2‖ *
        ‖cancellativeHaar 𝕜 p (target i).1 (target i).2‖) ≤ b i) :
    Summable (fun i => mixedCoordinateRankOne (𝕜 := 𝕜) (p := p)
      (source i) (target i) (a i)) := by
  apply summable_operators_of_norm_bound _ b hb
  intro i
  rw [norm_mixedCoordinateRankOne]
  exact hbound i

theorem norm_mixedNuclearError_le {ι : Type*}
    (source target : ι → DyadicIndex × DyadicIndex) (a : ι → 𝕜)
    (b : ι → ℝ) (hb : Summable b)
    (hbound : ∀ i, ‖a i‖ *
      (‖cancellativeHaarCoordinate 𝕜 p (source i).1 (source i).2‖ *
        ‖cancellativeHaar 𝕜 p (target i).1 (target i).2‖) ≤ b i) :
    ‖mixedNuclearError (𝕜 := 𝕜) (p := p) source target a‖ ≤ ∑' i, b i := by
  apply norm_operator_tsum_le _ b hb
  intro i
  rw [norm_mixedCoordinateRankOne]
  exact hbound i

theorem mixedNuclearError_haar {ι : Type*} (hp : p ≠ ∞)
    (source target : ι → DyadicIndex × DyadicIndex) (a : ι → 𝕜)
    (b : ι → ℝ) (hb : Summable b)
    (hbound : ∀ i, ‖a i‖ *
      (‖cancellativeHaarCoordinate 𝕜 p (source i).1 (source i).2‖ *
        ‖cancellativeHaar 𝕜 p (target i).1 (target i).2‖) ≤ b i)
    (K L : DyadicIndex) :
    mixedNuclearError (𝕜 := 𝕜) (p := p) source target a (cancellativeHaar 𝕜 p K L) =
      ∑' i, if source i = (K, L) then
        a i • cancellativeHaar 𝕜 p (target i).1 (target i).2 else 0 := by
  calc
    _ = ∑' i, mixedCoordinateRankOne (𝕜 := 𝕜) (p := p)
        (source i) (target i) (a i) (cancellativeHaar 𝕜 p K L) :=
      (ContinuousLinearMap.apply 𝕜 (DoublyZeroMean 𝕜 p)
        (cancellativeHaar 𝕜 p K L)).map_tsum
        (mixedNuclearError_summable source target a b hb hbound)
    _ = _ := tsum_congr (fun i => mixedCoordinateRankOne_haar hp _ _ _ K L)

theorem mixedNuclearError_coordinate {ι : Type*} (hp : p ≠ ∞)
    (source target : ι → DyadicIndex × DyadicIndex) (a : ι → 𝕜)
    (b : ι → ℝ) (hb : Summable b)
    (hbound : ∀ i, ‖a i‖ *
      (‖cancellativeHaarCoordinate 𝕜 p (source i).1 (source i).2‖ *
        ‖cancellativeHaar 𝕜 p (target i).1 (target i).2‖) ≤ b i)
    (I J K L : DyadicIndex) :
    cancellativeHaarCoordinate 𝕜 p I J
      (mixedNuclearError (𝕜 := 𝕜) (p := p) source target a (cancellativeHaar 𝕜 p K L)) =
      ∑' i, if source i = (K, L) ∧ target i = (I, J) then a i else 0 := by
  let ops := fun i => mixedCoordinateRankOne (𝕜 := 𝕜) (p := p)
    (source i) (target i) (a i)
  have hops : Summable ops := mixedNuclearError_summable source target a b hb hbound
  have hvalues := (ContinuousLinearMap.apply 𝕜 (DoublyZeroMean 𝕜 p)
    (cancellativeHaar 𝕜 p K L)).summable hops
  change cancellativeHaarCoordinate 𝕜 p I J ((∑' i, ops i) (cancellativeHaar 𝕜 p K L)) = _
  calc
    _ = cancellativeHaarCoordinate 𝕜 p I J
        (∑' i, ops i (cancellativeHaar 𝕜 p K L)) :=
      congrArg (cancellativeHaarCoordinate 𝕜 p I J)
        ((ContinuousLinearMap.apply 𝕜 (DoublyZeroMean 𝕜 p)
          (cancellativeHaar 𝕜 p K L)).map_tsum hops)
    _ = ∑' i, cancellativeHaarCoordinate 𝕜 p I J
        (ops i (cancellativeHaar 𝕜 p K L)) :=
      (cancellativeHaarCoordinate 𝕜 p I J).map_tsum hvalues
    _ = _ := tsum_congr (fun i => mixedCoordinateRankOne_coordinate hp _ _ _ I J K L)

end SurveyStatements.P5
