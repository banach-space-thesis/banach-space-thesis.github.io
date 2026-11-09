import SurveyStatements.P5GeneralMixedErrorReduction
import SurveyStatements.P5GeneralMixedErrorCanonicalTraceCoordinates
import SurveyStatements.P5GeneralMixedErrorCanonicalNuclear

/-! The three actual off-diagonal matrices, with genuine operator bounds,
assemble the required arbitrary-operator compression to a Haar multiplier. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory
open scoped ENNReal Classical

namespace SurveyStatements.P5
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
open P5Support BiTree
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem generalMixed_coordinate_error_sum (hp : p ≠ ∞)
    (Eouter Einner Emixed : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (a : DyadicIndex → DyadicIndex → DyadicIndex → DyadicIndex → 𝕜)
    (houter : ∀ I J K L, cancellativeHaarCoordinate 𝕜 p I J
      (Eouter (cancellativeHaar 𝕜 p K L)) =
        if I = K ∧ J ≠ L then a K J K L else 0)
    (hinner : ∀ I J K L, cancellativeHaarCoordinate 𝕜 p I J
      (Einner (cancellativeHaar 𝕜 p K L)) =
        if I ≠ K ∧ J = L then a I L K L else 0)
    (hmixed : ∀ I J K L, cancellativeHaarCoordinate 𝕜 p I J
      (Emixed (cancellativeHaar 𝕜 p K L)) =
        if I ≠ K ∧ J ≠ L then a I J K L else 0)
    (I J K L : DyadicIndex) :
    cancellativeHaarCoordinate 𝕜 p I J
      (a K L K L • cancellativeHaar 𝕜 p K L +
        Eouter (cancellativeHaar 𝕜 p K L) + Einner (cancellativeHaar 𝕜 p K L) +
        Emixed (cancellativeHaar 𝕜 p K L)) = a I J K L := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  let c : DoublyZeroMean 𝕜 p →L[𝕜] 𝕜 := cancellativeHaarCoordinate 𝕜 p I J
  let x : DoublyZeroMean 𝕜 p := a K L K L • cancellativeHaar 𝕜 p K L
  let y : DoublyZeroMean 𝕜 p := Eouter (cancellativeHaar 𝕜 p K L)
  let z : DoublyZeroMean 𝕜 p := Einner (cancellativeHaar 𝕜 p K L)
  let w : DoublyZeroMean 𝕜 p := Emixed (cancellativeHaar 𝕜 p K L)
  have hsum : c (x + y + z + w) = c x + c y + c z + c w :=
    (c.map_add (x + y + z) w).trans
      (congrArg (fun v : 𝕜 => v + c w)
        ((c.map_add (x + y) z).trans
          (congrArg (fun v : 𝕜 => v + c z) (c.map_add x y))))
  have hbase : c (cancellativeHaar 𝕜 p K L) =
      if (I, J) = (K, L) then 1 else 0 :=
    cancellativeHaarCoordinate_biorthogonal 𝕜 p hp I J K L
  have hscalar : c x = if (I, J) = (K, L) then a K L K L else 0 := by
    calc
      _ = a K L K L • c (cancellativeHaar 𝕜 p K L) := c.map_smul _ _
      _ = a K L K L • (if (I, J) = (K, L) then (1 : 𝕜) else 0) :=
        congrArg (fun v : 𝕜 => a K L K L • v) hbase
      _ = _ := by
        by_cases h : (I, J) = (K, L)
        · simp only [if_pos h, smul_eq_mul, mul_one]
        · simp only [if_neg h, smul_eq_mul, mul_zero]
  calc
    _ = c x + c y + c z + c w := hsum
    _ = (if (I, J) = (K, L) then a K L K L else 0) +
        (if I = K ∧ J ≠ L then a K J K L else 0) +
        (if I ≠ K ∧ J = L then a I L K L else 0) +
        (if I ≠ K ∧ J ≠ L then a I J K L else 0) :=
      congrArg₂ (fun u v : 𝕜 => u + v)
        (congrArg₂ (fun u v : 𝕜 => u + v)
          (congrArg₂ (fun u v : 𝕜 => u + v) hscalar (houter I J K L))
          (hinner I J K L)) (hmixed I J K L)
    _ = _ := (generalMixed_matrix_classes_exhaust a I J K L).symm

theorem faithful_arbitrary_multiplier_reduction_of_matrix (hp : p ≠ ∞)
    (Fo Fi : BiTree.SignedTree)
    (T Eouter Einner Emixed : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p)
    (a : DyadicIndex → DyadicIndex → DyadicIndex → DyadicIndex → 𝕜)
    (Couter Cinner Cmixed δ : ℝ)
    (ho : ‖Eouter‖ ≤ Couter) (hi : ‖Einner‖ ≤ Cinner) (hm : ‖Emixed‖ ≤ Cmixed)
    (hbudget : Couter + Cinner + Cmixed < δ)
    (hactual : ∀ I J K L,
      faithfulMixedBlockReader (𝕜 := 𝕜) (p := p) Fo Fi I J
        (generalMixedCancellativeExtension T
          (tensorWith ((Fi.block L).vector 𝕜 ⟨1, le_rfl⟩)
            ((Fo.block K).vector 𝕜 ⟨p, Fact.out⟩))) = a I J K L)
    (houter : ∀ I J K L, cancellativeHaarCoordinate 𝕜 p I J
      (Eouter (cancellativeHaar 𝕜 p K L)) =
        if I = K ∧ J ≠ L then a K J K L else 0)
    (hinner : ∀ I J K L, cancellativeHaarCoordinate 𝕜 p I J
      (Einner (cancellativeHaar 𝕜 p K L)) =
        if I ≠ K ∧ J = L then a I L K L else 0)
    (hmixed : ∀ I J K L, cancellativeHaarCoordinate 𝕜 p I J
      (Emixed (cancellativeHaar 𝕜 p K L)) =
        if I ≠ K ∧ J ≠ L then a I J K L else 0) :
    ∃ A B M : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p,
      A.comp B = ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p) ∧
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      IsProductHaarMultiplier M (fun K L => a K L K L) ∧
      ‖((A.comp T).comp B) - M‖ < δ := by
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  apply faithful_arbitrary_multiplier_reduction_of_errors (𝕜 := 𝕜) (p := p)
    hp Fo Fi T Eouter Einner Emixed
    (fun K L => a K L K L) Couter Cinner Cmixed δ ho hi hm hbudget
  exact fun I J K L => (hactual I J K L).trans
    (generalMixed_coordinate_error_sum (𝕜 := 𝕜) (p := p) hp
      Eouter Einner Emixed a houter hinner hmixed I J K L).symm

end SurveyStatements.P5
