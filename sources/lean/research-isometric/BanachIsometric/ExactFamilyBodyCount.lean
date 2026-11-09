import BanachIsometric.ExactFamilyInteriorCount
import BanachIsometric.GaugeLevelGeometry

/-!
# Actual interior body multiplicity of the exact-family cone

One fixed large coordinate cube defines the integer of the prescribed normal
cone. It is independent of the evaluated parameter. The actual count on the
original Euclidean unit ball is this integer almost everywhere throughout the
interior of the actual positive gauge-level body.
-/

namespace BanachIsometric.ExactTangentialFamily

open MeasureTheory Set Metric
open scoped Topology NNReal

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {g : V → ℝ} {p : E → ℝ} (A : ExactTangentialFamily E V g p)
  {n : ℕ} [NeZero n]

noncomputable def normalConeSignedIndex (e : V ≃L[ℝ] PiolaSpace n) : ℤ :=
  localSignedIndex (coordinateMapConjugate e (coneExtension (fun z => (A.normal z).val)))
    (coordinateCubeLower n (‖(e : V →L[ℝ] PiolaSpace n)‖ + 1))
    (coordinateCubeUpper n (‖(e : V →L[ℝ] PiolaSpace n)‖ + 1)) 0

variable [MeasurableSpace V] [BorelSpace V]

theorem ae_unitBall_coneEvaluation_count_eq_normalConeSignedIndex
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (e : V ≃L[ℝ] PiolaSpace n) (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g)
    {y : E} (hy : 0 < p y) (hnormal : ∃ L : ℝ≥0, LipschitzWith L A.normal) :
    ∀ᵐ v ∂μ, g v < p y → signedFiberCount (A.coneEvaluation y) (fderiv ℝ (A.coneEvaluation y))
      (closedBall (0 : V) 1) v = A.normalConeSignedIndex e := by
  have hR : ‖(e : V →L[ℝ] PiolaSpace n)‖ < ‖(e : V →L[ℝ] PiolaSpace n)‖ + 1 := by linarith
  simpa only [normalConeSignedIndex] using
    A.ae_unitBall_coneEvaluation_count_eq_normal_index μ e hg hcont hy hnormal hR

theorem ae_interior_body_coneEvaluation_count_eq_normalConeSignedIndex
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (e : V ≃L[ℝ] PiolaSpace n) (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g)
    {y : E} (hy : 0 < p y) (hnormal : ∃ L : ℝ≥0, LipschitzWith L A.normal) :
    ∀ᵐ v ∂μ, v ∈ interior {x | g x ≤ p y} →
      signedFiberCount (A.coneEvaluation y) (fderiv ℝ (A.coneEvaluation y))
        (closedBall (0 : V) 1) v = A.normalConeSignedIndex e := by
  simpa only [hg.interior_pos_sublevel_eq_strict hcont hy, mem_setOf_eq] using
    A.ae_unitBall_coneEvaluation_count_eq_normalConeSignedIndex μ e hg hcont hy hnormal

end BanachIsometric.ExactTangentialFamily
