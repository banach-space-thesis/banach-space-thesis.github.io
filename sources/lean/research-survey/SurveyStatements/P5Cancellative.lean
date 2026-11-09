import SurveyStatements.P5Averages
import Mathlib.Tactic.Linarith

/-!
The actual two coordinate expectations on the Bochner space in Problem 5.
The zero-mean subspace below is defined by the two kernels. Identifying it with
the closed product-Haar span is a separate density theorem, still required.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5

section CommutingProjections

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Remove both means using two commuting projections. -/
def twoKernelProjection (P Q : E →L[𝕜] E) : E →L[𝕜] E :=
  (ContinuousLinearMap.id 𝕜 E - P).comp (ContinuousLinearMap.id 𝕜 E - Q)

theorem projection_sub_eq_zero (P : E →L[𝕜] E) (hP : P.comp P = P) (x : E) :
    P (x - P x) = 0 := by
  have hx := congrArg (fun A : E →L[𝕜] E => A x) hP
  change P (P x) = P x at hx
  rw [map_sub, hx, sub_self]

theorem twoKernelProjection_mem (P Q : E →L[𝕜] E)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q) (hPQ : P.comp Q = Q.comp P)
    (x : E) : twoKernelProjection P Q x ∈ LinearMap.ker P ⊓ LinearMap.ker Q := by
  constructor
  · change P ((x - Q x) - P (x - Q x)) = 0
    exact projection_sub_eq_zero P hP _
  · change Q ((x - Q x) - P (x - Q x)) = 0
    have hcomm := congrArg (fun A : E →L[𝕜] E => A (x - Q x)) hPQ
    change P (Q (x - Q x)) = Q (P (x - Q x)) at hcomm
    rw [map_sub, ← hcomm, projection_sub_eq_zero Q hQ, map_zero, sub_self]

theorem twoKernelProjection_fixes (P Q : E →L[𝕜] E)
    (x : ↥(LinearMap.ker P ⊓ LinearMap.ker Q)) : twoKernelProjection P Q x = x := by
  have hP : P x = 0 := x.property.1
  have hQ : Q x = 0 := x.property.2
  change ((x : E) - Q x) - P ((x : E) - Q x) = x
  rw [hQ, sub_zero, hP, sub_zero]

theorem twoKernelProjection_idempotent (P Q : E →L[𝕜] E)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q) (hPQ : P.comp Q = Q.comp P) :
    (twoKernelProjection P Q).comp (twoKernelProjection P Q) = twoKernelProjection P Q := by
  apply ContinuousLinearMap.ext
  intro x
  exact twoKernelProjection_fixes P Q
    ⟨twoKernelProjection P Q x, twoKernelProjection_mem P Q hP hQ hPQ x⟩

theorem twoKernelProjection_range (P Q : E →L[𝕜] E)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q) (hPQ : P.comp Q = Q.comp P) :
    LinearMap.range (twoKernelProjection P Q) = LinearMap.ker P ⊓ LinearMap.ker Q := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact twoKernelProjection_mem P Q hP hQ hPQ x
  · intro x hx
    exact ⟨x, twoKernelProjection_fixes P Q ⟨x, hx⟩⟩

theorem norm_twoKernelProjection_le (P Q : E →L[𝕜] E)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) : ‖twoKernelProjection P Q‖ ≤ 4 := by
  have hPn : ‖ContinuousLinearMap.id 𝕜 E - P‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E)])
  have hQn : ‖ContinuousLinearMap.id 𝕜 E - Q‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E)])
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hPn hQn (norm_nonneg _) (by norm_num)).trans (by norm_num))

end CommutingProjections

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Bochner integration in the outer coordinate, followed by constant extension. -/
def outerExpectation : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  probabilityLpMean

/-- Integration in the inner coordinate, applied pointwise in the outer one. -/
def innerExpectation : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (probabilityLpMean (𝕜 := 𝕜) (E := 𝕜) (p := 1)
    (μ := unitIntervalMeasure)).compLpL p unitIntervalMeasure

theorem outerExpectation_idempotent :
    (outerExpectation 𝕜 p).comp (outerExpectation 𝕜 p) = outerExpectation 𝕜 p :=
  probabilityLpMean_idempotent

theorem innerExpectation_idempotent :
    (innerExpectation 𝕜 p).comp (innerExpectation 𝕜 p) = innerExpectation 𝕜 p :=
  compLpL_idempotent _ probabilityLpMean_idempotent

theorem expectations_commute :
    (outerExpectation 𝕜 p).comp (innerExpectation 𝕜 p) =
      (innerExpectation 𝕜 p).comp (outerExpectation 𝕜 p) :=
  probabilityLpMean_natural _

theorem norm_outerExpectation_le : ‖outerExpectation 𝕜 p‖ ≤ 1 :=
  norm_probabilityLpMean_le

theorem norm_innerExpectation_le : ‖innerExpectation 𝕜 p‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le _).trans norm_probabilityLpMean_le

/-- The actual doubly zero-mean subspace of the mixed Bochner space. -/
def DoublyZeroMean : Submodule 𝕜 (MixedNorm 𝕜 p) :=
  LinearMap.ker (outerExpectation 𝕜 p) ⊓ LinearMap.ker (innerExpectation 𝕜 p)

theorem doublyZeroMean_isClosed : IsClosed (DoublyZeroMean 𝕜 p : Set (MixedNorm 𝕜 p)) :=
  (ContinuousLinearMap.isClosed_ker (outerExpectation 𝕜 p)).inter
    (ContinuousLinearMap.isClosed_ker (innerExpectation 𝕜 p))

instance doublyZeroMean_complete : CompleteSpace (DoublyZeroMean 𝕜 p) :=
  (doublyZeroMean_isClosed 𝕜 p).completeSpace_coe

/-- The paper's bounded projection `(id - E₁)(id - E₂)`, with its true codomain. -/
def cancellativeProjection : MixedNorm 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
  (twoKernelProjection (outerExpectation 𝕜 p) (innerExpectation 𝕜 p)).codRestrict
    (DoublyZeroMean 𝕜 p) (twoKernelProjection_mem _ _
      (outerExpectation_idempotent 𝕜 p) (innerExpectation_idempotent 𝕜 p)
      (expectations_commute 𝕜 p))

theorem cancellativeProjection_retraction :
    (cancellativeProjection 𝕜 p).comp (DoublyZeroMean 𝕜 p).subtypeL =
      ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact twoKernelProjection_fixes _ _ x

theorem norm_cancellativeProjection_le : ‖cancellativeProjection 𝕜 p‖ ≤ 4 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  exact (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right
      (norm_twoKernelProjection_le _ _ (norm_outerExpectation_le 𝕜 p)
        (norm_innerExpectation_le 𝕜 p)) (norm_nonneg x))

theorem norm_cancellativeInclusion_le : ‖(DoublyZeroMean 𝕜 p).subtypeL‖ ≤ 1 :=
  Submodule.norm_subtypeL_le _

end SurveyStatements.P5
