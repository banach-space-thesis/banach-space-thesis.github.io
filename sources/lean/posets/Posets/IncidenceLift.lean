import Posets.BlockMatrixLift
import Posets.ScalarMatrixProduct
import Posets.BoundedFewOperators
import Posets.IncidenceNorms

noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [PartialOrder P] [Nonempty P]
  {X : P → Type} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  [∀ p, CompleteSpace (X p)]
  {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι)

omit [Nonempty P] [∀ p, CompleteSpace (X p)] in
include h in
theorem fewOperators_contracts (s t : P) (x : X s) : ‖ι s t x‖ ≤ ‖x‖ := by
  by_cases hst : s ≤ t
  · simpa using ((h.2.1 s t hst).dist_eq x 0).le
  · simp [h.2.2.2.1 s t hst]

def incidenceLiftValue (T : oppositeIncidenceSubalgebra 𝕜 P) :
    DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X :=
  blockMatrixLift ι (fewOperators_contracts h) (scalarMatrix 𝕜 T.val)
    (scalarMatrix_boundedRows T.val) (scalarMatrix_zeroColumns T.val)

theorem incidenceLiftValue_block (T : oppositeIncidenceSubalgebra 𝕜 P) (s t : P) :
    operatorBlock 𝕜 X X (incidenceLiftValue h T) s t = scalarMatrix 𝕜 T.val s t • ι t s :=
  blockMatrixLift_block _ _ _ _ _ s t

theorem incidenceLiftValue_norm_le (T : oppositeIncidenceSubalgebra 𝕜 P) :
    ‖incidenceLiftValue h T‖ ≤ ‖T‖ := by
  change ‖incidenceLiftValue h T‖ ≤ ‖T.val‖
  rw [norm_eq_rowNorm_scalarMatrix]
  exact blockMatrixLift_norm_le _ _ _ _ _

def incidenceLiftLinear : oppositeIncidenceSubalgebra 𝕜 P →ₗ[𝕜]
    (DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) where
  toFun := incidenceLiftValue h
  map_add' := by
    intro S T
    apply operator_eq_of_blocks_eq
    intro s t
    rw [incidenceLiftValue_block]
    simp only [operatorBlock, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
    change scalarMatrix 𝕜 (S + T).val s t • ι t s =
      operatorBlock 𝕜 X X (incidenceLiftValue h S) s t +
        operatorBlock 𝕜 X X (incidenceLiftValue h T) s t
    rw [incidenceLiftValue_block, incidenceLiftValue_block]
    exact add_smul _ _ _
  map_smul' := by
    intro a T
    apply operator_eq_of_blocks_eq
    intro s t
    rw [incidenceLiftValue_block]
    simp only [operatorBlock, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
    change scalarMatrix 𝕜 (a • T).val s t • ι t s =
      a • operatorBlock 𝕜 X X (incidenceLiftValue h T) s t
    rw [incidenceLiftValue_block]
    exact mul_smul _ _ _

def incidenceLift : oppositeIncidenceSubalgebra 𝕜 P →L[𝕜]
    (DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) :=
  LinearMap.mkContinuous (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := oppositeIncidenceSubalgebra 𝕜 P) (F := DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X)
    (σ := RingHom.id 𝕜) (incidenceLiftLinear h) 1 (fun T => by
    change ‖incidenceLiftValue h T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using incidenceLiftValue_norm_le h T)

theorem incidenceLift_block (T : oppositeIncidenceSubalgebra 𝕜 P) (s t : P) :
    operatorBlock 𝕜 X X (incidenceLift h T) s t = scalarMatrix 𝕜 T.val s t • ι t s :=
  incidenceLiftValue_block h T s t

theorem incidenceLift_apply (T : oppositeIncidenceSubalgebra 𝕜 P) (x : DependentCZeroSum 𝕜 X) (s : P) :
    (incidenceLift h T x).val s = ∑' t, scalarMatrix 𝕜 T.val s t • ι t s (x.val t) := rfl

theorem incidenceLift_mul (S T : oppositeIncidenceSubalgebra 𝕜 P) :
    incidenceLift h (S * T) = incidenceLift h S * incidenceLift h T := by
  apply operator_eq_of_blocks_eq
  intro s t
  rw [incidenceLift_block]
  apply ContinuousLinearMap.ext
  intro x
  change scalarMatrix 𝕜 (S.val * T.val) s t • ι t s x =
    (incidenceLift h S (incidenceLift h T (sumInjection 𝕜 X t x))).val s
  rw [incidenceLift_apply, scalarMatrix_mul]
  have hcoord : ∀ r, (incidenceLift h T (sumInjection 𝕜 X t x)).val r =
      scalarMatrix 𝕜 T.val r t • ι t r x := fun r =>
    congrArg (fun U : X t →L[𝕜] X r => U x) (incidenceLift_block h T r t)
  simp_rw [hcoord, map_smul]
  rw [← (scalarMatrix_mul_summable S.val T.val s t).tsum_smul_const]
  apply tsum_congr
  intro r
  by_cases htr : t ≤ r
  · by_cases hrs : r ≤ s
    · have hcomp := congrArg (fun U : X t →L[𝕜] X s => U x)
        (h.2.2.1 t r s htr hrs)
      change ι r s (ι t r x) = ι t s x at hcomp
      rw [hcomp, mul_smul]
    · rw [S.property s r hrs]
      simp
  · rw [T.property r t htr]
    simp

def incidenceLiftHom : BoundedHom 𝕜 (oppositeIncidenceSubalgebra 𝕜 P)
    (DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) where
  toContinuousLinearMap := incidenceLift h
  map_mul' := incidenceLift_mul h

end Posets
