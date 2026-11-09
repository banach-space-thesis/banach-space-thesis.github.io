import LindenstraussRetraction.Definitions
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Continuous transpose and second adjoint, with their canonical-embedding identities. -/

noncomputable section

namespace LindenstraussRetraction

universe u v w s

variable {𝕜 : Type s} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type w} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

-- Iterated strong duals produce large, definitionally standard instance terms.
set_option synthInstance.maxSize 512

/-- Definitionally the standard operator norm, with scalar parameters explicit
to work around inference for iterated duals in the pinned Mathlib revision. -/
instance instNormBidualOperator : Norm (Bidual 𝕜 E →L[𝕜] Bidual 𝕜 F) :=
  ContinuousLinearMap.hasOpNorm (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := Bidual 𝕜 E) (F := Bidual 𝕜 F) (σ₁₂ := RingHom.id 𝕜)

/-- The continuous transpose, given by precomposition. -/
def transpose (T : E →L[𝕜] F) : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E :=
  (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip T

@[simp] theorem transpose_apply (T : E →L[𝕜] F) (f : StrongDual 𝕜 F) (x : E) :
    transpose T f x = f (T x) := rfl

theorem norm_transpose_le (T : E →L[𝕜] F) : ‖transpose T‖ ≤ ‖T‖ := by
  apply (transpose T).opNorm_le_bound (norm_nonneg T)
  intro f
  simpa only [transpose, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, mul_comm] using
    ContinuousLinearMap.opNorm_comp_le f T

/-- Passing to the continuous dual preserves the operator norm. -/
theorem norm_transpose (T : E →L[𝕜] F) : ‖transpose T‖ = ‖T‖ := by
  apply le_antisymm (norm_transpose_le T)
  apply T.opNorm_le_bound (norm_nonneg (transpose T))
  intro x
  apply NormedSpace.norm_le_dual_bound 𝕜 (T x) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro f
  calc
    ‖f (T x)‖ = ‖transpose T f x‖ := rfl
    _ ≤ ‖transpose T f‖ * ‖x‖ := (transpose T f).le_opNorm x
    _ ≤ (‖transpose T‖ * ‖f‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right ((transpose T).le_opNorm f) (norm_nonneg _)
    _ = (‖transpose T‖ * ‖x‖) * ‖f‖ := by rw [mul_right_comm]

/-- The second adjoint `T**`, acting on the normed continuous biduals. -/
def bidualMap (T : E →L[𝕜] F) : Bidual 𝕜 E →L[𝕜] Bidual 𝕜 F :=
  transpose (transpose T)

@[simp] theorem bidualMap_apply (T : E →L[𝕜] F)
    (z : Bidual 𝕜 E) (f : StrongDual 𝕜 F) :
    bidualMap T z f = z (transpose T f) := rfl

@[simp] theorem bidualMap_embedding (T : E →L[𝕜] F) (x : E) :
    bidualMap T (bidualEmbedding 𝕜 E x) = bidualEmbedding 𝕜 F (T x) := by
  ext f
  rfl

theorem norm_bidualMap_le (T : E →L[𝕜] F) : ‖bidualMap T‖ ≤ ‖T‖ :=
  (norm_transpose_le (transpose T)).trans (norm_transpose_le T)

theorem norm_bidualMap (T : E →L[𝕜] F) : ‖bidualMap T‖ = ‖T‖ :=
  (norm_transpose (transpose T)).trans (norm_transpose T)

/-- The pointwise operator estimate, useful without synthesizing a normed
group structure on the space of bidual operators. -/
theorem norm_bidualMap_apply_le (T : E →L[𝕜] F) (z : Bidual 𝕜 E) :
    ‖bidualMap T z‖ ≤ ‖T‖ * ‖z‖ := by
  apply (bidualMap T z).opNorm_le_bound (mul_nonneg (norm_nonneg T) (norm_nonneg z))
  intro f
  calc
    ‖bidualMap T z f‖ = ‖z (transpose T f)‖ := rfl
    _ ≤ ‖z‖ * ‖transpose T f‖ := z.le_opNorm _
    _ ≤ ‖z‖ * (‖T‖ * ‖f‖) := mul_le_mul_of_nonneg_left
      (((transpose T).le_opNorm f).trans (mul_le_mul_of_nonneg_right
        (norm_transpose_le T) (norm_nonneg f))) (norm_nonneg z)
    _ = (‖T‖ * ‖z‖) * ‖f‖ := by rw [← mul_assoc, mul_comm ‖z‖ ‖T‖]

@[simp] theorem bidualMap_id :
    bidualMap (ContinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 (Bidual 𝕜 E) := by
  ext z f
  rfl

@[simp] theorem bidualMap_comp (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    bidualMap (S.comp T) = (bidualMap S).comp (bidualMap T) := by
  ext z f
  rfl

theorem bidualMap_leftInverse (U : E →L[𝕜] F) (V : F →L[𝕜] E)
    (h : Function.LeftInverse V U) : Function.LeftInverse (bidualMap V) (bidualMap U) := by
  have hcomp : V.comp U = ContinuousLinearMap.id 𝕜 E := by
    ext x
    exact h x
  intro z
  change ((bidualMap V).comp (bidualMap U)) z = z
  rw [← bidualMap_comp, hcomp, bidualMap_id]
  rfl

end LindenstraussRetraction
