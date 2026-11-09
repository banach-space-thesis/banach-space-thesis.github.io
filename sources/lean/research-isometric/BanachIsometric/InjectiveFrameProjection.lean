import BanachIsometric.ProjectionGrassmannian
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Banach

/-! Orthogonal projection onto an actual injective frame has the analytic
formula F (F* F)⁻¹ F*. Gram invertibility and equality with the canonical
orthogonal projection are proved, rather than premises. This supplies the
projection formula for genuine Grassmannian graph charts. -/

noncomputable section
namespace BanachIsometric
open Set

variable {E V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def frameGram (F : E →L[ℝ] V) : E →L[ℝ] E := F.adjoint.comp F

def frameProjection (F : E →L[ℝ] V) : V →L[ℝ] V :=
  F.comp ((Ring.inverse (frameGram F)).comp F.adjoint)

theorem frameGram_isUnit (F : E →L[ℝ] V) (hF : Function.Injective F) :
    IsUnit (frameGram F) := by
  have hzero (x : E) (hx : frameGram F x = 0) : x = 0 := by
    apply hF
    rw [map_zero]
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    rw [F.apply_norm_sq_eq_inner_adjoint_left]
    change (inner ℝ (frameGram F x) x) = 0
    rw [hx, inner_zero_left]
  have hinj : Function.Injective (frameGram F) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩

theorem frameGram_mul_inverse_apply (F : E →L[ℝ] V) (hF : Function.Injective F) (x : E) :
    frameGram F (Ring.inverse (frameGram F) x) = x := by
  exact congrArg (fun T : E →L[ℝ] E => T x)
    (Ring.mul_inverse_cancel _ (frameGram_isUnit F hF))

theorem frameGram_inverse_mul_apply (F : E →L[ℝ] V) (hF : Function.Injective F) (x : E) :
    Ring.inverse (frameGram F) (frameGram F x) = x := by
  exact congrArg (fun T : E →L[ℝ] E => T x)
    (Ring.inverse_mul_cancel _ (frameGram_isUnit F hF))

theorem frameProjection_eq_starProjection (F : E →L[ℝ] V) (hF : Function.Injective F) :
    frameProjection F = (LinearMap.range F.toLinearMap).starProjection := by
  apply ContinuousLinearMap.ext
  intro y
  apply Eq.symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨Ring.inverse (frameGram F) (F.adjoint y), rfl⟩
  · have hAdj : F.adjoint (y - frameProjection F y) = 0 := by
      rw [map_sub]
      change F.adjoint y - frameGram F (Ring.inverse (frameGram F) (F.adjoint y)) = 0
      rw [frameGram_mul_inverse_apply F hF, sub_self]
    intro z hz
    obtain ⟨x, rfl⟩ := hz
    change inner ℝ (F x) (y - frameProjection F y) = 0
    rw [← F.adjoint_inner_right, hAdj, inner_zero_right]

theorem frameProjection_apply_frame (F : E →L[ℝ] V) (hF : Function.Injective F) (x : E) :
    frameProjection F (F x) = F x := by
  change F (Ring.inverse (frameGram F) (frameGram F x)) = F x
  rw [frameGram_inverse_mul_apply F hF]

theorem frameProjection_isStarProjection (F : E →L[ℝ] V) (hF : Function.Injective F) :
    IsStarProjection (frameProjection F) := by
  rw [frameProjection_eq_starProjection F hF]
  exact isStarProjection_starProjection

theorem frameProjection_range (F : E →L[ℝ] V) (hF : Function.Injective F) :
    LinearMap.range (frameProjection F).toLinearMap = LinearMap.range F.toLinearMap := by
  rw [frameProjection_eq_starProjection F hF]
  exact Submodule.range_starProjection _

theorem contDiff_frameGram : ContDiff ℝ ⊤ (frameGram : (E →L[ℝ] V) → E →L[ℝ] E) := by
  have hAdj : ContDiff ℝ ⊤ (fun F : E →L[ℝ] V => F.adjoint) :=
    (ContinuousLinearMap.adjoint : (E →L[ℝ] V) ≃ₗᵢ[ℝ] (V →L[ℝ] E)).contDiff
  exact hAdj.clm_comp contDiff_id

theorem contDiffAt_frameProjection (F : E →L[ℝ] V) (hF : Function.Injective F) :
    ContDiffAt ℝ ⊤ (frameProjection : (E →L[ℝ] V) → V →L[ℝ] V) F := by
  have hu := frameGram_isUnit F hF
  have hInv : ContDiffAt ℝ ⊤ Ring.inverse (frameGram F) := by
    simpa only [hu.unit_spec] using (contDiffAt_ringInverse ℝ hu.unit :
      ContDiffAt ℝ ⊤ Ring.inverse (hu.unit : E →L[ℝ] E))
  have hAdj : ContDiffAt ℝ ⊤ (fun F : E →L[ℝ] V => F.adjoint) F :=
    (ContinuousLinearMap.adjoint : (E →L[ℝ] V) ≃ₗᵢ[ℝ] (V →L[ℝ] E)).contDiff.contDiffAt
  exact contDiffAt_id.clm_comp
    ((hInv.comp F contDiff_frameGram.contDiffAt).clm_comp hAdj)

end BanachIsometric
