import ThesisCommon.Analysis.GantmacherResiduum
import ThesisCommon.Analysis.BanachAdjointAlgebra
import ThesisCommon.Analysis.QuotientOperatorBound

/-! Algebraic laws and contractivity of the actual bidual quotient operator. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace ThesisCommon
variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

local instance : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

local instance : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

local instance : HasQuotient (StrongDual 𝕜 (StrongDual 𝕜 E))
    (Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) :=
  @Submodule.hasQuotient 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))
    inferInstance inferInstance inferInstance

theorem residuumOperator_sub (S T : E →L[𝕜] F) :
    residuumOperator (S - T) = residuumOperator S - residuumOperator T := by
  apply ContinuousLinearMap.ext
  intro ξ
  induction ξ using Quotient.inductionOn' with
  | h ξ =>
    change Submodule.Quotient.mk (p := bidualImage 𝕜 F) (bidualMap (S - T) ξ) =
      Submodule.Quotient.mk (p := bidualImage 𝕜 F) (bidualMap S ξ) -
        Submodule.Quotient.mk (p := bidualImage 𝕜 F) (bidualMap T ξ)
    rw [bidualMap_sub, ContinuousLinearMap.sub_apply, Submodule.Quotient.mk_sub]

theorem residuumOperator_smul (a : 𝕜) (T : E →L[𝕜] F) :
    residuumOperator (a • T) = a • residuumOperator T := by
  apply ContinuousLinearMap.ext
  intro ξ
  induction ξ using Quotient.inductionOn' with
  | h ξ =>
    change Submodule.Quotient.mk (p := bidualImage 𝕜 F) (bidualMap (a • T) ξ) =
      a • Submodule.Quotient.mk (p := bidualImage 𝕜 F) (bidualMap T ξ)
    rw [bidualMap_smul, ContinuousLinearMap.smul_apply, Submodule.Quotient.mk_smul]

theorem residuumOperator_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    residuumOperator (S.comp T) = (residuumOperator S).comp (residuumOperator T) := by
  apply ContinuousLinearMap.ext
  intro ξ
  induction ξ using Quotient.inductionOn' with
  | h ξ =>
    change Submodule.Quotient.mk (bidualMap (S.comp T) ξ) =
      Submodule.Quotient.mk (bidualMap S (bidualMap T ξ))
    rw [bidualMap_comp, ContinuousLinearMap.comp_apply]

theorem residuumOperator_add (S T : E →L[𝕜] F) :
    residuumOperator (S + T) = residuumOperator S + residuumOperator T := by
  apply ContinuousLinearMap.ext
  intro ξ
  induction ξ using Quotient.inductionOn' with
  | h ξ =>
    change Submodule.Quotient.mk (p := bidualImage 𝕜 F) (bidualMap (S + T) ξ) =
      Submodule.Quotient.mk (p := bidualImage 𝕜 F) (bidualMap S ξ) +
        Submodule.Quotient.mk (p := bidualImage 𝕜 F) (bidualMap T ξ)
    rw [bidualMap_add, ContinuousLinearMap.add_apply, Submodule.Quotient.mk_add]

theorem residuumOperator_zero : residuumOperator (0 : E →L[𝕜] F) = 0 :=
  (gantmacher_iff_residuum_eq_zero _).mp weaklyCompact_zero

theorem residuumOperator_id : residuumOperator (ContinuousLinearMap.id 𝕜 E) =
    ContinuousLinearMap.id 𝕜 (ResiduumSpace 𝕜 E) := by
  apply ContinuousLinearMap.ext
  intro ξ
  induction ξ using Quotient.inductionOn' with
  | h ξ =>
    change Submodule.Quotient.mk (p := bidualImage 𝕜 E)
      (bidualMap (ContinuousLinearMap.id 𝕜 E) ξ) = Submodule.Quotient.mk ξ
    congr 1

theorem residuumNorm_eq_norm (T : E →L[𝕜] F) :
    residuumNorm T = ‖residuumOperator T‖ := rfl

theorem residuumNorm_nonneg (T : E →L[𝕜] F) : 0 ≤ residuumNorm T :=
  norm_nonneg (residuumOperator T)

theorem residuumNorm_le_norm (T : E →L[𝕜] F) : residuumNorm T ≤ ‖T‖ := by
  exact (norm_quotientOperator_le (𝕜 := 𝕜)
    (E := StrongDual 𝕜 (StrongDual 𝕜 E)) (F := StrongDual 𝕜 (StrongDual 𝕜 F))
    (bidualImage 𝕜 E) (bidualImage 𝕜 F) (bidualMap T)
    (bidual_preserves_image T)).trans_eq (norm_bidualMap T)

theorem residuumNorm_le_weakEssentialNorm (T : E →L[𝕜] F) :
    residuumNorm T ≤ weakEssentialNorm T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
  · rintro r ⟨W, hW, rfl⟩
    have hzero : residuumOperator W = 0 := (gantmacher_iff_residuum_eq_zero W).mp hW
    have heq : residuumOperator (T - W) = residuumOperator T := by
      rw [residuumOperator_sub, hzero]
      exact sub_zero _
    calc
      residuumNorm T = residuumNorm (T - W) := by
        rw [residuumNorm_eq_norm, residuumNorm_eq_norm, heq]
      _ ≤ ‖T - W‖ := residuumNorm_le_norm _

theorem residuumNorm_comp_le (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    residuumNorm (S.comp T) ≤ residuumNorm S * residuumNorm T := by
  rw [residuumNorm_eq_norm, residuumOperator_comp, residuumNorm_eq_norm, residuumNorm_eq_norm]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem residuumNorm_comp_left_le (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    residuumNorm (S.comp T) ≤ ‖S‖ * residuumNorm T :=
  (residuumNorm_comp_le S T).trans
    (mul_le_mul_of_nonneg_right (residuumNorm_le_norm S) (residuumNorm_nonneg T))

theorem residuumNorm_comp_right_le (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    residuumNorm (S.comp T) ≤ residuumNorm S * ‖T‖ :=
  (residuumNorm_comp_le S T).trans
    (mul_le_mul_of_nonneg_left (residuumNorm_le_norm T) (residuumNorm_nonneg S))

end ThesisCommon
