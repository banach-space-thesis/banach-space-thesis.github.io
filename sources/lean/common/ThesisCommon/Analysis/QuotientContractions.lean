import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

/-! Continuous linear quotient maps with their actual quotient-norm bounds. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

def quotientMkL (S : Submodule 𝕜 E) : E →L[𝕜] E ⧸ S :=
  ⟨S.mkQ, continuous_quot_mk⟩

@[simp] theorem quotientMkL_apply (S : Submodule 𝕜 E) (x : E) :
    quotientMkL S x = Submodule.Quotient.mk x := rfl

theorem norm_quotientMkL_le (S : Submodule 𝕜 E) : ‖quotientMkL S‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using Submodule.Quotient.norm_mk_le S x

def quotientLiftL (S : Submodule 𝕜 E) (f : E →L[𝕜] F)
    (hf : S ≤ LinearMap.ker f.toLinearMap) : (E ⧸ S) →L[𝕜] F where
  toLinearMap := S.liftQ f.toLinearMap hf
  cont := S.isOpenQuotientMap_mkQ.continuous_comp_iff.mp f.continuous

@[simp] theorem quotientLiftL_mk (S : Submodule 𝕜 E) (f : E →L[𝕜] F)
    (hf : S ≤ LinearMap.ker f.toLinearMap) (x : E) :
    quotientLiftL S f hf (Submodule.Quotient.mk x) = f x := rfl

theorem norm_quotientLiftL_apply_le (S : Submodule 𝕜 E) (f : E →L[𝕜] F)
    (hf : S ≤ LinearMap.ker f.toLinearMap) (x : E ⧸ S) :
    ‖quotientLiftL S f hf x‖ ≤ ‖f‖ * ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < ‖f‖ + 1 := by positivity
  obtain ⟨a, ha, han⟩ := Submodule.Quotient.norm_mk_lt x (div_pos hε hden)
  rw [← ha, quotientLiftL_mk]
  have hfa := f.le_opNorm a
  have hmul := mul_le_mul_of_nonneg_left han.le (norm_nonneg f)
  have he : ‖f‖ * (ε / (‖f‖ + 1)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  rw [← ha] at hmul
  nlinarith

theorem norm_quotientLiftL_le (S : Submodule 𝕜 E) (f : E →L[𝕜] F)
    (hf : S ≤ LinearMap.ker f.toLinearMap) : ‖quotientLiftL S f hf‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
    (norm_quotientLiftL_apply_le S f hf)

def quotientMapL (S : Submodule 𝕜 E) (R : Submodule 𝕜 F) (f : E →L[𝕜] F)
    (hf : ∀ x ∈ S, f x ∈ R) : (E ⧸ S) →L[𝕜] F ⧸ R :=
  quotientLiftL S ((quotientMkL R).comp f) (by
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero R).mpr (hf x hx))

@[simp] theorem quotientMapL_mk (S : Submodule 𝕜 E) (R : Submodule 𝕜 F)
    (f : E →L[𝕜] F) (hf : ∀ x ∈ S, f x ∈ R) (x : E) :
    quotientMapL S R f hf (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

theorem norm_quotientMapL_le (S : Submodule 𝕜 E) (R : Submodule 𝕜 F)
    (f : E →L[𝕜] F) (hf : ∀ x ∈ S, f x ∈ R) :
    ‖quotientMapL S R f hf‖ ≤ ‖f‖ := by
  apply (norm_quotientLiftL_le _ _ _).trans
  calc
    ‖(quotientMkL R).comp f‖ ≤ ‖quotientMkL R‖ * ‖f‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right (norm_quotientMkL_le R) (norm_nonneg f)
    _ = ‖f‖ := one_mul _

end ThesisCommon
