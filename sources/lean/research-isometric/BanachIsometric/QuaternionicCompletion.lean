import BanachIsometric.QuaternionicNormReduction
import Mathlib.Analysis.InnerProductSpace.Completion

/-! Completion of a normed right quaternionic module retains the original
right action and norm. A given positive Hermitian norm square extends to a
complete positive Hermitian norm square, without `NormedSpace` over H. -/

namespace BanachIsometric.Quaternionic

open UniformSpace Set
open scoped Quaternion

noncomputable section

attribute [local instance] RestrictScalars.moduleOrig

section Pullback

variable {U W : Type*} [AddCommGroup U] [Module Hᵐᵒᵖ U]
    [AddCommGroup W] [Module Hᵐᵒᵖ W]

def HermitianForm.comap (h : HermitianForm W) (f : U →ₗ[Hᵐᵒᵖ] W) : HermitianForm U where
  form x y := h.form (f x) (f y)
  add_right x y z := by rw [f.map_add, h.add_right]
  mul_right x y a := by
    change h.form (f x) (f (MulOpposite.op a • y)) = _
    rw [f.map_smul]
    exact h.mul_right (f x) (f y) a
  star_symm x y := h.star_symm (f x) (f y)

end Pullback

section Normed

variable {V : Type*} [NormedAddCommGroup V] [Module Hᵐᵒᵖ V] [NormSMulClass Hᵐᵒᵖ V]

instance (priority := 100) uniformContinuousConstSMul_right : UniformContinuousConstSMul Hᵐᵒᵖ V where
  uniformContinuous_const_smul a := (lipschitzWith_smul a).uniformContinuous

theorem norm_smul_completion (a : Hᵐᵒᵖ) (x : Completion V) : ‖a • x‖ = ‖a‖ * ‖x‖ := by
  exact Completion.induction_on x
    (isClosed_eq (continuous_norm.comp (continuous_const_smul a)) (continuous_const.mul continuous_norm))
    (fun v => by simp only [← Completion.coe_smul, Completion.norm_coe, norm_smul])

instance completionNormSMulClass : NormSMulClass Hᵐᵒᵖ (Completion V) where
  norm_smul := norm_smul_completion

/-- The actual dense embedding preserves the original right action and norm. -/
def completionEmbedding : V →ₗᵢ[Hᵐᵒᵖ] Completion V := Completion.toComplₗᵢ

theorem completionEmbedding_denseRange : DenseRange (completionEmbedding (V := V)) :=
  Completion.denseRange_coe

/-- The real inner product is installed on the canonical restriction alias;
the preexisting norm is a parameter and is retained exactly. -/
def realInnerProductSpaceOfHermitian (h : HermitianForm V)
    (hdiag : ∀ x, h.form x x = (‖x‖ ^ 2 : ℝ)) :
    InnerProductSpace ℝ (RestrictScalars ℝ Hᵐᵒᵖ V) where
  __ := realNormedSpace (V := V)
  inner x y := (h.form x y).re
  norm_sq_eq_re_inner x := by
    change ‖x‖ ^ 2 = (h.form x x).re
    rw [hdiag, Quaternion.re_coe]
  conj_inner_symm x y := by
    change (h.form y x).re = (h.form x y).re
    simpa only [Quaternion.re_star] using (congrArg QuaternionAlgebra.re (h.star_symm x y)).symm
  add_left x y z := by
    change (h.form (x + y) z).re = (h.form x z).re + (h.form y z).re
    rw [h.add_left, Quaternion.re_add]
  smul_left x y r := by
    change (h.form (rightMul (x : V) (r : H)) y).re = r * (h.form x y).re
    rw [h.mul_left]
    simp

set_option maxHeartbeats 800000 in
theorem completion_hasHermitianSquare (hV : HasHermitianSquare (norm : V → ℝ)) :
    HasHermitianSquare (norm : Completion V → ℝ) := by
  obtain ⟨h, hdiag, _⟩ := hV
  letI : NormSMulClass Hᵐᵒᵖ (RestrictScalars ℝ Hᵐᵒᵖ V) :=
    (inferInstance : NormSMulClass Hᵐᵒᵖ V)
  letI : UniformContinuousConstSMul Hᵐᵒᵖ (RestrictScalars ℝ Hᵐᵒᵖ V) :=
    uniformContinuousConstSMul_right
  letI : InnerProductSpace ℝ (RestrictScalars ℝ Hᵐᵒᵖ V) := realInnerProductSpaceOfHermitian h hdiag
  let W := Completion (RestrictScalars ℝ Hᵐᵒᵖ V)
  let B := innerₗ W
  have hsym : ∀ x y : W, B x y = B y x := fun x y => real_inner_comm y x
  have hscale : ∀ (x : W) (a : H), B (rightMul x a) (rightMul x a) = Quaternion.normSq a * B x x := by
    intro x a
    change inner ℝ (rightMul x a) (rightMul x a) = Quaternion.normSq a * inner ℝ x x
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, rightMul, norm_smul,
      MulOpposite.norm_op, Quaternion.normSq_eq_norm_mul_self]
    ring
  have hpos : ∀ x : W, x ≠ 0 → 0 < B x x := by
    intro x hx
    change 0 < inner ℝ x x
    exact real_inner_self_pos.mpr hx
  obtain ⟨hC, hCdiag, _⟩ := existsUnique_of_realBilinear B hsym hscale hpos
  refine ⟨hC, ?_, hCdiag.2⟩
  intro x
  let xW : W := x
  have hx : hC.form xW xW = (‖xW‖ ^ 2 : ℝ) := by
    rw [hCdiag.1]
    change (inner ℝ xW xW : H) = (‖xW‖ ^ 2 : ℝ)
    rw [real_inner_self_eq_norm_sq]
  exact hx

/-- The extended norm square also extends the specified original Hermitian
form itself, by uniqueness of quaternionic polarization from the diagonal. -/
theorem exists_completion_hermitian_extension (h : HermitianForm V)
    (hdiag : ∀ x, h.form x x = (‖x‖ ^ 2 : ℝ)) (hpos : h.IsPositiveDefinite) :
    ∃ hC : HermitianForm (Completion V),
      (∀ x, hC.form x x = (‖x‖ ^ 2 : ℝ)) ∧ hC.IsPositiveDefinite ∧
      ∀ x y : V, hC.form (x : Completion V) (y : Completion V) = h.form x y := by
  obtain ⟨hC, hCdiag, hCpos⟩ := completion_hasHermitianSquare (V := V) ⟨h, hdiag, hpos⟩
  let hR := hC.comap (completionEmbedding (V := V)).toLinearMap
  have hRdiag : ∀ x : V, hR.form x x = (‖x‖ ^ 2 : ℝ) := by
    intro x
    change hC.form (x : Completion V) (x : Completion V) = _
    simpa only [Completion.norm_coe] using hCdiag (x : Completion V)
  refine ⟨hC, hCdiag, hCpos, ?_⟩
  intro x y
  exact (hR.form_eq_quaternionPolar hRdiag x y).trans (h.form_eq_quaternionPolar hdiag x y).symm

/-- Completeness together with a positive right Hermitian form inducing the
specified norm is the quaternionic Hilbert property used in Corollary B. -/
def IsHilbertForNorm : Prop := CompleteSpace V ∧ HasHermitianSquare (norm : V → ℝ)

theorem completion_isHilbertForNorm (hV : HasHermitianSquare (norm : V → ℝ)) :
    IsHilbertForNorm (V := Completion V) :=
  ⟨inferInstance, completion_hasHermitianSquare hV⟩

end Normed

end
end BanachIsometric.Quaternionic
