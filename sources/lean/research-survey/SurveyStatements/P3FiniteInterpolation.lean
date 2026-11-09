import SurveyStatements.P3Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Isomorphisms

/-! The finite-dimensional evaluation map needed by preadjoint extraction. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000

namespace SurveyStatements.P3

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Restrict evaluation at `x` to the given family of continuous functionals. -/
def finiteEvaluation (j : F →ₗᵢ[𝕜] (X →L[𝕜] 𝕜)) : X →L[𝕜] (F →L[𝕜] 𝕜) :=
  (adjoint j.toContinuousLinearMap).comp (NormedSpace.inclusionInDoubleDual 𝕜 X)

@[simp] theorem finiteEvaluation_apply (j : F →ₗᵢ[𝕜] (X →L[𝕜] 𝕜)) (x : X) (f : F) :
    finiteEvaluation j x f = j f x := rfl

/-- Every functional on a finite-dimensional family is exact evaluation at
some vector of the original space. This is algebraic finite-dimensional duality. -/
theorem finiteEvaluation_surjective (j : F →ₗᵢ[𝕜] (X →L[𝕜] 𝕜))
    [FiniteDimensional 𝕜 F] : Function.Surjective (finiteEvaluation j) := by
  let B : F →ₗ[𝕜] (X →ₗ[𝕜] 𝕜) := (ContinuousLinearMap.coeLM 𝕜).comp j.toLinearMap
  have hB : Function.Injective B := by
    intro f g hfg
    apply j.injective
    exact ContinuousLinearMap.coe_injective hfg
  have hflip : Function.Surjective B.flip :=
    (LinearMap.flip_surjective_iff₁ (B := B)).mpr hB
  intro φ
  obtain ⟨x, hx⟩ := hflip φ.toLinearMap
  refine ⟨x, ?_⟩
  ext f
  exact LinearMap.congr_fun hx f

/-- Open mapping supplies a uniform norm bound for finite interpolation.
This preliminary bound is weaker than the nearly isometric bound used by
the survey's diagonal construction. -/
theorem finite_interpolation_with_uniform_bound [CompleteSpace X]
    (j : F →ₗᵢ[𝕜] (X →L[𝕜] 𝕜)) [FiniteDimensional 𝕜 F] :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : F →L[𝕜] 𝕜,
      ∃ x : X, (∀ f : F, j f x = φ f) ∧ ‖x‖ ≤ C * ‖φ‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    (finiteEvaluation j).exists_preimage_norm_le (finiteEvaluation_surjective j)
  refine ⟨C, hC, ?_⟩
  intro φ
  obtain ⟨x, hx, hnorm⟩ := hbound φ
  exact ⟨x, fun f => congrArg (fun g : F →L[𝕜] 𝕜 => g f) hx, hnorm⟩

/-- Finite-dimensional continuous biduals consist of evaluations. -/
theorem finite_bidual_eq_evaluation {V : Type*} [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (ψ : (V →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
    ∃ v : V, ∀ f : V →L[𝕜] 𝕜, ψ f = f v := by
  let B : Module.Dual 𝕜 (Module.Dual 𝕜 V) :=
    ψ.toLinearMap.comp LinearMap.toContinuousLinearMap.toLinearMap
  refine ⟨(Module.evalEquiv 𝕜 V).symm B, ?_⟩
  intro f
  exact (Module.apply_evalEquiv_symm_apply 𝕜 V f.toLinearMap B).symm

/-- The adjoint of finite evaluation is isometric, the quantitative fact
underlying nearly isometric finite interpolation. -/
theorem norm_adjoint_finiteEvaluation (j : F →ₗᵢ[𝕜] (X →L[𝕜] 𝕜))
    [FiniteDimensional 𝕜 F] (ψ : (F →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
    ‖adjoint (finiteEvaluation j) ψ‖ = ‖ψ‖ := by
  obtain ⟨f, hf⟩ := finite_bidual_eq_evaluation ψ
  have hψ : ψ = NormedSpace.inclusionInDoubleDual 𝕜 F f := by
    ext g
    exact hf g
  have ha : adjoint (finiteEvaluation j) ψ = j f := by
    ext x
    exact hf (finiteEvaluation j x)
  rw [ha, j.norm_map, hψ]
  exact (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := F)).norm_map f |>.symm

/-- An onto map with finite-dimensional range and isometric adjoint is a
metric quotient: its preimages have norm arbitrarily close to the target norm. -/
theorem exists_preimage_norm_lt_of_adjoint_isometry
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (S : X →L[𝕜] V) (hS : Function.Surjective S)
    (hiso : ∀ f : V →L[𝕜] 𝕜, ‖adjoint S f‖ = ‖f‖)
    (v : V) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : X, S x = v ∧ ‖x‖ < ‖v‖ + ε := by
  let M : Submodule 𝕜 X := LinearMap.ker S
  letI : IsClosed (M : Set X) := ContinuousLinearMap.isClosed_ker S
  let e₀ : (X ⧸ M) ≃ₗ[𝕜] V := S.toLinearMap.quotKerEquivOfSurjective hS
  letI : FiniteDimensional 𝕜 (X ⧸ M) := e₀.symm.finiteDimensional
  let e : (X ⧸ M) ≃L[𝕜] V := e₀.toContinuousLinearEquiv
  have he (x : X) : e (quotientMap M x) = S x := rfl
  have he' (x : X) : e.symm (S x) = quotientMap M x := by
    rw [← he x, e.symm_apply_apply]
  have hnorm (z : X ⧸ M) : ‖z‖ ≤ ‖e z‖ := by
    apply NormedSpace.norm_le_dual_bound 𝕜 z (norm_nonneg _)
    intro p
    let f : V →L[𝕜] 𝕜 := p.comp e.symm.toContinuousLinearMap
    have hf : adjoint S f = adjoint (quotientMap M) p := by
      ext x
      change p (e.symm (S x)) = p (quotientMap M x)
      rw [he']
    have hn : ‖f‖ = ‖p‖ := by
      rw [← hiso f, hf, norm_adjoint_quotientMap]
    calc
      ‖p z‖ = ‖f (e z)‖ := by simp only [f, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, e.symm_apply_apply]
      _ ≤ ‖f‖ * ‖e z‖ := f.le_opNorm (e z)
      _ = ‖e z‖ * ‖p‖ := by rw [hn, mul_comm]
  obtain ⟨x, hx, hxnorm⟩ := Submodule.Quotient.norm_mk_lt (e.symm v) hε
  refine ⟨x, ?_, ?_⟩
  · rw [← he x]
    change e (Submodule.Quotient.mk x) = v
    rw [hx, e.apply_symm_apply]
  · have hz : ‖e.symm v‖ ≤ ‖v‖ := by simpa using hnorm (e.symm v)
    exact hxnorm.trans_le (add_le_add_right hz ε)

/-- The uniform factor-two finite interpolation used in the survey's
recursive construction. -/
theorem finite_interpolation_norm_le_two
    (j : F →ₗᵢ[𝕜] (X →L[𝕜] 𝕜)) [FiniteDimensional 𝕜 F]
    (φ : F →L[𝕜] 𝕜) :
    ∃ x : X, (∀ f : F, j f x = φ f) ∧ ‖x‖ ≤ 2 * ‖φ‖ := by
  by_cases hφ : φ = 0
  · exact ⟨0, by simp [hφ], by simp [hφ]⟩
  letI : FiniteDimensional 𝕜 (F →L[𝕜] 𝕜) :=
    FiniteDimensional.of_injective (ContinuousLinearMap.coeLM 𝕜)
      ContinuousLinearMap.coe_injective
  obtain ⟨x, hx, hnorm⟩ := exists_preimage_norm_lt_of_adjoint_isometry
    (finiteEvaluation j) (finiteEvaluation_surjective j) (norm_adjoint_finiteEvaluation j)
    φ (norm_pos_iff.mpr hφ)
  refine ⟨x, fun f => congrArg (fun g : F →L[𝕜] 𝕜 => g f) hx, ?_⟩
  simpa only [two_mul] using hnorm.le

end SurveyStatements.P3
