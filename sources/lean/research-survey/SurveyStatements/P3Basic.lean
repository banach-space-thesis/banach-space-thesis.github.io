import SurveyStatements.P3Definitions
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P3

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y P : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]

@[simp] theorem adjoint_apply (T : X →L[𝕜] Y) (f : Y →L[𝕜] 𝕜) (x : X) :
    adjoint T f x = f (T x) := rfl

@[simp] theorem adjoint_comp (T : X →L[𝕜] Y) (A : Y →L[𝕜] P) :
    adjoint (A.comp T) = (adjoint T).comp (adjoint A) := by
  ext f x
  rfl

/-- The algebraic final step of the source's quotient-factorization argument.
Every onto composition with infinite-dimensional target witnesses failure of
strict cosingularity, by taking the kernel of its left factor. -/
theorem not_strictlyCosingular_of_surjective_comp (T : X →L[𝕜] Y)
    (A : Y →L[𝕜] P) (hP : ¬ FiniteDimensional 𝕜 P)
    (hAT : Function.Surjective (A.comp T)) : ¬ IsStrictlyCosingular T := by
  let M : Submodule 𝕜 Y := LinearMap.ker A
  have hA : Function.Surjective A := fun p => by
    obtain ⟨x, hx⟩ := hAT p
    exact ⟨T x, hx⟩
  have hM : ¬ FiniteDimensional 𝕜 (Y ⧸ M) := by
    intro hfin
    letI := hfin
    let B : (Y ⧸ M) →ₗ[𝕜] P := M.liftQ A.toLinearMap le_rfl
    have hB : Function.Surjective B := by
      intro p
      obtain ⟨y, hy⟩ := hA p
      exact ⟨M.mkQ y, hy⟩
    exact hP (FiniteDimensional.of_surjective B hB)
  intro hT
  apply hT M (ContinuousLinearMap.isClosed_ker A) hM
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ y =>
    obtain ⟨x, hx⟩ := hAT (A y)
    refine ⟨x, ?_⟩
    apply (Submodule.Quotient.eq M).mpr
    change A (T x - y) = 0
    simpa only [map_sub, sub_eq_zero] using hx

/-- The theorem above directly applies to the quotient factorization in the source. -/
theorem not_strictlyCosingular_of_quotient_factorization (T : X →L[𝕜] Y)
    (A : Y →L[𝕜] P) (q : X →L[𝕜] P) (hP : ¬ FiniteDimensional 𝕜 P)
    (hq : Function.Surjective q) (hAT : A.comp T = q) : ¬ IsStrictlyCosingular T := by
  apply not_strictlyCosingular_of_surjective_comp T A hP
  rwa [hAT]

/-- Open mapping gives the quantitative lower bound for an adjoint of an
onto operator. No separability hypothesis is needed for this direction. -/
theorem adjoint_boundedBelow_of_surjective [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[𝕜] Y) (hT : Function.Surjective T) :
    IsBoundedBelowOn (adjoint T) ⊤ := by
  obtain ⟨C, hC, hbound⟩ := T.exists_preimage_norm_le hT
  refine ⟨C⁻¹, inv_pos.mpr hC, fun f _ => ?_⟩
  have hf : ‖f‖ ≤ C * ‖adjoint T f‖ := by
    apply f.opNorm_le_bound (mul_nonneg hC.le (norm_nonneg _))
    intro y
    obtain ⟨x, hx, hnorm⟩ := hbound y
    calc
      ‖f y‖ = ‖adjoint T f x‖ := by rw [adjoint_apply, hx]
      _ ≤ ‖adjoint T f‖ * ‖x‖ := (adjoint T f).le_opNorm x
      _ ≤ ‖adjoint T f‖ * (C * ‖y‖) :=
        mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = (C * ‖adjoint T f‖) * ‖y‖ := by rw [mul_left_comm, mul_assoc]
  calc
    C⁻¹ * ‖f‖ ≤ C⁻¹ * (C * ‖adjoint T f‖) :=
      mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr hC.le)
    _ = ‖adjoint T f‖ := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]

/-- Infinite-dimensional normed spaces have infinite-dimensional continuous
duals; Hahn--Banach supplies injectivity of the canonical bidual embedding. -/
theorem dual_infiniteDimensional (hX : ¬ FiniteDimensional 𝕜 X) :
    ¬ FiniteDimensional 𝕜 (X →L[𝕜] 𝕜) := by
  intro hdual
  letI := hdual
  letI : FiniteDimensional 𝕜 ((X →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    FiniteDimensional.of_injective (ContinuousLinearMap.coeLM 𝕜)
      ContinuousLinearMap.coe_injective
  exact hX (FiniteDimensional.of_injective (V₂ := (X →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := X)).toLinearMap
    (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := X)).injective)

/-- The quotient map, with its actual quotient norm. -/
def quotientMap (M : Submodule 𝕜 Y) : Y →L[𝕜] (Y ⧸ M) :=
  M.mkQ.mkContinuous 1 (fun y => by simpa using Submodule.Quotient.norm_mk_le M y)

@[simp] theorem quotientMap_apply (M : Submodule 𝕜 Y) (y : Y) :
    quotientMap M y = M.mkQ y := rfl

/-- A uniform estimate on representatives descends to the quotient norm. -/
theorem quotient_norm_bound (M : Submodule 𝕜 Y) [IsClosed (M : Set Y)]
    (f : (Y ⧸ M) → 𝕜) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ y : Y, ‖f (quotientMap M y)‖ ≤ C * ‖y‖) (z : Y ⧸ M) :
    ‖f z‖ ≤ C * ‖z‖ := by
  by_cases hzero : C = 0
  · obtain ⟨y, rfl⟩ := M.mkQ_surjective z
    simpa [hzero] using h y
  have hpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  by_contra hfail
  have hlt : C * ‖z‖ < ‖f z‖ := lt_of_not_ge hfail
  have hdiv : ‖z‖ < ‖f z‖ / C := (lt_div_iff₀' hpos).mpr hlt
  obtain ⟨y, hy, hynorm⟩ := Submodule.Quotient.norm_mk_lt z (sub_pos.mpr hdiv)
  have hynorm' : ‖y‖ < ‖f z‖ / C := by linarith
  have hybound := h y
  have hqy : quotientMap M y = z := hy
  rw [hqy] at hybound
  exact (lt_div_iff₀' hpos).mp hynorm' |>.not_ge hybound

/-- The adjoint of the quotient map is an isometry for the continuous-dual norm. -/
@[simp] theorem norm_adjoint_quotientMap (M : Submodule 𝕜 Y)
    [IsClosed (M : Set Y)] (f : (Y ⧸ M) →L[𝕜] 𝕜) :
    ‖adjoint (quotientMap M) f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (adjoint (quotientMap M) f).opNorm_le_bound (norm_nonneg f)
    intro y
    exact (f.le_opNorm (quotientMap M y)).trans
      (mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le M y) (norm_nonneg _))
  · apply f.opNorm_le_bound (norm_nonneg (adjoint (quotientMap M) f))
    exact quotient_norm_bound M f (norm_nonneg _)
      (fun y => (adjoint (quotientMap M) f).le_opNorm y)

/-- The closed isometric copy of the quotient dual in the original dual. -/
def quotientDualIsometry (M : Submodule 𝕜 Y) [IsClosed (M : Set Y)] :
    ((Y ⧸ M) →L[𝕜] 𝕜) →ₗᵢ[𝕜] (Y →L[𝕜] 𝕜) where
  toLinearMap := (adjoint (quotientMap M)).toLinearMap
  norm_map' := norm_adjoint_quotientMap M

/-- The implication from a strictly singular adjoint to strict cosingularity.
It holds without a separability assumption. -/
theorem strictlyCosingular_of_adjoint_strictlySingular
    [CompleteSpace X] [CompleteSpace Y] (T : X →L[𝕜] Y)
    (hT : IsStrictlySingular (adjoint T)) : IsStrictlyCosingular T := by
  intro M hclosed hinfinite hsurj
  letI : IsClosed (M : Set Y) := hclosed
  let q : Y →L[𝕜] (Y ⧸ M) := quotientMap M
  let J := quotientDualIsometry M
  let W : Submodule 𝕜 (Y →L[𝕜] 𝕜) := LinearMap.range J.toLinearMap
  have hWclosed : IsClosed (W : Set (Y →L[𝕜] 𝕜)) :=
    J.isometry.isClosedEmbedding.isClosed_range
  have hWinfinite : ¬ FiniteDimensional 𝕜 W := by
    intro hfinite
    letI := hfinite
    have hJinj : Function.Injective J.toLinearMap.rangeRestrict := by
      intro a b hab
      apply J.injective
      exact congrArg Subtype.val hab
    exact dual_infiniteDimensional hinfinite
      (FiniteDimensional.of_injective (V₂ := W) J.toLinearMap.rangeRestrict hJinj)
  have hsurj' : Function.Surjective (q.comp T) := hsurj
  obtain ⟨c, hc, hbound⟩ := adjoint_boundedBelow_of_surjective (q.comp T) hsurj'
  apply hT W hWclosed hWinfinite
  refine ⟨c, hc, ?_⟩
  intro g hg
  obtain ⟨f, rfl⟩ := hg
  have hb := hbound f (Submodule.mem_top)
  change c * ‖adjoint (quotientMap M) f‖ ≤ ‖adjoint T (adjoint (quotientMap M) f)‖
  rw [norm_adjoint_quotientMap]
  exact hb

end SurveyStatements.P3
