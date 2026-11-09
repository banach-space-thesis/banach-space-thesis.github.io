import BanachIsometric.SkewFactorization
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Actual smoothness of the existing local logarithm and skew product
coordinates. The functions are the previously constructed IFT inverses,
rather than new functions supplied with a smoothness premise. This is an
analytic chart ingredient, not a higher-homotopy finiteness theorem. -/

noncomputable section
namespace BanachIsometric
open scoped Topology

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem contDiff_algebraExp : ContDiff ℝ ⊤ (NormedSpace.exp ℝ : A → A) :=
  contDiff_iff_contDiffAt.mpr (fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt)

theorem localAlgebraLog_contDiffAt_one : ContDiffAt ℝ ⊤ (localAlgebraLog A) 1 := by
  have hExp : ContDiffAt ℝ ⊤ (NormedSpace.exp ℝ : A → A) 0 := (contDiff_algebraExp A).contDiffAt
  have hDeriv : HasFDerivAt (NormedSpace.exp ℝ : A → A)
      (ContinuousLinearEquiv.refl ℝ A : A →L[ℝ] A) 0 := by
    simpa using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A)).hasFDerivAt
  have hInv := hExp.to_localInverse hDeriv (by simp)
  simpa only [ContDiffAt.localInverse, localAlgebraLog, NormedSpace.exp_zero] using hInv

namespace SkewFactorization

variable [StarRing A] [StarModule ℝ A] [ContinuousStar A]
    (U V : Submodule ℝ (Space A))

omit [ContinuousStar A] in
theorem expProduct_contDiff : ContDiff ℝ ⊤ (expProduct A U V) :=
  ((contDiff_algebraExp A).comp (firstInclusion A U V).contDiff).mul
    ((contDiff_algebraExp A).comp (secondInclusion A U V).contDiff)

theorem factorMap_contDiffAt_zero : ContDiffAt ℝ ⊤ (factorMap A U V) 0 := by
  have hLog : ContDiffAt ℝ ⊤ (localAlgebraLog A) (expProduct A U V 0) := by
    simpa only [expProduct_zero] using localAlgebraLog_contDiffAt_one A
  exact (projection A).contDiff.contDiffAt.comp 0
    (hLog.comp 0 (expProduct_contDiff A U V).contDiffAt)

variable [FiniteDimensional ℝ A]

theorem localInverse_contDiffAt_zero (hc : IsCompl U V) :
    ContDiffAt ℝ ⊤ (localInverse A U V hc) 0 := by
  have h := (factorMap_contDiffAt_zero A U V).to_localInverse
    (factorMap_hasStrictFDerivAt A U V hc).hasFDerivAt (by simp)
  simpa only [ContDiffAt.localInverse, localInverse, factorMap_zero] using h

theorem coordinates_contDiffAt_one (hc : IsCompl U V) :
    ContDiffAt ℝ ⊤ (coordinates A U V hc) 1 := by
  have hLogSkew : ContDiffAt ℝ ⊤ (logarithmicSkew A) 1 :=
    (projection A).contDiff.contDiffAt.comp 1 (localAlgebraLog_contDiffAt_one A)
  have hInv : ContDiffAt ℝ ⊤ (localInverse A U V hc) (logarithmicSkew A 1) := by
    simpa only [logarithmicSkew_one] using localInverse_contDiffAt_zero A U V hc
  exact hInv.comp 1 hLogSkew

end SkewFactorization
end BanachIsometric
