import SurveyStatements.P4BaireAdjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Finite-rank adjoints are continuous from the weak-star topology to the
norm topology. These are the actual continuous approximants in the source's
parameter convexification argument. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 1024

open Set Topology Module
open scoped BigOperators

namespace SurveyStatements.P4

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A finite-rank operator's adjoint is norm continuous on the entire dual
equipped with its weak-star topology. -/
theorem finiteRank_adjoint_weakStar_norm_continuous (T : X →L[𝕜] Y)
    (hT : HasFiniteRank 𝕜 T) :
    Continuous (fun φ : WeakDual 𝕜 Y => banachAdjoint T (WeakDual.toStrongDual φ)) := by
  classical
  let R := LinearMap.range T.toLinearMap
  letI : FiniteDimensional 𝕜 R := hT
  let b := Module.finBasis 𝕜 R
  let ℓ : Fin (Module.finrank 𝕜 R) → StrongDual 𝕜 X :=
    fun i => (b.coord i).toContinuousLinearMap.comp T.rangeRestrict
  have heq : (fun φ : WeakDual 𝕜 Y => banachAdjoint T (WeakDual.toStrongDual φ)) =
      fun φ => ∑ i, φ (b i).val • ℓ i := by
    funext φ
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    change φ (T x) = ∑ i, φ (b i).val * b.repr (T.rangeRestrict x) i
    have h := congrArg (fun y : R => φ y.val) (b.sum_repr (T.rangeRestrict x))
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
      smul_eq_mul] at h
    calc
      φ (T x) = ∑ i, b.repr (T.rangeRestrict x) i * φ (b i).val := h.symm
      _ = _ := Finset.sum_congr rfl (fun i hi => mul_comm _ _)
  rw [heq]
  exact continuous_finset_sum _ (fun i _ => (WeakDual.eval_continuous (b i).val).smul
    continuous_const)

end SurveyStatements.P4
