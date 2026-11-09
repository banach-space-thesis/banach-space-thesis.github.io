import SurveyStatements.P4FinitePath

/-! The contractive path projections are the actual ordered basis projections. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set Finset Module

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {N : ℕ}

def finiteBasisPrefix [FiniteDimensional 𝕜 E] (b : Basis (Fin N) 𝕜 E)
    (k : Fin (N + 1)) : E →L[𝕜] E :=
  ∑ i ∈ univ.filter (fun i : Fin N => i.val < k.val),
    (b.coord i).toContinuousLinearMap.smulRight (b i)

@[simp] lemma finitePathBasis_repr (v : Fin N → E) (hv : ∀ i, v i ≠ 0)
    (f : FinitePathSpace (𝕜 := 𝕜) v) (i : Fin N) :
    (finitePathBasis v hv).repr f i = (finitePathEquiv v hv).symm f i := by
  simp [finitePathBasis, Basis.map_repr, Pi.basisFun_repr]

lemma finitePathBasis_prefix (v : Fin N → E) (hv : ∀ i, v i ≠ 0)
    (k : Fin (N + 1)) :
    finiteBasisPrefix (finitePathBasis (𝕜 := 𝕜) v hv) k = finitePathProjection v hv k := by
  apply ContinuousLinearMap.ext
  intro f
  apply (finitePathEquiv (𝕜 := 𝕜) v hv).symm.injective
  simp only [finiteBasisPrefix, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    Basis.coord_apply, finitePathBasis_repr, map_sum, map_smul,
    finitePathBasis, Basis.map_apply, LinearEquiv.symm_apply_apply]
  simp only [finitePathProjection, LinearMap.coe_toContinuousLinearMap',
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  ext i
  simp [Pi.basisFun_apply, Pi.single_apply, Finset.sum_pi_single, finiteCoefficientPrefix]

lemma finitePathBasis_prefix_norm_le_one (v : Fin N → E) (hv : ∀ i, v i ≠ 0)
    (k : Fin (N + 1)) :
    ‖finiteBasisPrefix (finitePathBasis (𝕜 := 𝕜) v hv) k‖ ≤ 1 := by
  rw [finitePathBasis_prefix]
  exact finitePathProjection_norm_le_one (𝕜 := 𝕜) v hv k

end SurveyStatements.P4
