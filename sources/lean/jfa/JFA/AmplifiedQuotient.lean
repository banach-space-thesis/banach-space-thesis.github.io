import JFA.AmplifiedDecomposition
import JFA.EpsilonQuotient

/-! The scalar quotient on the original operator algebra B(C₀(ℕ × K_𝒜)).
It is contractive and surjective, preserves composition and identity, and its
kernel is exactly the ideal of operators with separable range. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

-- Explicit projections provide the pinned release's nested-operator instances.
local instance : NormedAddCommGroup (cZero 𝕜 →L[𝕜] cZero 𝕜) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜) :=
  ContinuousLinearMap.toNormedSpace
local instance : ContinuousAdd (cZero 𝕜 →L[𝕜] cZero 𝕜) :=
  (ContinuousLinearMap.topologicalAddGroup :
    IsTopologicalAddGroup (cZero 𝕜 →L[𝕜] cZero 𝕜)).toContinuousAdd
local instance : NormedAddCommGroup (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace 𝕜 (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) :=
  ContinuousLinearMap.toNormedSpace
local instance : Norm ((AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) →L[𝕜]
    (cZero 𝕜 →L[𝕜] cZero 𝕜)) := ContinuousLinearMap.hasOpNorm

theorem norm_amplifiedConjugate_le (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) :
    ‖amplifiedConjugate h𝒜 T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro z
  change ‖(mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜).symm
    (T (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜 z))‖ ≤ ‖T‖ * ‖z‖
  rw [LinearIsometryEquiv.norm_map]
  exact (T.le_opNorm _).trans_eq (by rw [LinearIsometryEquiv.norm_map])

def amplifiedConjugateL (h𝒜 : IsAlmostDisjoint 𝒜) :
    (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) →L[𝕜]
      (InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜) →L[𝕜]
        InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜)) :=
  LinearMap.mkContinuous
    (E := AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜)
    (F := InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜) →L[𝕜]
      InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜)) {
    toFun := amplifiedConjugate (𝕜 := 𝕜) h𝒜
    map_add' := by
      intro T Q
      apply ContinuousLinearMap.ext
      intro z
      change (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜).symm
        (T (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜 z) + Q (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜 z)) = _
      exact map_add _ _ _
    map_smul' := by
      intro a T
      apply ContinuousLinearMap.ext
      intro z
      change (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜).symm
        (a • T (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜 z)) = _
      exact map_smul _ _ _ }
    1 (fun T => by
      change ‖amplifiedConjugate h𝒜 T‖ ≤ 1 * ‖T‖
      simpa only [one_mul] using norm_amplifiedConjugate_le h𝒜 T)

def amplifiedScalarQuotient (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜)) :
    (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) →L[𝕜] (cZero 𝕜 →L[𝕜] cZero 𝕜) := by
  letI := czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)
  exact (epsilonScalarQuotient (E := cZero 𝕜) (F := cZero 𝕜)
    (mrowka_czero_nonseparable h𝒜 hc) hfew).comp (amplifiedConjugateL h𝒜)

@[simp] theorem amplifiedScalarQuotient_apply (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (T : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) :
    amplifiedScalarQuotient h𝒜 hc hfew T = amplifiedScalarOperator h𝒜 hc hfew T := rfl

theorem amplifiedConjugate_tensorLift (h𝒜 : IsAlmostDisjoint 𝒜)
    (U : cZero 𝕜 →L[𝕜] cZero 𝕜) :
    amplifiedConjugate h𝒜 (amplifiedTensorLift h𝒜 U) = injectiveTensorMap U := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [amplifiedConjugate, amplifiedTensorLift, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply]

theorem amplifiedScalarQuotient_surjective (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜)) :
    Function.Surjective (amplifiedScalarQuotient h𝒜 hc hfew) := by
  letI := czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)
  intro U
  refine ⟨amplifiedTensorLift h𝒜 U, ?_⟩
  change epsilonScalarOperator (mrowka_czero_nonseparable h𝒜 hc) hfew
    (amplifiedConjugate h𝒜 (amplifiedTensorLift h𝒜 U)) = U
  rw [amplifiedConjugate_tensorLift, epsilonScalarOperator_tensorMap]

theorem amplifiedScalarOperator_comp (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (T Q : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) :
    amplifiedScalarOperator h𝒜 hc hfew (Q.comp T) =
      (amplifiedScalarOperator h𝒜 hc hfew Q).comp (amplifiedScalarOperator h𝒜 hc hfew T) := by
  letI := czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)
  have heq : amplifiedConjugate h𝒜 (Q.comp T) =
      (amplifiedConjugate h𝒜 Q).comp (amplifiedConjugate h𝒜 T) := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [amplifiedConjugate, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.apply_symm_apply]
  change epsilonScalarOperator _ hfew (amplifiedConjugate h𝒜 (Q.comp T)) = _
  rw [heq, epsilonScalarOperator_comp]
  rfl

theorem amplifiedScalarOperator_eq_zero_iff (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (T : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) :
    amplifiedScalarOperator h𝒜 hc hfew T = 0 ↔
      HasSeparableRange 𝕜 (AmplifiedMrowka 𝕜 𝒜) (AmplifiedMrowka 𝕜 𝒜) T := by
  letI := czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)
  let c := mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜
  change epsilonScalarOperator _ hfew (amplifiedConjugate h𝒜 T) = 0 ↔ _
  rw [epsilonScalarOperator_eq_zero_iff]
  constructor
  · intro hT
    have hsep := HasSeparableRange.comp_left (𝕜 := 𝕜)
      (E := AmplifiedMrowka 𝕜 𝒜)
      (F := InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜)) (G := AmplifiedMrowka 𝕜 𝒜)
      (HasSeparableRange.comp_right (𝕜 := 𝕜) (E := AmplifiedMrowka 𝕜 𝒜)
        (F := InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜))
        (G := InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜)) hT
        c.symm.toContinuousLinearEquiv.toContinuousLinearMap) c.toContinuousLinearEquiv.toContinuousLinearMap
    have heq : c.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((amplifiedConjugate h𝒜 T).comp c.symm.toContinuousLinearEquiv.toContinuousLinearMap) = T := by
      apply ContinuousLinearMap.ext
      intro y
      simp only [c, amplifiedConjugate, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.apply_symm_apply]
    exact heq ▸ hsep
  · intro hT
    exact HasSeparableRange.comp_left (𝕜 := 𝕜)
      (E := InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜))
      (F := AmplifiedMrowka 𝕜 𝒜) (G := InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜))
      (HasSeparableRange.comp_right (𝕜 := 𝕜)
        (E := InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜))
        (F := AmplifiedMrowka 𝕜 𝒜) (G := AmplifiedMrowka 𝕜 𝒜) hT
        c.toContinuousLinearEquiv.toContinuousLinearMap) c.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem amplifiedScalarOperator_id (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜)) :
    amplifiedScalarOperator h𝒜 hc hfew (ContinuousLinearMap.id 𝕜 (AmplifiedMrowka 𝕜 𝒜)) =
      ContinuousLinearMap.id 𝕜 (cZero 𝕜) := by
  letI := czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)
  have heq : amplifiedConjugate h𝒜 (ContinuousLinearMap.id 𝕜 (AmplifiedMrowka 𝕜 𝒜)) =
      ContinuousLinearMap.id 𝕜 (InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜)) := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [amplifiedConjugate, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply]
  change epsilonScalarOperator _ hfew (amplifiedConjugate h𝒜 _) = _
  rw [heq, epsilonScalarOperator_id]

theorem norm_amplifiedScalarQuotient_le (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜)) :
    ‖amplifiedScalarQuotient h𝒜 hc hfew‖ ≤ 1 := by
  letI := czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  rw [one_mul, amplifiedScalarQuotient_apply]
  exact (norm_epsilonScalarOperator_le (mrowka_czero_nonseparable h𝒜 hc) hfew
    (amplifiedConjugate h𝒜 T)).trans (norm_amplifiedConjugate_le h𝒜 T)

def amplifiedScalarAlgebraHom (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜)) :
    (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) →ₐ[𝕜] (cZero 𝕜 →L[𝕜] cZero 𝕜) where
  toFun := amplifiedScalarQuotient h𝒜 hc hfew
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    simpa only [ContinuousLinearMap.one_def, amplifiedScalarQuotient_apply] using
      amplifiedScalarOperator_id h𝒜 hc hfew
  map_mul' := by
    intro T Q
    simpa only [ContinuousLinearMap.mul_def, amplifiedScalarQuotient_apply] using
      amplifiedScalarOperator_comp h𝒜 hc hfew Q T
  commutes' := by
    intro a
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, ContinuousLinearMap.one_def,
      amplifiedScalarQuotient_apply, amplifiedScalarOperator_id]

end JFA
