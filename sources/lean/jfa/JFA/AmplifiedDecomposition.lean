import JFA.MrowkaSupport
import JFA.CZeroDiscreteProduct
import JFA.ProjectionScalar

/-! The decomposition on the actual amplified Mrowka function space. The
discrete tensor identification transports scalar extraction and its separable
remainder to C₀(ℕ × K_𝒜), including uniqueness and the projection consequence. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

def mrowkaAmplificationEquiv (h𝒜 : IsAlmostDisjoint 𝒜) :
    InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜) ≃ₗᵢ[𝕜] AmplifiedMrowka 𝕜 𝒜 := by
  letI := mrowka_t2Space h𝒜
  exact czeroDiscreteTensorEquiv

@[simp] theorem mrowkaAmplificationEquiv_pure (h𝒜 : IsAlmostDisjoint 𝒜)
    (f : cZero 𝕜) (g : MrowkaCZero 𝕜 𝒜) (p : ℕ × Mrowka 𝒜) :
    mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜 (injectivePure 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜) f g) p =
      f p.1 * g p.2 := by
  letI := mrowka_t2Space h𝒜
  exact czeroDiscreteTensorEquiv_pure f g p

def amplifiedConjugate (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) :
    InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜) →L[𝕜]
      InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜) :=
  (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜).toContinuousLinearEquiv.toContinuousLinearMap)

def amplifiedTensorLift (h𝒜 : IsAlmostDisjoint 𝒜) (U : cZero 𝕜 →L[𝕜] cZero 𝕜) :
    AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜 :=
  (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((injectiveTensorMap U).comp
      (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜).symm.toContinuousLinearEquiv.toContinuousLinearMap)

def amplifiedScalarOperator (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (T : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) : cZero 𝕜 →L[𝕜] cZero 𝕜 := by
  letI := czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)
  exact epsilonScalarOperator (mrowka_czero_nonseparable h𝒜 hc) hfew (amplifiedConjugate h𝒜 T)

def amplifiedRemainder (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (T : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) :
    AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜 :=
  T - amplifiedTensorLift h𝒜 (amplifiedScalarOperator h𝒜 hc hfew T)

theorem amplifiedRemainder_separable (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (T : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) :
    HasSeparableRange 𝕜 (AmplifiedMrowka 𝕜 𝒜) (AmplifiedMrowka 𝕜 𝒜)
      (amplifiedRemainder h𝒜 hc hfew T) := by
  letI := czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)
  let c := mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜
  let R := epsilonRemainder (mrowka_czero_nonseparable h𝒜 hc) hfew (amplifiedConjugate h𝒜 T)
  have hR := epsilonRemainder_separable (mrowka_czero_nonseparable h𝒜 hc) hfew
    (amplifiedConjugate h𝒜 T)
  have hsep : HasSeparableRange 𝕜 (AmplifiedMrowka 𝕜 𝒜) (AmplifiedMrowka 𝕜 𝒜)
      (c.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (R.comp c.symm.toContinuousLinearEquiv.toContinuousLinearMap)) := by
    apply HasSeparableRange.comp_left (𝕜 := 𝕜)
      (E := AmplifiedMrowka 𝕜 𝒜)
      (F := InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜))
      (G := AmplifiedMrowka 𝕜 𝒜)
    exact HasSeparableRange.comp_right (𝕜 := 𝕜)
      (E := AmplifiedMrowka 𝕜 𝒜)
      (F := InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜))
      (G := InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜)) hR _
  have heq : c.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (R.comp c.symm.toContinuousLinearEquiv.toContinuousLinearMap) =
        amplifiedRemainder h𝒜 hc hfew T := by
    apply ContinuousLinearMap.ext
    intro y
    simp only [R, c, epsilonRemainder, amplifiedConjugate, amplifiedRemainder,
      amplifiedTensorLift, amplifiedScalarOperator, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearMap.sub_apply, map_sub,
      LinearIsometryEquiv.apply_symm_apply]
  exact heq ▸ hsep

theorem amplified_decomposition (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (T : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) :
    ∃! d : (cZero 𝕜 →L[𝕜] cZero 𝕜) ×
        (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜),
      HasSeparableRange 𝕜 (AmplifiedMrowka 𝕜 𝒜) (AmplifiedMrowka 𝕜 𝒜) d.2 ∧
        T = amplifiedTensorLift h𝒜 d.1 + d.2 := by
  letI := czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)
  let c := mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜
  let U := amplifiedScalarOperator h𝒜 hc hfew T
  let S := amplifiedRemainder h𝒜 hc hfew T
  have hTS : T = amplifiedTensorLift h𝒜 U + S := by
    simp only [S, amplifiedRemainder, U, add_sub_cancel]
  refine ⟨(U, S), ⟨amplifiedRemainder_separable h𝒜 hc hfew T, hTS⟩, ?_⟩
  rintro ⟨V, R⟩ ⟨hR, hTR⟩
  have hR' : HasSeparableRange 𝕜
      (InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜))
      (InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜)) (amplifiedConjugate h𝒜 R) := by
    apply HasSeparableRange.comp_left (𝕜 := 𝕜)
      (E := InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜))
      (F := AmplifiedMrowka 𝕜 𝒜)
      (G := InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜))
    exact HasSeparableRange.comp_right (𝕜 := 𝕜)
      (E := InjectiveTensor 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜))
      (F := AmplifiedMrowka 𝕜 𝒜) (G := AmplifiedMrowka 𝕜 𝒜) hR _
  have hV : U = V := epsilonScalarOperator_of_decomposition
    (mrowka_czero_nonseparable h𝒜 hc) hfew (amplifiedConjugate h𝒜 T) V
      (amplifiedConjugate h𝒜 R) hR' (by
        intro f g
        have h := congrArg (fun A : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜 =>
          c.symm (A (c (injectivePure 𝕜 (cZero 𝕜) (MrowkaCZero 𝕜 𝒜) f g)))) hTR
        simpa only [amplifiedConjugate, amplifiedTensorLift, c,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          map_add, LinearIsometryEquiv.symm_apply_apply,
          injectiveTensorMap_pure] using h)
  apply Prod.ext hV.symm
  apply add_left_cancel (a := amplifiedTensorLift h𝒜 V)
  rw [← hTR, ← hV]
  exact hTS

theorem amplifiedScalarOperator_projection (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (P : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) (hP : P.comp P = P) :
    (amplifiedScalarOperator h𝒜 hc hfew P).comp (amplifiedScalarOperator h𝒜 hc hfew P) =
      amplifiedScalarOperator h𝒜 hc hfew P := by
  letI := czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)
  apply epsilonScalarOperator_projection
  apply ContinuousLinearMap.ext
  intro z
  have h := congrArg (fun A : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜 =>
    (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜).symm (A (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜 z))) hP
  simpa only [amplifiedConjugate, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply] using h

end JFA
