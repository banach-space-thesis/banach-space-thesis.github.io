import JFA.ProjectionComparison
import JFA.TensorProjectionRange
import JFA.AmplifiedProjectionCases

/-! The infinite-rank scalar case of Theorem 1.4. The range of the lifted
scalar projection is Y because its c₀ range is c₀. Its difference from the
original projection factors through c₀. Stabilized range embeddings and
countable self-similarity give the required isomorphism of ranges. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

theorem amplifiedTensorLift_projection (h𝒜 : IsAlmostDisjoint 𝒜)
    (Q : cZero 𝕜 →L[𝕜] cZero 𝕜) (hQ : Q.comp Q = Q) :
    (amplifiedTensorLift h𝒜 Q).comp (amplifiedTensorLift h𝒜 Q) = amplifiedTensorLift h𝒜 Q := by
  apply ContinuousLinearMap.ext
  intro y
  let c := mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜
  have hz := congrArg (fun L => L (c.symm y)) (injectiveTensorMap_projection
    (X := MrowkaCZero 𝕜 𝒜) Q hQ)
  change c (injectiveTensorMap Q (c.symm (c (injectiveTensorMap Q (c.symm y))))) =
    c (injectiveTensorMap Q (c.symm y))
  rw [c.symm_apply_apply]
  exact congrArg c hz

def amplifiedTensorProjectionRangeEquiv (h𝒜 : IsAlmostDisjoint 𝒜)
    (Q : cZero 𝕜 →L[𝕜] cZero 𝕜) (hQ : Q.comp Q = Q) :
    LinearMap.range (amplifiedTensorLift h𝒜 Q).toLinearMap ≃L[𝕜]
      InjectiveTensor 𝕜 (LinearMap.range Q.toLinearMap) (MrowkaCZero 𝕜 𝒜) :=
  (conjugateProjectionRangeEquiv (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜).toContinuousLinearEquiv
    (injectiveTensorMap Q) (amplifiedTensorLift h𝒜 Q) rfl).symm.trans
      (injectiveTensorProjectionRangeEquiv Q hQ)

def amplifiedSequenceSelfSimilarEquiv (h𝒜 : IsAlmostDisjoint 𝒜) :
    AmplifiedMrowka 𝕜 𝒜 ≃L[𝕜] C₀(ℕ, AmplifiedMrowka 𝕜 𝒜) := by
  letI := mrowka_t2Space h𝒜
  let e := (czeroDiscreteProductEquiv (𝕜 := 𝕜) (D := ℕ) (L := Mrowka 𝒜)).toContinuousLinearEquiv
  exact e.trans ((ThesisCommon.cZeroFlattenEquiv (𝕜 := 𝕜) (X := MrowkaCZero 𝕜 𝒜)).symm.trans
    (ThesisCommon.cZeroMapEquiv (ι := ℕ) e.symm))

theorem amplified_lift_noncompact_projection_range_iso (h𝒜 : IsAlmostDisjoint 𝒜)
    (Q : cZero 𝕜 →L[𝕜] cZero 𝕜) (hQ : Q.comp Q = Q) (hnc : ¬ IsCompactOperator Q) :
    Isomorphic 𝕜 (LinearMap.range (amplifiedTensorLift h𝒜 Q).toLinearMap)
      (AmplifiedMrowka 𝕜 𝒜) := by
  have hinf : ¬ FiniteDimensional 𝕜 (LinearMap.range Q.toLinearMap) :=
    fun h => hnc ((projection_compact_iff_finiteDimensional Q hQ).mpr h)
  obtain ⟨e⟩ := cZero_projection_range_iso Q hQ hinf
  exact ⟨(amplifiedTensorProjectionRangeEquiv h𝒜 Q hQ).trans
    ((injectiveTensorEquiv (X := MrowkaCZero 𝕜 𝒜) e).trans
      (mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜).toContinuousLinearEquiv)⟩

theorem amplified_not_finiteDimensional (h𝒜 : IsAlmostDisjoint 𝒜) :
    ¬ FiniteDimensional 𝕜 (AmplifiedMrowka 𝕜 𝒜) := by
  intro hfin
  letI := hfin
  obtain ⟨A, B, hBA, _, _⟩ := amplified_exists_cZero_retract (𝕜 := 𝕜) h𝒜
  have hleft : Function.LeftInverse B A := fun x => congrArg (fun L => L x) hBA
  exact JLMS.cZero_not_finiteDimensional 𝕜
    (FiniteDimensional.of_injective A.toLinearMap hleft.injective)

theorem amplified_noncompact_scalar_projection_range_iso (h𝒜 : IsAlmostDisjoint 𝒜)
    (hc : HasContinuumSize 𝒜) (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (P : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) (hP : P.comp P = P)
    (hnc : ¬ IsCompactOperator (amplifiedScalarOperator h𝒜 hc hfew P))
    (hinf : ¬ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap)) :
    Isomorphic 𝕜 (LinearMap.range P.toLinearMap) (AmplifiedMrowka 𝕜 𝒜) := by
  let Q := amplifiedScalarOperator h𝒜 hc hfew P
  let L := amplifiedTensorLift h𝒜 Q
  have hQ : Q.comp Q = Q := amplifiedScalarOperator_projection h𝒜 hc hfew P hP
  have hL : L.comp L = L := amplifiedTensorLift_projection h𝒜 Q hQ
  obtain ⟨eL⟩ := amplified_lift_noncompact_projection_range_iso h𝒜 Q hQ hnc
  have hLinf : ¬ FiniteDimensional 𝕜 (LinearMap.range L.toLinearMap) := by
    intro hfin
    letI := hfin
    exact amplified_not_finiteDimensional h𝒜
      (FiniteDimensional.of_injective eL.symm.toLinearEquiv.toLinearMap eL.symm.injective)
  let eRep := eL.trans ((amplifiedSequenceSelfSimilarEquiv h𝒜).trans
    (ThesisCommon.cZeroMapEquiv (ι := ℕ) eL.symm))
  obtain ⟨UP, VP, hVP⟩ := amplified_complemented_infinite_contains_cZero_retract h𝒜
    (LinearMap.range P.toLinearMap) ⟨P, hP, rfl⟩ hinf
  obtain ⟨UL, VL, hVL⟩ := amplified_complemented_infinite_contains_cZero_retract h𝒜
    (LinearMap.range L.toLinearMap) ⟨L, hL, rfl⟩ hLinf
  obtain ⟨A, B, hAB, _⟩ := amplified_separable_factors_cZero h𝒜
    (amplifiedRemainder h𝒜 hc hfew P) (amplifiedRemainder_separable h𝒜 hc hfew P)
  have hBA : B.comp A = P - L := hAB.symm
  obtain ⟨e⟩ := projection_range_iso_of_cZero_difference P L hP hL A B hBA eRep
    UP VP hVP UL VL hVL
  exact ⟨e.trans eL⟩

end JFA
