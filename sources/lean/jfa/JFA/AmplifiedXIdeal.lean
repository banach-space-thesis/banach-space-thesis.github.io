import JFA.AmplifiedIdealClassification
import JFA.SeparableCZeroFactorization
import JFA.FactorizationClosedIdeal
import JFA.AmplifiedCZeroRetracts

/-! A single coordinate projection of Y factors the identity of C₀(K_A).
Its scalar image is rank one. This bounds the closed factorisation ideal by
the compact preimage. A c₀ retract of C₀(K_A) puts the separable ideal inside;
the checked upper-ideal classification then identifies the two ideals. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology Set
open scoped TensorProduct
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]

theorem injectiveTensorMap_smulRight {E F X : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (φ : E →L[𝕜] 𝕜) (e : F) :
    injectiveTensorMap (X := X) (φ.smulRight e) =
      (injectivePureMap e).comp (leftSlice φ) := by
  apply injectiveTensor_ext
  intro f x
  simp only [injectiveTensorMap_pure, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, leftSlice_pure, injectivePureMap_apply]
  change injectiveInclusion 𝕜 F X ((φ f • e) ⊗ₜ[𝕜] x) =
    injectiveInclusion 𝕜 F X (e ⊗ₜ[𝕜] (φ f • x))
  rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]

variable {𝒜 : Set (Set ℕ)}

theorem mrowka_exists_cZero_retract (h𝒜 : IsAlmostDisjoint 𝒜) :
    ∃ A : cZero 𝕜 →L[𝕜] MrowkaCZero 𝕜 𝒜,
    ∃ B : MrowkaCZero 𝕜 𝒜 →L[𝕜] cZero 𝕜,
      B.comp A = ContinuousLinearMap.id 𝕜 (cZero 𝕜) := by
  letI := mrowka_locallyCompactSpace (𝒜 := 𝒜)
  letI := mrowka_t2Space h𝒜
  letI : Infinite (Mrowka 𝒜) := Infinite.of_injective
    (Sum.inl : ℕ → Mrowka 𝒜) Sum.inl_injective
  obtain ⟨A, B, hBA, _, _⟩ := JLMS.exists_cZero_retract (𝕜 := 𝕜) (K := Mrowka 𝒜)
    mrowka_isScattered
  exact ⟨A, B, hBA⟩

theorem amplified_exists_X_coordinate_retract (h𝒜 : IsAlmostDisjoint 𝒜) :
    ∃ J : MrowkaCZero 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜,
    ∃ R : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] MrowkaCZero 𝕜 𝒜,
      R.comp J = ContinuousLinearMap.id 𝕜 (MrowkaCZero 𝕜 𝒜) ∧
      J.comp R = amplifiedTensorLift h𝒜
        ((czeroEvaluation (𝕜 := 𝕜) 0).smulRight (czeroDelta 0)) := by
  let c := mrowkaAmplificationEquiv (𝕜 := 𝕜) h𝒜
  let J := c.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (injectivePureMap (X := MrowkaCZero 𝕜 𝒜) (czeroDelta (𝕜 := 𝕜) 0))
  let R := (leftSlice (X := MrowkaCZero 𝕜 𝒜) (czeroEvaluation (𝕜 := 𝕜) 0)).comp
    c.symm.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨J, R, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    simp only [J, R, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
      injectivePureMap_apply, leftSlice_pure]
    simp [czeroEvaluation, czeroDelta_apply]
  · apply ContinuousLinearMap.ext
    intro y
    simp only [J, R, amplifiedTensorLift, c, injectiveTensorMap_smulRight,
      ContinuousLinearMap.comp_apply]

theorem amplifiedCompactPreimage_closedIdeal (h𝒜 : IsAlmostDisjoint 𝒜)
    (hc : HasContinuumSize 𝒜) (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜)) :
    IsClosedOperatorIdeal 𝕜 (AmplifiedMrowka 𝕜 𝒜) (amplifiedCompactPreimage h𝒜 hc hfew) :=
  ((amplified_closedIdeal_classification_above_separable h𝒜 hc hfew _).mpr
    (Or.inr (Or.inl rfl))).1

theorem amplified_X_factorizations_subset_compactPreimage (h𝒜 : IsAlmostDisjoint 𝒜)
    (hc : HasContinuumSize 𝒜) (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜)) :
    factorizationOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) (MrowkaCZero 𝕜 𝒜) ⊆
      amplifiedCompactPreimage h𝒜 hc hfew := by
  letI := czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)
  obtain ⟨J, R, hRJ, hJR⟩ := amplified_exists_X_coordinate_retract (𝕜 := 𝕜) h𝒜
  have hP : J.comp R ∈ amplifiedCompactPreimage h𝒜 hc hfew := by
    rw [hJR]
    change IsCompactOperator (amplifiedScalarQuotient h𝒜 hc hfew
      (amplifiedTensorLift h𝒜 ((czeroEvaluation (𝕜 := 𝕜) 0).smulRight (czeroDelta 0))))
    change IsCompactOperator (epsilonScalarOperator (mrowka_czero_nonseparable h𝒜 hc) hfew
      (amplifiedConjugate h𝒜 (amplifiedTensorLift h𝒜
        ((czeroEvaluation (𝕜 := 𝕜) 0).smulRight (czeroDelta 0)))))
    rw [amplifiedConjugate_tensorLift, epsilonScalarOperator_tensorMap]
    exact JLMS.isCompactOperator_smulRight _ _
  apply factorizationOperators_subset_ideal_of_factors_identity
    (amplifiedCompactPreimage_closedIdeal h𝒜 hc hfew) hP R J
  apply ContinuousLinearMap.ext
  intro x
  have hx : R (J x) = x := congrArg (fun L => L x) hRJ
  change R (J (R (J x))) = x
  rw [hx, hx]

theorem amplified_closure_X_factorizations_eq_compactPreimage (h𝒜 : IsAlmostDisjoint 𝒜)
    (hc : HasContinuumSize 𝒜) (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜)) :
    closure (factorizationOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) (MrowkaCZero 𝕜 𝒜)) =
      amplifiedCompactPreimage h𝒜 hc hfew := by
  letI := czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)
  let I := closure (factorizationOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) (MrowkaCZero 𝕜 𝒜))
  have hI : IsClosedOperatorIdeal 𝕜 (AmplifiedMrowka 𝕜 𝒜) I :=
    closure_factorizationOperators_closedIdeal
  have hsub : I ⊆ amplifiedCompactPreimage h𝒜 hc hfew :=
    closure_minimal (amplified_X_factorizations_subset_compactPreimage h𝒜 hc hfew)
      (amplifiedCompactPreimage_closedIdeal h𝒜 hc hfew).1
  obtain ⟨A, B, hBA⟩ := mrowka_exists_cZero_retract (𝕜 := 𝕜) h𝒜
  have hsep : separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) ⊆ I := by
    rw [← amplified_factorizationOperators_eq_separableOperators h𝒜]
    exact (factorizationOperators_subset_of_retract A B hBA).trans subset_closure
  have hupper := (amplified_closedIdeal_classification_above_separable h𝒜 hc hfew I).mp ⟨hI, hsep⟩
  rcases hupper with hsmall | heq | hwhole
  · obtain ⟨J, R, _, hJR⟩ := amplified_exists_X_coordinate_retract (𝕜 := 𝕜) h𝒜
    have hmem : J.comp R ∈ I := subset_closure (Submodule.subset_span ⟨R, J, rfl⟩)
    rw [hsmall] at hmem
    have hz := (amplifiedScalarOperator_eq_zero_iff h𝒜 hc hfew (J.comp R)).mpr hmem
    rw [hJR] at hz
    change epsilonScalarOperator (mrowka_czero_nonseparable h𝒜 hc) hfew
      (amplifiedConjugate h𝒜 (amplifiedTensorLift h𝒜
        ((czeroEvaluation (𝕜 := 𝕜) 0).smulRight (czeroDelta 0)))) = 0 at hz
    rw [amplifiedConjugate_tensorLift, epsilonScalarOperator_tensorMap] at hz
    have he := congrArg (fun L : cZero 𝕜 →L[𝕜] cZero 𝕜 => L (czeroDelta 0) 0) hz
    simp [ContinuousLinearMap.smulRight_apply, czeroEvaluation, czeroDelta_apply] at he
  · exact heq
  · have hproper := (amplified_upper_ideals_strict (𝕜 := 𝕜) h𝒜 hc hfew).2
    exact False.elim (hproper.ne (subset_antisymm hproper.subset (hwhole ▸ hsub)))

end JFA
