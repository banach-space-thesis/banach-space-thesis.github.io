import JFA.CZeroAbsorption
import JFA.AmplifiedCZeroRetracts
import JFA.AmplifiedQuotient

/-! The zero and identity scalar-projection cases in the complemented-subspace
classification. The identity case absorbs the actual complementary range,
which is a complemented subspace of c₀ after factorisation. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

theorem amplified_complement_separable_projection_range_iso (h𝒜 : IsAlmostDisjoint 𝒜)
    (P : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜)
    (hP : P.comp P = P)
    (hsep : HasSeparableRange 𝕜 (AmplifiedMrowka 𝕜 𝒜) (AmplifiedMrowka 𝕜 𝒜)
      (ContinuousLinearMap.id 𝕜 (AmplifiedMrowka 𝕜 𝒜) - P))
    (hR : ¬ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap)) :
    Isomorphic 𝕜 (LinearMap.range P.toLinearMap) (AmplifiedMrowka 𝕜 𝒜) := by
  obtain ⟨A, B, hAB, _⟩ := amplified_separable_factors_cZero h𝒜 _ hsep
  obtain ⟨U, V, hVU⟩ := amplified_complemented_infinite_contains_cZero_retract h𝒜
    (LinearMap.range P.toLinearMap) ⟨P, hP, rfl⟩ hR
  exact projection_range_iso_of_complement_factors_cZero P hP A B hAB.symm U V hVU

theorem amplified_projection_scalar_zero_range_iso (h𝒜 : IsAlmostDisjoint 𝒜)
    (hc : HasContinuumSize 𝒜) (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (P : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜)
    (hP : P.comp P = P) (hz : amplifiedScalarOperator h𝒜 hc hfew P = 0)
    (hR : ¬ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap)) :
    Isomorphic 𝕜 (LinearMap.range P.toLinearMap) (cZero 𝕜) :=
  amplified_separable_projection_range_iso h𝒜 P hP
    ((amplifiedScalarOperator_eq_zero_iff h𝒜 hc hfew P).mp hz) hR

theorem amplified_projection_scalar_identity_range_iso (h𝒜 : IsAlmostDisjoint 𝒜)
    (hc : HasContinuumSize 𝒜) (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (P : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜)
    (hP : P.comp P = P)
    (hid : amplifiedScalarOperator h𝒜 hc hfew P = ContinuousLinearMap.id 𝕜 (cZero 𝕜))
    (hR : ¬ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap)) :
    Isomorphic 𝕜 (LinearMap.range P.toLinearMap) (AmplifiedMrowka 𝕜 𝒜) := by
  apply amplified_complement_separable_projection_range_iso h𝒜 P hP _ hR
  apply (amplifiedScalarOperator_eq_zero_iff h𝒜 hc hfew _).mp
  change amplifiedScalarQuotient h𝒜 hc hfew
    (ContinuousLinearMap.id 𝕜 (AmplifiedMrowka 𝕜 𝒜) - P) = 0
  rw [map_sub]
  change amplifiedScalarOperator h𝒜 hc hfew
    (ContinuousLinearMap.id 𝕜 (AmplifiedMrowka 𝕜 𝒜)) -
      amplifiedScalarOperator h𝒜 hc hfew P = 0
  rw [amplifiedScalarOperator_id, hid, sub_self]

end JFA
