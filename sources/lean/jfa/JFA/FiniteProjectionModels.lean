import JFA.AmplifiedNoncompactProjection
import JFA.FiniteCZeroTensor
import JFA.ModelUniqueness
import JFA.ProjectionComparisonAbsorption

/-! The nonzero compact scalar case. A compact projection has a positive
finite-dimensional scalar range, so its tensor lift has a positive finite
power of C₀(K_A) as its range. The separable remainder factors through c₀;
the comparison-kernel absorption identifies the original range with this
lifted range directly. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem compact_nonzero_projection_range_finite_power (Q : E →L[𝕜] E)
    (hQ : Q.comp Q = Q) (hk : IsCompactOperator Q) (hne : Q ≠ 0) :
    ∃ n : ℕ, Isomorphic 𝕜 (LinearMap.range Q.toLinearMap) (Fin (n + 1) → 𝕜) := by
  letI := (projection_compact_iff_finiteDimensional Q hQ).mp hk
  have hex : ∃ x, Q x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (ContinuousLinearMap.ext h)
  obtain ⟨x, hx⟩ := hex
  let z : LinearMap.range Q.toLinearMap := ⟨Q x, ⟨x, rfl⟩⟩
  have hz : z ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have hd : 0 < Module.finrank 𝕜 (LinearMap.range Q.toLinearMap) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨z, hz⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hd)
  have hn' : Module.finrank 𝕜 (LinearMap.range Q.toLinearMap) = n + 1 := hn
  exact ⟨n, ⟨(Module.finBasisOfFinrankEq 𝕜 (LinearMap.range Q.toLinearMap) hn').equivFun.toContinuousLinearEquiv⟩⟩

variable {𝒜 : Set (Set ℕ)}

theorem amplified_lift_compact_nonzero_projection_range_iso (h𝒜 : IsAlmostDisjoint 𝒜)
    (Q : cZero 𝕜 →L[𝕜] cZero 𝕜) (hQ : Q.comp Q = Q)
    (hk : IsCompactOperator Q) (hne : Q ≠ 0) :
    ∃ n : ℕ, Isomorphic 𝕜 (LinearMap.range (amplifiedTensorLift h𝒜 Q).toLinearMap)
      (Fin (n + 1) → MrowkaCZero 𝕜 𝒜) := by
  obtain ⟨n, ⟨e⟩⟩ := compact_nonzero_projection_range_finite_power Q hQ hk hne
  exact ⟨n, ⟨(amplifiedTensorProjectionRangeEquiv h𝒜 Q hQ).trans
    ((injectiveTensorEquiv (X := MrowkaCZero 𝕜 𝒜) e).trans
      (finitePowerTensorEquiv (𝕜 := 𝕜) (D := Fin (n + 1)) (X := MrowkaCZero 𝕜 𝒜)))⟩⟩

theorem amplified_nonzero_compact_scalar_projection_range_iso (h𝒜 : IsAlmostDisjoint 𝒜)
    (hc : HasContinuumSize 𝒜) (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (P : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) (hP : P.comp P = P)
    (hinf : ¬ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap))
    (hk : IsCompactOperator (amplifiedScalarOperator h𝒜 hc hfew P))
    (hne : amplifiedScalarOperator h𝒜 hc hfew P ≠ 0) :
    ∃ n : ℕ, Isomorphic 𝕜 (LinearMap.range P.toLinearMap) (Fin (n + 1) → MrowkaCZero 𝕜 𝒜) := by
  let Q := amplifiedScalarOperator h𝒜 hc hfew P
  let L := amplifiedTensorLift h𝒜 Q
  have hQ : Q.comp Q = Q := amplifiedScalarOperator_projection h𝒜 hc hfew P hP
  have hL : L.comp L = L := amplifiedTensorLift_projection h𝒜 Q hQ
  obtain ⟨n, ⟨eL⟩⟩ := amplified_lift_compact_nonzero_projection_range_iso h𝒜 Q hQ hk hne
  have hLinf : ¬ FiniteDimensional 𝕜 (LinearMap.range L.toLinearMap) := by
    intro hfin
    letI := hfin
    exact finitePower_nonseparable (mrowka_czero_nonseparable h𝒜 hc) n
      (isomorphic_separableSpace ⟨eL⟩ (inferInstance : SeparableSpace (LinearMap.range L.toLinearMap)))
  obtain ⟨UP, VP, hVP⟩ := amplified_complemented_infinite_contains_cZero_retract h𝒜
    (LinearMap.range P.toLinearMap) ⟨P, hP, rfl⟩ hinf
  obtain ⟨UL, VL, hVL⟩ := amplified_complemented_infinite_contains_cZero_retract h𝒜
    (LinearMap.range L.toLinearMap) ⟨L, hL, rfl⟩ hLinf
  obtain ⟨A, B, hAB, _⟩ := amplified_separable_factors_cZero h𝒜
    (amplifiedRemainder h𝒜 hc hfew P) (amplifiedRemainder_separable h𝒜 hc hfew P)
  have hBA : B.comp A = P - L := hAB.symm
  obtain ⟨e⟩ := projection_ranges_isomorphic_of_cZero_difference P L hP hL A B hBA
    UP VP hVP UL VL hVL
  exact ⟨n, ⟨e.trans eL⟩⟩

end JFA
