import JFA.ModelUniqueness
import JFA.AmplifiedNoncompactProjection
import JFA.MainStatements

/-! Case assembly for Theorem 1.4. This helper takes the nonzero compact
scalar case as an explicit premise. FiniteProjectionModels.lean proves that
case; ComplementedClassification.lean supplies it to obtain the unconditional
numbered theorem. The other existence cases and uniqueness are supplied here
by checked proof constants. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

theorem theorem_1_4_of_nonzero_compact_scalar_case
    (hfinite : ∀ (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
      (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
      (P : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜),
      P.comp P = P → ¬ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap) →
      IsCompactOperator (amplifiedScalarOperator h𝒜 hc hfew P) →
      amplifiedScalarOperator h𝒜 hc hfew P ≠ 0 →
      ∃ n : ℕ, Isomorphic 𝕜 (LinearMap.range P.toLinearMap)
        (Fin (n + 1) → MrowkaCZero 𝕜 𝒜)) :
    Theorem_1_4 𝕜 𝒜 := by
  classical
  unfold Theorem_1_4
  intro h𝒜 hc hfew W hW hWinf
  obtain ⟨P, hP, hPW⟩ := hW
  rw [← hPW] at hWinf ⊢
  have hex : ∃ c : ComplementedModel,
      IsModel 𝕜 (MrowkaCZero 𝕜 𝒜) (AmplifiedMrowka 𝕜 𝒜)
        (LinearMap.range P.toLinearMap) c := by
    by_cases hz : amplifiedScalarOperator h𝒜 hc hfew P = 0
    · exact ⟨.c0, amplified_projection_scalar_zero_range_iso h𝒜 hc hfew P hP hz hWinf⟩
    by_cases hk : IsCompactOperator (amplifiedScalarOperator h𝒜 hc hfew P)
    · obtain ⟨n, hn⟩ := hfinite h𝒜 hc hfew P hP hWinf hk hz
      exact ⟨.finitePower n, hn⟩
    · exact ⟨.whole, amplified_noncompact_scalar_projection_range_iso h𝒜 hc hfew P hP hk hWinf⟩
  obtain ⟨c, hWc⟩ := hex
  exact ⟨c, hWc, fun d hWd => amplified_model_unique h𝒜 hc hfew hWd hWc⟩

end JFA
