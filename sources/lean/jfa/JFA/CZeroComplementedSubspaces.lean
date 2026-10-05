import JFA.CZeroIdeals
import JFA.ProjectionCompact
import JFA.SeparableCZeroFactorization
import ThesisCommon.Analysis.PelczynskiDecomposition
import ThesisCommon.Analysis.CZeroSelfSimilarity

/-! Every infinite-dimensional complemented subspace of scalar c₀ is
isomorphic to c₀. The noncompact projection factors its identity; the actual
range/kernel splitting and countable self-similarity complete Pełczyński's
decomposition argument. This also classifies the separable projections on Y. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]

theorem cZero_projection_range_iso (P : cZero 𝕜 →L[𝕜] cZero 𝕜)
    (hP : P.comp P = P) (hR : ¬ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap)) :
    Isomorphic 𝕜 (LinearMap.range P.toLinearMap) (cZero 𝕜) := by
  have hPc : ¬ IsCompactOperator P :=
    fun h => hR ((projection_compact_iff_finiteDimensional P hP).mp h)
  obtain ⟨U, V, hUV⟩ := cZero_noncompact_factors_identity P hPc
  have hf : ThesisCommon.FactorsIdentity P (cZero 𝕜) := ⟨U, V, hUV⟩
  obtain ⟨U', ⟨eYX⟩⟩ := hf.projection_range_decomposition
  exact ⟨(ThesisCommon.cZeroDecompositionEquiv
    (ThesisCommon.cZeroFlattenEquiv (𝕜 := 𝕜) (X := 𝕜)).symm
    (ThesisCommon.projectionRangeKerEquiv P hP) eYX).symm⟩

theorem cZero_complemented_infinite_iso (W : Submodule 𝕜 (cZero 𝕜))
    (hW : IsComplemented 𝕜 (cZero 𝕜) W) (hWinf : ¬ FiniteDimensional 𝕜 W) :
    Isomorphic 𝕜 W (cZero 𝕜) := by
  obtain ⟨P, hP, hPW⟩ := hW
  rw [← hPW] at hWinf ⊢
  exact cZero_projection_range_iso P hP hWinf

theorem amplified_separable_projection_range_iso {𝒜 : Set (Set ℕ)}
    (h𝒜 : IsAlmostDisjoint 𝒜)
    (P : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜)
    (hP : P.comp P = P)
    (hsep : HasSeparableRange 𝕜 (AmplifiedMrowka 𝕜 𝒜) (AmplifiedMrowka 𝕜 𝒜) P)
    (hR : ¬ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap)) :
    Isomorphic 𝕜 (LinearMap.range P.toLinearMap) (cZero 𝕜) := by
  obtain ⟨A, B, hAB, _⟩ := amplified_separable_factors_cZero h𝒜 P hsep
  obtain ⟨W, hW, ⟨e⟩⟩ := projection_factorization_complemented P hP A B hAB.symm
  have hWinf : ¬ FiniteDimensional 𝕜 W := by
    intro hf
    letI := hf
    exact hR (FiniteDimensional.of_injective e.toLinearEquiv.toLinearMap e.injective)
  obtain ⟨f⟩ := cZero_complemented_infinite_iso W hW hWinf
  exact ⟨e.trans f⟩

end JFA
