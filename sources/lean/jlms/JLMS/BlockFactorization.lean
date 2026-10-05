import JLMS.RosenthalRestriction
import JLMS.BlockCZeroProjection
import JLMS.PaperConstructions

/-!
# Quantitative factorization from weak-star-null normalized blocks

Rosenthal restriction supplies a bounded-below coordinate copy. The block
projection gives the exact strict product bound. Block existence is still
an explicit analytic hypothesis; this does not prove the no-l-one branch.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- The forward Arnott–Laustsen implication for the disjoint witnesses
used by this paper, assuming the explicitly stated normalized-block property. -/
theorem factorizationFromDisjointFunctions_of_blocks
    (hX : DualNormalizedBlockNull (𝕜 := 𝕜) (X := X))
    (T : CZero 𝕜 K →L[𝕜] X) (δ : ℝ) (hδ : 0 < δ)
    (h : UniformDisjointFunctionWitnesses T δ) :
    ∃ U : X →L[𝕜] cZero 𝕜, ∃ V : cZero 𝕜 →L[𝕜] CZero 𝕜 K,
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧
      ‖U‖ * ‖V‖ < 1 / δ := by
  obtain ⟨γ, hδγ, η, hunit, hd, hlarge⟩ := h
  let V₀ := disjointSynthesis η hunit hd
  let R := T.comp V₀
  let c := (δ + γ) / 2
  have hδc : δ < c := by dsimp [c]; linarith
  have hc : 0 < c := hδ.trans hδc
  have hcγ : c < γ := by dsimp [c]; linarith
  have hR (n : ℕ) : γ < ‖R (cZeroUnit 𝕜 n)‖ := by
    simpa only [R, V₀, ContinuousLinearMap.comp_apply, disjointSynthesis_unit] using hlarge n
  obtain ⟨s, hs, hrestriction⟩ := exists_cZero_restriction_bounded_below R hc hcγ hR
  let S := cZeroSubsequenceInsertion (𝕜 := 𝕜) s hs
  let J := R.comp S
  obtain ⟨U, A, hidentity, hU, hA⟩ :=
    exists_cZero_projection_of_blocks hX J hc hrestriction
  let V := V₀.comp (S.comp A)
  have hV : ‖V‖ ≤ 1 := by
    have hS := norm_cZeroSubsequenceInsertion_le (𝕜 := 𝕜) s hs
    have hV₀ := norm_disjointSynthesis_le η hunit hd
    have hSA : ‖S.comp A‖ ≤ 1 :=
      (S.opNorm_comp_le A).trans (by nlinarith [norm_nonneg S, norm_nonneg A])
    exact (V₀.opNorm_comp_le (S.comp A)).trans
      (by nlinarith [norm_nonneg V₀, norm_nonneg (S.comp A)])
  refine ⟨U, V, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro a
    exact congrArg (fun L : cZero 𝕜 →L[𝕜] cZero 𝕜 => L a) hidentity
  · calc
      ‖U‖ * ‖V‖ ≤ (1 / c) * 1 := mul_le_mul hU hV (norm_nonneg V) (one_div_pos.mpr hc).le
      _ = 1 / c := mul_one _
      _ < 1 / δ := one_div_lt_one_div_of_lt hδ hδc

/-- Conditional Theorem 1.6 assembly from the normalized-block property. -/
theorem theorem_1_6_of_blocks (hX : DualNormalizedBlockNull (𝕜 := 𝕜) (X := X)) :
    Theorem_1_6 𝕜 K X := by
  apply theorem_1_6_of_bridge
  intro _ T δ hδ hw
  exact factorizationFromDisjointFunctions_of_blocks hX T δ hδ hw

/-- Conditional Theorem 1.7 assembly from the normalized-block property. -/
theorem theorem_1_7_of_blocks (hX : DualNormalizedBlockNull (𝕜 := 𝕜) (X := X)) :
    Theorem_1_7 𝕜 K X := by
  apply theorem_1_7_of_bridge
  intro _ T δ hδ hw
  exact factorizationFromDisjointFunctions_of_blocks hX T δ hδ hw

end JLMS
