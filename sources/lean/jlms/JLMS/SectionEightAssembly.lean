import JLMS.FactorizationAssembly
import JLMS.SimultaneousAssembly
import JLMS.CZeroBlocks

/-!
# Section 8: connecting the constructed blocks to the paper's results

The retract and admissibility of C₀(K) remain explicit background inputs.
Everything after the retract is constructed: the c₀ blocks, balanced maps,
convergent operator series and the minimality contradiction. The Bonsall
conclusion uses the same retract and the sharp Section 7 construction.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]

/-- The minimality assertion of Theorem 1.1. Complete uniqueness is a separate
consequence requiring the open-mapping argument for arbitrary complete norms. -/
theorem essentialNormIsMinimal_of_rudin_bridge_retract
    (hRudin : RudinRepresentation 𝕜 K)
    (hbridge : FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := CZero 𝕜 K))
    (hK : IsScattered K) (hX : AdmissibleCodomain 𝕜 (CZero 𝕜 K))
    (A : cZero 𝕜 →L[𝕜] CZero 𝕜 K) (B : CZero 𝕜 K →L[𝕜] cZero 𝕜)
    (hBA : B.comp A = ContinuousLinearMap.id 𝕜 (cZero 𝕜)) :
    EssentialNormIsMinimal 𝕜 (CZero 𝕜 K) := by
  apply essentialNormIsMinimal_of_factor_two (orthogonalRetracts_of_cZero_retract A B hBA)
  exact theorem_1_6_of_rudin_and_bridge hRudin hbridge hK hX

omit [LocallyCompactSpace K] [T2Space K] in
/-- Convert the below-threshold formulation of sharp factorizations to the
strict additive-epsilon estimate used in the Bonsall proof. -/
theorem sharp_factorization_epsilon (T : CZero 𝕜 K →L[𝕜] CZero 𝕜 K)
    (hsharp : SharpFactorizations T) (hd : 0 < dualEssentialNorm T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : CZero 𝕜 K →L[𝕜] cZero 𝕜, ∃ V : cZero 𝕜 →L[𝕜] CZero 𝕜 K,
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧
      ‖U‖ * ‖V‖ < 1 / dualEssentialNorm T + ε := by
  let δ : ℝ := 1 / (1 / dualEssentialNorm T + ε)
  have hden : 0 < 1 / dualEssentialNorm T + ε := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hden
  have hδd : δ < dualEssentialNorm T := by
    apply (div_lt_iff₀ hden).mpr
    have hcancel := one_div_mul_cancel (ne_of_gt hd)
    nlinarith
  obtain ⟨U, V, hUV, hnorm⟩ := hsharp δ hδ hδd
  refine ⟨U, V, hUV, ?_⟩
  simpa [δ] using hnorm

/-- The Bonsall conclusion of Theorem 1.5, from the cited background inputs
and the contractive retract of Lemma 8.1. -/
theorem bonsallMinimality_of_rudin_bridge_retract
    (hRudin : RudinRepresentation 𝕜 K)
    (hbridge : FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := CZero 𝕜 K))
    (hK : IsScattered K) (hX : AdmissibleCodomain 𝕜 (CZero 𝕜 K))
    (A : cZero 𝕜 →L[𝕜] CZero 𝕜 K) (B : CZero 𝕜 K →L[𝕜] cZero 𝕜)
    (hBA : B.comp A = ContinuousLinearMap.id 𝕜 (cZero 𝕜))
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    DualEssentialNormHasBonsallMinimality 𝕜 (CZero 𝕜 K) := by
  have hP : ¬ IsCompactOperator (A.comp B) := by
    have hc0 : ¬ IsCompactOperator (ContinuousLinearMap.id 𝕜 (cZero 𝕜)) :=
      fun h => cZero_not_finiteDimensional 𝕜 (finiteDimensional_of_compact_identity h)
    intro h
    have hc := (h.comp_clm A).clm_comp B
    change IsCompactOperator (B.comp ((A.comp B).comp A)) at hc
    have heq : B.comp ((A.comp B).comp A) = ContinuousLinearMap.id 𝕜 (cZero 𝕜) := by
      apply ContinuousLinearMap.ext
      intro f
      have hr (g : cZero 𝕜) : B (A g) = g := congrArg (fun L => L g) hBA
      exact (hr (B (A f))).trans (hr f)
    rw [heq] at hc
    exact hc0 hc
  apply bonsall_minimality_of_factorizations A B hBA hA hB hP
  intro T hd ε hε
  exact sharp_factorization_epsilon T
    (sharpFactorizations_of_disjointFunctions (disjointFunctionsSharp_of_rudin hRudin)
      hbridge hK hX T) hd hε

end JLMS
