import JLMS.ConvergentNormingFactorization
import JLMS.CZeroNormingSequence
import JLMS.SectionEightReduced

/-!
# Sharp factorization for scattered C₀ codomains

Point norming, scattered compact sequential compactness, matrix selection,
pairing, and Neumann correction discharge the factorization bridge for
scattered C₀ codomains. In particular this closes the original Section 8
main theorems, including the finite-space cases.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K L : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
  [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L]

theorem factorizationFromDisjointFunctions_scatteredCZero (hL : IsScattered L)
    (T : CZero 𝕜 K →L[𝕜] CZero 𝕜 L) (δ : ℝ) (hδ : 0 < δ)
    (h : UniformDisjointFunctionWitnesses T δ) :
    ∃ U : CZero 𝕜 L →L[𝕜] cZero 𝕜, ∃ V : cZero 𝕜 →L[𝕜] CZero 𝕜 K,
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧ ‖U‖ * ‖V‖ < 1 / δ := by
  obtain ⟨γ, hδγ, η, hunit, hd, hlarge⟩ := h
  let V₀ := disjointSynthesis η hunit hd
  let R := T.comp V₀
  have hR (n : ℕ) : γ < ‖R (cZeroUnit 𝕜 n)‖ := by
    simpa only [R, V₀, ContinuousLinearMap.comp_apply, disjointSynthesis_unit] using hlarge n
  obtain ⟨φ, hφ, hdiag, ψ, r, hr, ht⟩ :=
    exists_convergent_CZero_normingSequence hL (fun n => R (cZeroUnit 𝕜 n)) (hδ.trans hδγ) hR
  obtain ⟨U, A, hidentity, hprod⟩ := factorization_of_convergent_norming R hδ hδγ φ hφ
    (fun n => (hdiag n).1.le) (fun n => (hdiag n).2) ψ r hr ht
  refine ⟨U, V₀.comp A, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro a
    exact congrArg (fun M : cZero 𝕜 →L[𝕜] cZero 𝕜 => M a) hidentity
  · apply lt_of_le_of_lt ?_ hprod
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg U)
    exact (V₀.opNorm_comp_le A).trans (by
      simpa using mul_le_mul_of_nonneg_right (norm_disjointSynthesis_le η hunit hd) (norm_nonneg A))

theorem theorem_1_6_of_scatteredCZero (hL : IsScattered L) :
    Theorem_1_6 𝕜 K (CZero 𝕜 L) := by
  apply theorem_1_6_of_bridge
  intro _ T δ hδ hw
  exact factorizationFromDisjointFunctions_scatteredCZero hL T δ hδ hw

theorem theorem_1_7_of_scatteredCZero (hL : IsScattered L) :
    Theorem_1_7 𝕜 K (CZero 𝕜 L) := by
  apply theorem_1_7_of_bridge
  intro _ T δ hδ hw
  exact factorizationFromDisjointFunctions_scatteredCZero hL T δ hδ hw

/-- The paper's Theorem 1.1, with exactly its original hypotheses. -/
theorem theorem_1_1 : Theorem_1_1 𝕜 K := by
  intro hK
  apply theorem_1_1_of_bridge _ hK
  intro _ T δ hδ hw
  exact factorizationFromDisjointFunctions_scatteredCZero hK T δ hδ hw

/-- The paper's Theorem 1.5, with exactly its original hypotheses. -/
theorem theorem_1_5 : Theorem_1_5 𝕜 K := by
  intro hK
  apply theorem_1_5_of_bridge _ hK
  intro _ T δ hδ hw
  exact factorizationFromDisjointFunctions_scatteredCZero hK T δ hδ hw

end JLMS
