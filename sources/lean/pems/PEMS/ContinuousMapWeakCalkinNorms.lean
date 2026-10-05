import PEMS.GenericFactorizationNormConsequences
import PEMS.CZeroFactorizationClauses
import PEMS.ContinuousMapCZeroFixing
import ThesisCommon.Analysis.CZeroInfinityAlgebraGeometry
import ThesisCommon.Analysis.ContinuousMapAdjointApproximation

/-! Full real and complex C(K) algebra-norm corollaries. All factorization
and self-copy geometry is discharged by actual constructions. In particular
the competing norms are arbitrary, and need not be complete or continuous. -/
noncomputable section
open ThesisCommon
namespace PEMS
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

theorem dualWeakEssentialNorm_eq_cZero_factorization_real [SeqCompactSpace K]
    (T : C(K, ℝ) →L[ℝ] C(K, ℝ)) :
    dualWeakEssentialNorm T = factorizationSup (CZero ℝ) T :=
  (dualWeakEssentialNorm_eq_fixesCZeroSup_real T).trans
    (fixesCZeroSup_eq_factorizationSup_cZero_sequentiallyCompact T)

theorem dualWeakEssentialNorm_eq_cZero_factorization_complex [SeqCompactSpace K]
    (T : C(K, ℂ) →L[ℂ] C(K, ℂ)) :
    dualWeakEssentialNorm T = factorizationSup (CZero ℂ) T :=
  (dualWeakEssentialNorm_eq_fixesCZeroSup_complex T).trans
    (fixesCZeroSup_eq_factorizationSup_cZero_sequentiallyCompact T)

theorem weakEssentialNorm_eq_infinity_factorization_real [ExtremallyDisconnected K]
    (T : C(K, ℝ) →L[ℝ] C(K, ℝ)) :
    weakEssentialNorm T = factorizationSup (EllInfinity ℝ) T :=
  (weakEssentialNorm_banachAdjoint_eq_continuousMap T).symm.trans
    ((dualWeakEssentialNorm_eq_fixesCZeroSup_real T).trans
      (fixesCZeroSup_eq_factorizationSup_infinity_extremallyDisconnected T))

theorem weakEssentialNorm_eq_infinity_factorization_complex [ExtremallyDisconnected K]
    (T : C(K, ℂ) →L[ℂ] C(K, ℂ)) :
    weakEssentialNorm T = factorizationSup (EllInfinity ℂ) T :=
  (weakEssentialNorm_banachAdjoint_eq_continuousMap T).symm.trans
    ((dualWeakEssentialNorm_eq_fixesCZeroSup_complex T).trans
      (fixesCZeroSup_eq_factorizationSup_infinity_extremallyDisconnected T))

theorem corollary_1_8_real : Corollary_1_8 (𝕜 := ℝ) K := by
  intro hK
  letI := hK
  obtain ⟨I, Q, hd, ho⟩ := exists_orthogonal_selfCopies_ellInfinity (𝕜 := ℝ)
  exact minimal_weakEssentialNorm_of_generic_factorization not_weaklyCompact_id_ellInfinity
    I Q hd ho weakEssentialNorm_eq_infinity_factorization_real

theorem corollary_1_8_complex : Corollary_1_8 (𝕜 := ℂ) K := by
  intro hK
  letI := hK
  obtain ⟨I, Q, hd, ho⟩ := exists_orthogonal_selfCopies_ellInfinity (𝕜 := ℂ)
  exact minimal_weakEssentialNorm_of_generic_factorization not_weaklyCompact_id_ellInfinity
    I Q hd ho weakEssentialNorm_eq_infinity_factorization_complex

theorem corollary_1_9_real : Corollary_1_9 (𝕜 := ℝ) K := by
  intro hK
  letI := hK
  obtain ⟨I, Q, hd, ho⟩ := exists_orthogonal_selfCopies_cZero (𝕜 := ℝ)
  exact minimal_dualWeakEssentialNorm_of_generic_factorization not_weaklyCompact_id_cZero
    I Q hd ho dualWeakEssentialNorm_eq_cZero_factorization_real

theorem corollary_1_9_complex : Corollary_1_9 (𝕜 := ℂ) K := by
  intro hK
  letI := hK
  obtain ⟨I, Q, hd, ho⟩ := exists_orthogonal_selfCopies_cZero (𝕜 := ℂ)
  exact minimal_dualWeakEssentialNorm_of_generic_factorization not_weaklyCompact_id_cZero
    I Q hd ho dualWeakEssentialNorm_eq_cZero_factorization_complex

theorem corollary_1_12_real : Corollary_1_12 (𝕜 := ℝ) K := by
  intro hK
  letI := hK
  exact bonsall_weakEssentialNorm_of_generic_factorization not_weaklyCompact_id_ellInfinity
    weakEssentialNorm_eq_infinity_factorization_real

theorem corollary_1_12_complex : Corollary_1_12 (𝕜 := ℂ) K := by
  intro hK
  letI := hK
  exact bonsall_weakEssentialNorm_of_generic_factorization not_weaklyCompact_id_ellInfinity
    weakEssentialNorm_eq_infinity_factorization_complex

theorem corollary_1_13_real : Corollary_1_13 (𝕜 := ℝ) K := by
  intro hK
  letI := hK
  exact bonsall_dualWeakEssentialNorm_of_generic_factorization not_weaklyCompact_id_cZero
    dualWeakEssentialNorm_eq_cZero_factorization_real

theorem corollary_1_13_complex : Corollary_1_13 (𝕜 := ℂ) K := by
  intro hK
  letI := hK
  exact bonsall_dualWeakEssentialNorm_of_generic_factorization not_weaklyCompact_id_cZero
    dualWeakEssentialNorm_eq_cZero_factorization_complex

end PEMS
