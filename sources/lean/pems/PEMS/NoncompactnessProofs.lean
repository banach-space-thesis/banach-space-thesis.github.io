import PEMS.NoncompactnessDefinitions
import ThesisCommon.WeakNoncompactnessBound

noncomputable section
namespace PEMS
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Lemma 5.10, following the paper: subtract an arbitrary weakly compact W,
apply normalization and the ideal estimate, and take the infimum over W.
The shared perturbation lemma supplies the equality implicit in the paper. -/
theorem lemma_5_10_proof (α : (E →L[𝕜] E) → ℝ) (T : E →L[𝕜] E) :
    Lemma_5_10 α T := by
  intro hα
  exact weakNoncompactness_le_weakEssentialNorm α hα.add_le hα.comp_le_left
    (fun W hW => (hα.zero_iff W).mpr hW) hα.normalized T

/-- The factorization estimate inside Proposition 5.11. The witnesses J,P come
from Definition 5.8(d); U,V factor the identity on the actual ℓ¹ space.
The proof makes the paper's insertion of J and P explicit. -/
theorem factorization_value_le_measure (α : (E →L[𝕜] E) → ℝ)
    (hα : NormalizedWeakNoncompactnessMeasure α) (T : E →L[𝕜] E)
    (U : E →L[𝕜] EllOne 𝕜) (V : EllOne 𝕜 →L[𝕜] E)
    (hfac : U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 (EllOne 𝕜)) :
    ‖U‖⁻¹ * ‖V‖⁻¹ ≤ α T := by
  obtain ⟨J, P, hJ, hP, hPJ, hJP⟩ := hα.normalized_copy
  have hJn : ‖J‖ ≤ 1 := by
    apply J.opNorm_le_bound (by norm_num)
    intro x
    simp [hJ x]
  have hcomp : (J.comp U).comp (T.comp (V.comp P)) = J.comp P := by
    ext x
    have h := congrArg (fun R : EllOne 𝕜 →L[𝕜] EllOne 𝕜 => R (P x)) hfac
    exact congrArg J h
  have hJU : ‖J.comp U‖ ≤ ‖U‖ :=
    (J.opNorm_comp_le U).trans (mul_le_of_le_one_left (norm_nonneg U) hJn)
  have hVP : ‖V.comp P‖ ≤ ‖V‖ := by
    simpa [hP] using V.opNorm_comp_le P
  have hone : 1 ≤ (‖U‖ * ‖V‖) * α T := by
    calc
      1 ≤ α (J.comp P) := hJP
      _ = α ((J.comp U).comp (T.comp (V.comp P))) := congrArg α hcomp.symm
      _ ≤ ‖J.comp U‖ * α (T.comp (V.comp P)) := hα.comp_le_left _ _
      _ ≤ ‖J.comp U‖ * (α T * ‖V.comp P‖) :=
        mul_le_mul_of_nonneg_left (hα.comp_le_right _ _) (norm_nonneg _)
      _ ≤ ‖U‖ * (α T * ‖V‖) :=
        mul_le_mul hJU (mul_le_mul_of_nonneg_left hVP (hα.nonneg T))
          (mul_nonneg (hα.nonneg T) (norm_nonneg _)) (norm_nonneg _)
      _ = (‖U‖ * ‖V‖) * α T := by ring
  have hprod : 0 < ‖U‖ * ‖V‖ := by
    have hnonneg := mul_nonneg (norm_nonneg U) (norm_nonneg V)
    by_contra h
    have hz : ‖U‖ * ‖V‖ = 0 := le_antisymm (le_of_not_gt h) hnonneg
    rw [hz, zero_mul] at hone
    norm_num at hone
  rw [← mul_inv]
  exact (inv_le_iff_one_le_mul₀' hprod).mpr hone

/-- CONDITIONAL assembly of Proposition 5.11. The exact outstanding input is
the factorization equality from Theorem 1.4 for this T. This is NOT a proof
of Proposition_5_11 until that input is constructed under its AL hypotheses.
Taking the supremum instead of normalizing and passing epsilon to zero is the
order-theoretic form of the same quantitative estimate in the paper. -/
theorem proposition_5_11_of_factorization (α : (E →L[𝕜] E) → ℝ)
    (hα : NormalizedWeakNoncompactnessMeasure α) (T : E →L[𝕜] E)
    (hfactor : weakEssentialNorm T = factorizationSup (EllOne 𝕜) T) :
    α T = weakEssentialNorm T := by
  apply le_antisymm (lemma_5_10_proof α T hα)
  rw [hfactor]
  apply csSup_le (Set.insert_nonempty _ _)
  intro r hr
  rcases hr with rfl | ⟨U, V, hfac, rfl⟩
  · exact hα.nonneg T
  · exact factorization_value_le_measure α hα T U V hfac

end PEMS
