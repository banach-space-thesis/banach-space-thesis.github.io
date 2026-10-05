import PEMS.SequentialCZeroFactorization
import PEMS.ExtremallyDisconnectedInfinityFactorization
import PEMS.CZeroFactorizationFixingComparison
import PEMS.MainStatements

/-! The two factorization clauses of Theorem 1.5 follow from the actual
c₀-fixing supremum. The first equality is isolated as a premise only in
the final assembly theorem; neither complementation result is assumed. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 3
open Set ThesisCommon
open scoped ENNReal
namespace PEMS
variable {𝕜 : Type} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K L : Type*} [TopologicalSpace K] [CompactSpace K]
variable [TopologicalSpace L] [CompactSpace L] [T2Space L]

theorem fixesCZeroSup_eq_factorizationSup_cZero_sequentiallyCompact
    [SeqCompactSpace K] (T : E →L[𝕜] C(K, 𝕜)) :
    fixesCZeroSup T = factorizationSup (CZero 𝕜) T := by
  letI : Nontrivial (CZero 𝕜) := ⟨⟨cZeroSingle 0 1, 0, by
    intro h
    have hh := congrArg (fun x : CZero 𝕜 => x 0) h
    simp at hh⟩⟩
  apply le_antisymm ?_ (factorizationSup_cZero_le_fixesCZeroSup T)
  apply csSup_le
  · refine ⟨minimumModulus (T.comp (0 : CZero 𝕜 →L[𝕜] E)), ⟨0, ?_, rfl⟩⟩
    simp
  · rintro _ ⟨V, hV, rfl⟩
    rcases (minimumModulus_cZero_nonneg (T.comp V)).eq_or_lt with hzero | hpos
    · rw [← hzero]
      exact factorizationSup_nonneg T
    · exact le_factorizationSup_of_fixed_copy_sequentiallyCompact T V hV hpos
        (minimumModulus_cZero_mul_norm_le (T.comp V))

theorem fixesCZeroSup_eq_factorizationSup_infinity_extremallyDisconnected
    [ExtremallyDisconnected L] (T : C(L, 𝕜) →L[𝕜] F) :
    fixesCZeroSup T = factorizationSup (EllInfinity 𝕜) T := by
  letI : Nontrivial (EllInfinity 𝕜) := ⟨⟨lp.single ∞ 0 (1 : 𝕜), 0, by
    intro h
    have hh := congrArg (fun x : EllInfinity 𝕜 => x 0) h
    simp at hh⟩⟩
  apply le_antisymm ?_ (factorizationSup_infinity_le_fixesCZeroSup T)
  apply csSup_le
  · refine ⟨minimumModulus (T.comp (0 : CZero 𝕜 →L[𝕜] C(L, 𝕜))), ⟨0, ?_, rfl⟩⟩
    simp
  · rintro _ ⟨V, hV, rfl⟩
    rcases (minimumModulus_cZero_nonneg (T.comp V)).eq_or_lt with hzero | hpos
    · rw [← hzero]
      exact factorizationSup_nonneg T
    · exact le_factorizationSup_infinity_of_fixed_copy_extremallyDisconnected T V hV hpos
        (minimumModulus_cZero_mul_norm_le (T.comp V))

theorem theorem_1_5_of_fixing_formula [T2Space K]
    (T : C(L, 𝕜) →L[𝕜] C(K, 𝕜))
    (hfirst : dualWeakEssentialNorm T = fixesCZeroSup T) : Theorem_1_5 K L T := by
  refine ⟨hfirst, ?_, ?_⟩
  · intro hK
    letI := hK
    exact hfirst.trans (fixesCZeroSup_eq_factorizationSup_cZero_sequentiallyCompact T)
  · intro hL
    letI := hL
    exact hfirst.trans (fixesCZeroSup_eq_factorizationSup_infinity_extremallyDisconnected T)

end PEMS
