import PEMS.ContinuousMapAdjointOpenWitness
import PEMS.DisjointContinuousCZeroFixing

/-! Proposition 6.3 and the first clause of Theorem 1.5, for arbitrary
compact Hausdorff spaces over the real or complex field. The sharp lower
bound uses constructed regular-measure witnesses and a constructed c0
subcopy; it assumes no quantitative Grothendieck criterion. -/
noncomputable section
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000
open Set ThesisCommon
namespace PEMS

theorem fixesCZeroSup_nonneg {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →L[𝕜] F) :
    0 ≤ fixesCZeroSup T := by
  apply (minimumModulus_cZero_nonneg (T.comp (0 : CZero 𝕜 →L[𝕜] E))).trans
  apply le_csSup
  · refine ⟨dualWeakEssentialNorm T, ?_⟩
    rintro _ ⟨V, hV, rfl⟩
    exact minimumModulus_comp_le_dualWeakEssentialNorm T V hV
  · refine ⟨(0 : CZero 𝕜 →L[𝕜] E), ?_, rfl⟩
    rw [norm_zero]
    exact zero_le_one

variable {K L : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TopologicalSpace L] [CompactSpace L] [T2Space L]

theorem dualWeakEssentialNorm_le_fixesCZeroSup_real
    (T : C(L, ℝ) →L[ℝ] C(K, ℝ)) : dualWeakEssentialNorm T ≤ fixesCZeroSup T := by
  letI : MeasurableSpace L := borel L
  letI : BorelSpace L := ⟨rfl⟩
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  by_cases hc0 : 0 < c
  · obtain ⟨ν, U, hν, hU, hUd, hm⟩ := exists_real_adjoint_disjoint_open_witness T hc0 hc
    choose f hf hs he using fun n =>
      exists_continuousMap_real_open_modulus_test (banachAdjoint T (ν n)) (hU n) (hm n)
    apply le_fixesCZeroSup_of_disjoint_continuous_columns T f hf ?_ hc0 ?_
    · intro i j hij t
      by_cases ht : t ∈ U i
      · exact Or.inr (hs j t (fun hj => Set.disjoint_left.mp (hUd hij) ht hj))
      · exact Or.inl (hs i t ht)
    · intro n
      have h := (ν n).le_opNorm (T (f n))
      rw [hν n, one_mul] at h
      exact (he n).le.trans h
  · exact (le_of_not_gt hc0).trans (fixesCZeroSup_nonneg T)

theorem dualWeakEssentialNorm_le_fixesCZeroSup_complex
    (T : C(L, ℂ) →L[ℂ] C(K, ℂ)) : dualWeakEssentialNorm T ≤ fixesCZeroSup T := by
  letI : MeasurableSpace L := borel L
  letI : BorelSpace L := ⟨rfl⟩
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  by_cases hc0 : 0 < c
  · obtain ⟨ν, U, hν, hU, hUd, hm⟩ := exists_complex_adjoint_disjoint_open_witness T hc0 hc
    choose f hf hs he using fun n =>
      exists_continuousMap_complex_open_modulus_test (banachAdjoint T (ν n)) (hU n) (hm n)
    apply le_fixesCZeroSup_of_disjoint_continuous_columns T f hf ?_ hc0 ?_
    · intro i j hij t
      by_cases ht : t ∈ U i
      · exact Or.inr (hs j t (fun hj => Set.disjoint_left.mp (hUd hij) ht hj))
      · exact Or.inl (hs i t ht)
    · intro n
      have h := (ν n).le_opNorm (T (f n))
      rw [hν n, one_mul] at h
      exact (he n).le.trans h
  · exact (le_of_not_gt hc0).trans (fixesCZeroSup_nonneg T)

theorem dualWeakEssentialNorm_eq_fixesCZeroSup_real
    (T : C(L, ℝ) →L[ℝ] C(K, ℝ)) : dualWeakEssentialNorm T = fixesCZeroSup T :=
  le_antisymm (dualWeakEssentialNorm_le_fixesCZeroSup_real T)
    (fixesCZeroSup_le_dualWeakEssentialNorm T)

theorem dualWeakEssentialNorm_eq_fixesCZeroSup_complex
    (T : C(L, ℂ) →L[ℂ] C(K, ℂ)) : dualWeakEssentialNorm T = fixesCZeroSup T :=
  le_antisymm (dualWeakEssentialNorm_le_fixesCZeroSup_complex T)
    (fixesCZeroSup_le_dualWeakEssentialNorm T)

end PEMS
