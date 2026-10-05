import ThesisCommon.Analysis.ContinuousFunctionDiagonal
import ThesisCommon.Analysis.FreeNatUltrafilterVectorCompression
import ThesisCommon.Analysis.FreeNatUltrafilterSeparablePFP
import ThesisCommon.Analysis.ScalarPFP
import ThesisCommon.Analysis.SeparableTotalDual
import ThesisCommon.SetTheory.InfiniteNatSetSplit

/-! Diagonal evaluation gives an actual obstruction to extending Drewnowski's
local coefficient-compression theorem to nonseparable domain coefficients.
The codomain coefficient is the scalar field and has a countable total dual.
No claim here negates the unrestricted PFP transfer in manuscript Remark 5.2:
this obstructs one intermediate argument only. -/
noncomputable section
open Set TopologicalSpace
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The coefficient space used in the obstruction itself has the exact
2-primary-factorisation property, by the proved separable scalar transfer. -/
theorem freeNatUltrafilter_scalar_hasCPFP_two :
    HasCPFP 𝕜 C(FreeNatUltrafilter, 𝕜) 2 :=
  freeNatUltrafilter_hasCPFP_of_separable scalar_hasCPFP_two

theorem freeNatUltrafilter_diagonal_not_local_coefficient {A : Set ℕ}
    (hA : A.Infinite) :
    ¬ ∃ u : C(FreeNatUltrafilter, 𝕜) →L[𝕜] 𝕜,
      ∀ f : C(FreeNatUltrafilter, C(FreeNatUltrafilter, 𝕜)),
        (∀ U, U ∉ FreeNatUltrafilter.basic A → f U = 0) →
        ∀ U ∈ FreeNatUltrafilter.basic A,
          continuousFunctionDiagonal (𝕜 := 𝕜) f U = u (f U) := by
  obtain ⟨B, C, hB, hC, hBA, hCA, hBC⟩ :=
    infinite_nat_set_exists_disjoint_infinite_subsets hA
  obtain ⟨U, hU⟩ := FreeNatUltrafilter.exists_mem hB
  obtain ⟨V, hV⟩ := FreeNatUltrafilter.exists_mem hC
  have hBAm : FreeNatUltrafilter.basic B ⊆ FreeNatUltrafilter.basic A :=
    FreeNatUltrafilter.basic_mono_mod_finite (by
      rw [Set.diff_eq_empty.mpr hBA]
      exact Set.finite_empty)
  have hCAm : FreeNatUltrafilter.basic C ⊆ FreeNatUltrafilter.basic A :=
    FreeNatUltrafilter.basic_mono_mod_finite (by
      rw [Set.diff_eq_empty.mpr hCA]
      exact Set.finite_empty)
  have hBCm : Disjoint (FreeNatUltrafilter.basic B) (FreeNatUltrafilter.basic C) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← FreeNatUltrafilter.basic_inter,
      Set.disjoint_iff_inter_eq_empty.mp hBC, FreeNatUltrafilter.basic_empty]
  exact continuousFunctionDiagonal_not_local_coefficient
    (FreeNatUltrafilter.basic A) (FreeNatUltrafilter.basic B)
    (FreeNatUltrafilter.isClopen_basic A) (FreeNatUltrafilter.isClopen_basic B)
    (hBAm hU) (hCAm hV) hU (fun hVB => Set.disjoint_left.mp hBCm hVB hV)

/-- In particular the genuine scalar continuous-function space on ω* cannot
be separable: otherwise the already proved separable compression theorem would
give precisely the coefficient functional excluded above. -/
theorem freeNatUltrafilter_continuous_functions_not_separable :
    ¬ SeparableSpace C(FreeNatUltrafilter, 𝕜) := by
  intro hsep
  letI := hsep
  obtain ⟨B, hB, _, u, _, hu⟩ := exists_freeNatUltrafilter_vector_compression
    (hasCountableTotalDual_of_separable 𝕜 𝕜)
    (continuousFunctionDiagonal (𝕜 := 𝕜) (K := FreeNatUltrafilter))
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  exact freeNatUltrafilter_diagonal_not_local_coefficient hB ⟨u, hu⟩

end ThesisCommon
