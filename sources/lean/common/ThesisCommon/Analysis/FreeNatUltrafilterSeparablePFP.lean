import ThesisCommon.Analysis.FreeNatUltrafilterVectorCompression
import ThesisCommon.Analysis.ContinuousFunctionFactorization
import ThesisCommon.Analysis.SeparableTotalDual

/-! The separable-coefficient correction of the manuscript's Remark 5.2.
The countable hypotheses of Drewnowski's theorem are discharged by actual
separability. The unrestricted remark is not asserted here. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [TopologicalSpace.SeparableSpace X]

theorem freeNatUltrafilter_hasCPFP_of_separable {C : ℝ} (hX : HasCPFP 𝕜 X C) :
    HasCPFP 𝕜 C(FreeNatUltrafilter, X) C := by
  intro T
  obtain ⟨B, hB, _, u, _, hu⟩ := exists_freeNatUltrafilter_vector_compression
    (hasCountableTotalDual_of_separable 𝕜 X) T Set.infinite_univ
  obtain ⟨e⟩ := FreeNatUltrafilter.exists_basic_homeomorph hB
  rcases hX u with h | h
  · exact Or.inl (h.of_clopen_coefficient T (FreeNatUltrafilter.basic B)
      (FreeNatUltrafilter.isClopen_basic B) e u hu)
  · apply Or.inr
    apply h.of_clopen_coefficient (ContinuousLinearMap.id 𝕜 C(FreeNatUltrafilter, X) - T)
      (FreeNatUltrafilter.basic B) (FreeNatUltrafilter.isClopen_basic B) e
      (ContinuousLinearMap.id 𝕜 X - u)
    intro f hf U hU
    change f U - T f U = f U - u (f U)
    rw [hu f hf U hU]

theorem freeNatUltrafilter_hasUPFP_of_separable (hX : HasUPFP 𝕜 X) :
    HasUPFP 𝕜 C(FreeNatUltrafilter, X) := by
  obtain ⟨C, hC, hX⟩ := hX
  exact ⟨C, hC, freeNatUltrafilter_hasCPFP_of_separable hX⟩

theorem freeNatUltrafilter_hasPFP_of_separable (hX : HasPFP 𝕜 X) :
    HasPFP 𝕜 C(FreeNatUltrafilter, X) := by
  intro T
  obtain ⟨B, hB, _, u, _, hu⟩ := exists_freeNatUltrafilter_vector_compression
    (hasCountableTotalDual_of_separable 𝕜 X) T Set.infinite_univ
  obtain ⟨e⟩ := FreeNatUltrafilter.exists_basic_homeomorph hB
  rcases hX u with h | h
  · exact Or.inl (h.of_clopen_coefficient T (FreeNatUltrafilter.basic B)
      (FreeNatUltrafilter.isClopen_basic B) e u hu)
  · apply Or.inr
    apply h.of_clopen_coefficient (ContinuousLinearMap.id 𝕜 C(FreeNatUltrafilter, X) - T)
      (FreeNatUltrafilter.basic B) (FreeNatUltrafilter.isClopen_basic B) e
      (ContinuousLinearMap.id 𝕜 X - u)
    intro f hf U hU
    change f U - T f U = f U - u (f U)
    rw [hu f hf U hU]

end ThesisCommon
