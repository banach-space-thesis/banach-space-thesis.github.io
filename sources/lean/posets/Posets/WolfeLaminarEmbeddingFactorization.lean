import Posets.WolfeLaminarEmbeddingOrdinal

/-! Finite-span norming and quotient rank produce actual ordinal identity
factors. The complemented-subcopy result discharges the projection step. -/
noncomputable section
open Set Topology TopologicalSpace ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
variable {K ι X : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [Countable K]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [SeparableSpace X]

theorem wolfeLaminarEmbedding_factorization
    (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) (hcA : ∀ i, IsCompact (A i))
    (hunit : ∃ i, A i = univ)
    (hlam : ∀ i j, A i ⊆ A j ∨ A j ⊆ A i ∨ Disjoint (A i) (A j))
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ (s : Finset ι) (a : ι → 𝕜),
      c * ‖∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i)‖ ≤
        ‖T (∑ i ∈ s, a i • JLMS.clopenIndicator (𝕜 := 𝕜) (A i) (hA i) (hcA i))‖)
    {α : Ordinal.{0}} (hα : α ≠ 0) (hcα : α.card ≤ Cardinal.aleph0)
    (hD : (ordinalDerived (univ : Set (WolfeClopenQuotient A hA)) α).Nonempty) :
    ∃ I : OrdinalContinuous 𝕜 (ω ^ α) →L[𝕜] JLMS.CZero 𝕜 K,
    ∃ R : X →L[𝕜] OrdinalContinuous 𝕜 (ω ^ α),
      R.comp (T.comp I) = ContinuousLinearMap.id 𝕜 _ ∧ ‖I‖ ≤ 1 ∧ ‖R‖ ≤ 1 / c := by
  obtain ⟨V⟩ := exists_ordinal_isometry_of_derivative_nonempty (𝕜 := 𝕜)
    (WolfeClopenQuotient A hA) hα hD
  let J := (wolfeClopenCZeroIsometry (𝕜 := 𝕜) A hA).comp V
  have hJ : ∀ f, c * ‖f‖ ≤ ‖(T.comp J.toContinuousLinearMap) f‖ := by
    intro f
    have h := wolfeLaminarEmbedding_lower_bound A hA hcA hunit hlam T c hbound (V f)
    simpa only [LinearIsometry.norm_map] using h
  obtain ⟨S, R, hR, hS, hnR⟩ := exists_countable_ordinal_embedding_identity_factors hcα
    (T.comp J.toContinuousLinearMap) hc hJ
  refine ⟨J.toContinuousLinearMap.comp S, R, ?_, ?_, hnR⟩
  · simpa only [ContinuousLinearMap.comp_assoc] using hR
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖J (S f)‖ ≤ 1 * ‖f‖
    rw [J.norm_map, one_mul]
    exact (S.le_opNorm f).trans (by simpa using mul_le_mul_of_nonneg_right hS (norm_nonneg f))

end Posets
