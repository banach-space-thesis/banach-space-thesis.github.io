import ThesisCommon.Analysis.ALFragmentL1Isometry
import ThesisCommon.Analysis.ALPrincipalFragmentDensity
import ThesisCommon.Analysis.LpCodingOrder

/-! A principal band in a complete real AL-lattice is genuinely represented
by L1 of its finite fragment measure. The isometry and its order reflection
are proved from the constructed fragment map. -/
noncomputable section
open Set MeasureTheory
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [HasSolidNorm E] [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]

theorem alFragmentL1Map_nonneg_iff (f : Lp ℝ 1 (alFragmentMeasure hAL e)) :
    0 ≤ alFragmentL1Map hAL e f ↔ 0 ≤ f := by
  constructor
  · intro hf
    have hn := alFragmentL1Map_nonneg hAL e (negPart_nonneg f)
    have hadd : alFragmentL1Map hAL e f + alFragmentL1Map hAL e f⁻ =
        alFragmentL1Map hAL e f⁺ := by
      rw [← map_add]
      congr 1
      exact eq_sub_iff_add_eq.mp (posPart_sub_negPart f).symm
    have h := hAL _ _ hf hn
    rw [hadd, alFragmentL1Map_norm, alFragmentL1Map_norm, alFragmentL1Map_norm] at h
    have hnorm : ‖f‖ = ‖f⁺‖ + ‖f⁻‖ := by
      rw [← lOne_norm_add_of_nonneg _ _ _ (posPart_nonneg f) (negPart_nonneg f),
        posPart_add_negPart, norm_abs_eq_norm]
    have hz : f⁻ = 0 := norm_eq_zero.mp (by linarith [norm_nonneg f⁻])
    rw [← posPart_sub_negPart f, hz, sub_zero]
    exact posPart_nonneg f
  · exact alFragmentL1Map_nonneg hAL e

theorem alFragmentL1Map_mem_principalBand (f : Lp ℝ 1 (alFragmentMeasure hAL e)) :
    alFragmentL1Map hAL e f ∈ principalBand e := by
  have heq : (principalBandProjection e).comp (alFragmentL1Map hAL e) = alFragmentL1Map hAL e := by
    apply lOne_continuousLinearMap_ext_indicators
    intro s hs
    rw [ContinuousLinearMap.comp_apply, alFragmentL1Map_indicator]
    apply (principalBand_orderClosed e).bandProjection_eq_self
    exact positiveFragmentSpan_le_principalBand e
      (Submodule.subset_span (positiveFragmentValue_isFragment _))
  have h := DFunLike.congr_fun heq f
  rw [← h]
  exact (principalBand_orderClosed e).bandProjection_mem _

theorem range_alFragmentL1Map :
    LinearMap.range (alFragmentL1Map hAL e).toLinearMap = principalBand e := by
  apply le_antisymm
  · rintro x ⟨f, rfl⟩
    exact alFragmentL1Map_mem_principalBand hAL e f
  · rw [← positiveFragmentSpan_closure_eq_principalBand hAL (Fact.out : 0 ≤ e)]
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro a ha
      exact ⟨alFragmentIndicator hAL e (positiveFragmentOf ha),
        alFragmentL1Map_fragment hAL e (positiveFragmentOf ha)⟩
    · exact (alFragmentL1Isometry hAL e).isometry.isClosedEmbedding.isClosed_range

def alPrincipalL1Isometry : Lp ℝ 1 (alFragmentMeasure hAL e) →ₗᵢ[ℝ] principalBand e where
  toFun f := ⟨alFragmentL1Map hAL e f, alFragmentL1Map_mem_principalBand hAL e f⟩
  map_add' f g := Subtype.ext (map_add _ f g)
  map_smul' c f := Subtype.ext (map_smul _ c f)
  norm_map' := alFragmentL1Map_norm hAL e

theorem alPrincipalL1Isometry_surjective : Function.Surjective (alPrincipalL1Isometry hAL e) := by
  intro x
  have hx : (x : E) ∈ LinearMap.range (alFragmentL1Map hAL e).toLinearMap := by
    rw [range_alFragmentL1Map]
    exact x.property
  obtain ⟨f, hf⟩ := hx
  exact ⟨f, Subtype.ext hf⟩

def alPrincipalL1Equiv : Lp ℝ 1 (alFragmentMeasure hAL e) ≃ₗᵢ[ℝ] principalBand e :=
  LinearIsometryEquiv.ofSurjective (alPrincipalL1Isometry hAL e)
    (alPrincipalL1Isometry_surjective hAL e)

theorem alPrincipalL1Equiv_nonneg_iff (f : Lp ℝ 1 (alFragmentMeasure hAL e)) :
    0 ≤ alPrincipalL1Equiv hAL e f ↔ 0 ≤ f := alFragmentL1Map_nonneg_iff hAL e f

end ThesisCommon
