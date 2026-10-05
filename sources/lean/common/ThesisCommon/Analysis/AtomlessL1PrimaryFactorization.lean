import ThesisCommon.Analysis.RealL1LocalizedFactorization
import ThesisCommon.Analysis.ComplexL1DiagonalCompression
import ThesisCommon.Analysis.IntervalCantorL1Model
import ThesisCommon.Analysis.ScalarFactorizationTransport
import ThesisCommon.Analysis.IntervalLpFunctionSelfSimilarity
import ThesisCommon.Analysis.PelczynskiDecomposition

/-! The actual Lebesgue L1 space has the 4-primary factorisation property
over every RCLike scalar field. The proof constructs a positive-measure
diagonal compression for an arbitrary operator and transports its genuine
restricted L1 factors through atomless measure-space isometries. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] RingHomInvPair.of_ringEquiv

private theorem factorsIdentityWith_isometric_target
    {𝕜 E F Z W : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {T : E →L[𝕜] F} {C : ℝ} (h : FactorsIdentityWith T Z C)
    (e : Z ≃ₗᵢ[𝕜] W) : FactorsIdentityWith T W C := by
  have hC : 0 ≤ C := by
    obtain ⟨U, V, _, hn⟩ := h
    exact (mul_nonneg (norm_nonneg U) (norm_nonneg V)).trans hn
  apply (h.target_equiv e.toContinuousLinearEquiv).mono
  have hn : ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ *
      ‖e.toContinuousLinearEquiv.symm.toContinuousLinearMap‖ ≤ 1 := by
    simpa using mul_le_mul e.toLinearIsometry.norm_toContinuousLinearMap_le
      e.symm.toLinearIsometry.norm_toContinuousLinearMap_le (norm_nonneg _) zero_le_one
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hC

section Compact
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [StandardBorelSpace X] {μ : Measure X} [IsFiniteMeasure μ] [NoAtoms μ]

theorem real_compactAtomlessL1_hasCPFP_four (hμ : μ ≠ 0) : HasCPFP ℝ (Lp ℝ 1 μ) 4 := by
  intro T
  obtain ⟨D, _, hd, h⟩ := exists_realL1_part_factorization T hμ
  let e := (atomlessRestrictedL1Equiv ℝ μ D hd).trans
    (atomlessStandardBorelL1Equiv ℝ μ hμ).symm
  exact h.imp (fun hf => factorsIdentityWith_isometric_target hf e)
    (fun hf => factorsIdentityWith_isometric_target hf e)

theorem complex_compactAtomlessL1_hasCPFP_four (hμ : μ ≠ 0) : HasCPFP ℂ (Lp ℂ 1 μ) 4 := by
  intro T
  obtain ⟨S, hS, D, hD, hd, hlower, hsmall⟩ :=
    exists_complexL1_small_diagonal_compression T hμ (show (0 : ℝ) < 1 / 4 by norm_num)
  have hf := factorsIdentityWith_of_lp_diagonal_compression S (complexL1DiagonalMultiplier S)
    (complexL1Diagonal S) (complexL1Diagonal_measurable S) (complexL1DiagonalMultiplier_coe S)
    D hD hlower hsmall
  let e := (atomlessRestrictedL1Equiv ℂ μ D hd).trans
    (atomlessStandardBorelL1Equiv ℂ μ hμ).symm
  have h := factorsIdentityWith_isometric_target hf e
  rcases hS with rfl | rfl
  · exact Or.inl h
  · exact Or.inr h

end Compact

theorem intervalCantorL1_hasCPFP_four (𝕜 : Type*) [RCLike 𝕜] :
    HasCPFP 𝕜 (Lp 𝕜 1 intervalCantorMeasure) 4 := by
  letI : MetricSpace (ℕ → Bool) := PiNat.metricSpace
  have hμ : intervalCantorMeasure ≠ 0 := MeasureTheory.IsProbabilityMeasure.ne_zero _
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hr | hc
  · let e := RCLike.realRingEquiv hr
    letI : RingHomIsometric (RingHomClass.toRingHom e) :=
      ⟨fun {x} => (RCLike.realLinearIsometryEquiv hr).norm_map x⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
      intro x
      have h := scalarRingEquiv_norm e (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm.symm) := by
      simpa only [RingEquiv.symm_symm] using (inferInstance : RingHomIsometric (RingHomClass.toRingHom e))
    exact (real_compactAtomlessL1_hasCPFP_four hμ).of_semilinearIsometry e.symm
      (measureLpScalarIsometryEquiv e intervalCantorMeasure 1).symm
  · let e := RCLike.complexRingEquiv hc
    letI : RingHomIsometric (RingHomClass.toRingHom e) :=
      ⟨fun {x} => (RCLike.complexLinearIsometryEquiv hc).norm_map x⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
      intro x
      have h := scalarRingEquiv_norm e (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm.symm) := by
      simpa only [RingEquiv.symm_symm] using (inferInstance : RingHomIsometric (RingHomClass.toRingHom e))
    exact (complex_compactAtomlessL1_hasCPFP_four hμ).of_semilinearIsometry e.symm
      (measureLpScalarIsometryEquiv e intervalCantorMeasure 1).symm

theorem intervalL1_hasCPFP_four (𝕜 : Type*) [RCLike 𝕜] :
    HasCPFP 𝕜 (IntervalLp 𝕜 ⟨1, le_rfl⟩) 4 := by
  letI : RingHomIsometric (RingHomClass.toRingHom (RingEquiv.refl 𝕜)) := ⟨fun {_} => rfl⟩
  letI : RingHomIsometric (RingHomClass.toRingHom (RingEquiv.refl 𝕜).symm) := ⟨fun {_} => rfl⟩
  exact (intervalCantorL1_hasCPFP_four 𝕜).of_semilinearIsometry (RingEquiv.refl 𝕜)
    (intervalCantorL1Equiv 𝕜)

theorem intervalL1_hasUPFP (𝕜 : Type*) [RCLike 𝕜] :
    HasUPFP 𝕜 (IntervalLp 𝕜 ⟨1, le_rfl⟩) :=
  ⟨4, by norm_num, intervalL1_hasCPFP_four 𝕜⟩

theorem intervalL1_isPrimary (𝕜 : Type*) [RCLike 𝕜] :
    IsPrimary 𝕜 (IntervalLp 𝕜 ⟨1, le_rfl⟩) :=
  (intervalL1_hasUPFP 𝕜).isPrimary_of_sequenceSelfSimilar
    (intervalLpFunction_isSequenceSelfSimilar 𝕜 ⟨1, le_rfl⟩ (by simp))

end ThesisCommon
