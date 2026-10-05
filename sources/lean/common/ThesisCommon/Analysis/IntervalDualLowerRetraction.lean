import ThesisCommon.Analysis.IntervalDisjointLebesgueBands
import ThesisCommon.Analysis.ContinuousMapComplexBandCoordinates
import ThesisCommon.Analysis.IntervalLpFunctionSelfSimilarity
import ThesisCommon.Analysis.ScalarIsometryTransport

/-! The continuum-indexed ell-one sum of actual Lebesgue L1 embeds
complementedly into the actual interval dual. Vertical-fibre measures provide
the real and complex bands; scalar transport covers every RCLike field. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open MeasureTheory
namespace ThesisCommon
open scoped PositiveOperatorOrder DualLattice
attribute [local instance] RingHomInvPair.of_ringEquiv

local instance (𝕜 : Type*) [RCLike 𝕜] :
    NormedAddCommGroup (IntervalContinuous 𝕜 →L[𝕜] 𝕜) := inferInstance
local instance (𝕜 : Type*) [RCLike 𝕜] :
    NormedSpace 𝕜 (IntervalContinuous 𝕜 →L[𝕜] 𝕜) := inferInstance
local instance (𝕜 : Type*) [RCLike 𝕜] :
    NormedAddCommGroup (EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩)) := inferInstance
local instance (𝕜 : Type*) [RCLike 𝕜] :
    NormedSpace 𝕜 (EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩)) := inferInstance

theorem exists_intervalContinuousRealDual_lower_retraction :
    ∃ (J : EllOneSum UnitInterval (IntervalLp ℝ ⟨1, le_rfl⟩) →L[ℝ]
          (IntervalContinuous ℝ →L[ℝ] ℝ))
      (R : (IntervalContinuous ℝ →L[ℝ] ℝ) →L[ℝ]
          EllOneSum UnitInterval (IntervalLp ℝ ⟨1, le_rfl⟩)),
      ‖J‖ ≤ 1 ∧ ‖R‖ ≤ 2 ∧ R.comp J = ContinuousLinearMap.id ℝ _ := by
  let a := IntervalDisjointLebesgue.generator
  let hd := IntervalDisjointLebesgue.generator_disjoint
  let d : EllOneSum UnitInterval (IntervalLp ℝ ⟨1, le_rfl⟩) ≃ₗᵢ[ℝ]
      lp (fun i => principalBand (a i)) 1 :=
    lebesgueLpCoordinateEquiv (by norm_num) IntervalDisjointLebesgue.realBandEquiv
  let S := alBandSynthesis a
  let Q := alBandCoordinates continuousMapDual_norm_add_of_nonneg a hd
  let J := S.comp d.toContinuousLinearEquiv.toContinuousLinearMap
  let R := d.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp Q
  refine ⟨J, R, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖S (d x)‖ ≤ 1 * ‖x‖
    simpa only [d.norm_map, one_mul] using alBandSynthesis_norm_le a (d x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro φ
    change ‖d.symm (Q φ)‖ ≤ 2 * ‖φ‖
    rw [d.symm.norm_map]
    exact (alBandCoefficients_norm_le continuousMapDual_norm_add_of_nonneg a hd φ).trans
      (by nlinarith [norm_nonneg φ])
  · apply ContinuousLinearMap.ext
    intro x
    change d.symm (Q (S (d x))) = x
    rw [alBandCoordinates_alBandSynthesis, d.symm_apply_apply]

theorem exists_intervalContinuousComplexDual_lower_retraction :
    ∃ (J : EllOneSum UnitInterval (IntervalLp ℂ ⟨1, le_rfl⟩) →L[ℂ]
          (IntervalContinuous ℂ →L[ℂ] ℂ))
      (R : (IntervalContinuous ℂ →L[ℂ] ℂ) →L[ℂ]
          EllOneSum UnitInterval (IntervalLp ℂ ⟨1, le_rfl⟩)),
      ‖J‖ ≤ 1 ∧ ‖R‖ ≤ 2 ∧ R.comp J = ContinuousLinearMap.id ℂ _ := by
  let a := IntervalDisjointLebesgue.generator
  let hd := IntervalDisjointLebesgue.generator_disjoint
  let d : EllOneSum UnitInterval (IntervalLp ℂ ⟨1, le_rfl⟩) ≃ₗᵢ[ℂ]
      lp (fun i => continuousMapComplexPrincipalBand (a i)) 1 :=
    lebesgueLpCoordinateEquiv (by norm_num) IntervalDisjointLebesgue.complexBandEquiv
  let S := continuousMapComplexBandSynthesis a
  let Q := continuousMapComplexBandCoordinates a hd
  let J := S.comp d.toContinuousLinearEquiv.toContinuousLinearMap
  let R := d.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp Q
  refine ⟨J, R, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖S (d x)‖ ≤ 1 * ‖x‖
    have hh := S.le_of_opNorm_le (norm_continuousMapComplexBandSynthesis_le a) (d x)
    simpa only [d.norm_map, one_mul] using hh
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro φ
    change ‖d.symm (Q φ)‖ ≤ 2 * ‖φ‖
    rw [d.symm.norm_map]
    exact continuousMapComplexBandCoefficients_norm_le a hd φ
  · apply ContinuousLinearMap.ext
    intro x
    change d.symm (Q (S (d x))) = x
    have hh := DFunLike.congr_fun (continuousMapComplexBandCoordinates_comp_synthesis a hd) (d x)
    change Q (S (d x)) = d x at hh
    rw [hh, d.symm_apply_apply]

theorem intervalContinuousDual_lower_retraction_scalarTransport
    {𝕜 𝕜' : Type*} [RCLike 𝕜] [RCLike 𝕜']
    (e : 𝕜 ≃+* 𝕜') [RingHomIsometric (RingHomClass.toRingHom e)]
    [RingHomIsometric (RingHomClass.toRingHom e.symm)]
    (J' : EllOneSum UnitInterval (IntervalLp 𝕜' ⟨1, le_rfl⟩) →L[𝕜']
      (IntervalContinuous 𝕜' →L[𝕜'] 𝕜'))
    (R' : (IntervalContinuous 𝕜' →L[𝕜'] 𝕜') →L[𝕜']
      EllOneSum UnitInterval (IntervalLp 𝕜' ⟨1, le_rfl⟩))
    (hJ : ‖J'‖ ≤ 1) (hR : ‖R'‖ ≤ 2) (hRJ : R'.comp J' = ContinuousLinearMap.id 𝕜' _) :
    ∃ (J : EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩) →L[𝕜]
          (IntervalContinuous 𝕜 →L[𝕜] 𝕜))
      (R : (IntervalContinuous 𝕜 →L[𝕜] 𝕜) →L[𝕜]
          EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩)),
      ‖J‖ ≤ 1 ∧ ‖R‖ ≤ 2 ∧ R.comp J = ContinuousLinearMap.id 𝕜 _ := by
  let d := continuousMapDualScalarIsometryEquiv e UnitInterval
  let b : EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩) ≃ₛₗᵢ[RingHomClass.toRingHom e]
      EllOneSum UnitInterval (IntervalLp 𝕜' ⟨1, le_rfl⟩) :=
    lpFamilySemilinearIsometryEquiv e 1 (by norm_num)
      (fun _ => measureLpScalarIsometryEquiv e (volume.restrict (Set.Icc (0 : ℝ) 1)) 1)
  let J := d.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (J'.comp b.toContinuousLinearEquiv.toContinuousLinearMap)
  let R := b.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (R'.comp d.toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨J, R, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖d.symm (J' (b x))‖ ≤ 1 * ‖x‖
    rw [d.symm.norm_map]
    simpa only [b.norm_map] using J'.le_of_opNorm_le hJ (b x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro φ
    change ‖b.symm (R' (d φ))‖ ≤ 2 * ‖φ‖
    rw [b.symm.norm_map]
    simpa only [d.norm_map] using R'.le_of_opNorm_le hR (d φ)
  · apply ContinuousLinearMap.ext
    intro x
    change b.symm (R' (d (d.symm (J' (b x))))) = x
    rw [d.apply_symm_apply]
    have hh := DFunLike.congr_fun hRJ (b x)
    change R' (J' (b x)) = b x at hh
    rw [hh, b.symm_apply_apply]

theorem exists_intervalContinuousDual_lower_retraction (𝕜 : Type*) [RCLike 𝕜] :
    ∃ (J : EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩) →L[𝕜]
          (IntervalContinuous 𝕜 →L[𝕜] 𝕜))
      (R : (IntervalContinuous 𝕜 →L[𝕜] 𝕜) →L[𝕜]
          EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩)),
      ‖J‖ ≤ 1 ∧ ‖R‖ ≤ 2 ∧ R.comp J = ContinuousLinearMap.id 𝕜 _ := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hr | hc
  · let e := RCLike.realRingEquiv hr
    letI : RingHomIsometric (RingHomClass.toRingHom e) :=
      ⟨fun {x} => (RCLike.realLinearIsometryEquiv hr).norm_map x⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
      intro x
      have h := scalarRingEquiv_norm e (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm⟩
    obtain ⟨J, R, hJ, hR, hRJ⟩ := exists_intervalContinuousRealDual_lower_retraction
    exact intervalContinuousDual_lower_retraction_scalarTransport e J R hJ hR hRJ
  · let e := RCLike.complexRingEquiv hc
    letI : RingHomIsometric (RingHomClass.toRingHom e) :=
      ⟨fun {x} => (RCLike.complexLinearIsometryEquiv hc).norm_map x⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
      intro x
      have h := scalarRingEquiv_norm e (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm⟩
    obtain ⟨J, R, hJ, hR, hRJ⟩ := exists_intervalContinuousComplexDual_lower_retraction
    exact intervalContinuousDual_lower_retraction_scalarTransport e J R hJ hR hRJ

end ThesisCommon
