import PL1.HilbertDyadicTrace
import PL1.DyadicCellMeasure
import PL1.LpOperatorLift

/-! # Trace vanishing for operators with an Lp-to-Hilbert smoothing extension -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace PL1.SmoothingTrace

attribute [local instance] DyadicTrace.intervalMeasure_probability

variable {𝕜 Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω] (μ : Measure Ω)

theorem norm_cellVector_le_one (n i : ℕ) :
    ‖HilbertDyadicTrace.cellVector (𝕜 := 𝕜) n i‖ ≤ 1 := by
  have h := norm_indicatorConstLp_le (p := ∞) (hs := DyadicTrace.measurableSet_cell n i)
    (hμs := measure_ne_top intervalMeasure (DyadicTrace.cell n i)) (c := (1 : 𝕜))
  simpa only [HilbertDyadicTrace.cellVector, TraceBounds.cellVector,
    ENNReal.toReal_top, div_zero, Real.rpow_zero, norm_one, mul_one] using h

theorem norm_inclusion_cellVector (n i : ℕ) (hi : i < 2 ^ n) :
    ‖ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top
      (HilbertDyadicTrace.cellVector (𝕜 := 𝕜) n i)‖ = ((2 : ℝ) ^ n)⁻¹ := by
  rw [TraceBounds.inclusion_cellVector, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one, ENNReal.toReal_one, div_one, Real.rpow_one, one_mul,
    measureReal_def, DyadicTrace.intervalMeasure_cell_toReal n i hi]

variable (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ) (G : Ω → ℝ) (hG : Measurable G)
  (hdom : ∀ f : Lp 𝕜 ∞ intervalMeasure, ‖f‖ ≤ 1 →
    ∀ᵐ x ∂μ, ‖OperatorDomination.restriction μ B f x‖ ≤ G x)

theorem norm_maskedRestriction_cell_le (M : ℝ) (n i : ℕ) (hi : i < 2 ^ n) :
    ‖OperatorDomination.maskedRestriction μ B G hG M
      (HilbertDyadicTrace.cellVector (𝕜 := 𝕜) n i)‖ ≤ ‖B‖ * ((2 : ℝ) ^ n)⁻¹ := by
  have hmask := L1Masks.norm_maskFun_le μ {x | G x ≤ M}
    (measurableSet_le hG measurable_const)
    (OperatorDomination.restriction μ B (HilbertDyadicTrace.cellVector (𝕜 := 𝕜) n i))
  change ‖OperatorDomination.maskedRestriction μ B G hG M
    (HilbertDyadicTrace.cellVector (𝕜 := 𝕜) n i)‖ ≤ _ at hmask
  exact hmask.trans ((B.le_opNorm _).trans_eq
    (congrArg (fun z : ℝ => ‖B‖ * z) (norm_inclusion_cellVector (𝕜 := 𝕜) n i hi)))

theorem norm_maskedRestrictionLp_cell_le (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ∞)
    [Fact (1 ≤ p)] (M : ℝ) (hM : 0 ≤ M) (n i : ℕ) (hi : i < 2 ^ n) :
    ‖OperatorDomination.maskedRestrictionLp μ B G hG hdom p hp hptop M hM
      (HilbertDyadicTrace.cellVector (𝕜 := 𝕜) n i)‖ ≤
      (M ^ (1 - 1 / p.toReal) * ‖B‖ ^ (1 / p.toReal)) *
        (((2 : ℝ) ^ n)⁻¹) ^ (1 / p.toReal) := by
  have h := OperatorDomination.norm_maskedRestrictionLp_apply_le μ B G hG hdom
    p hp hptop M hM (HilbertDyadicTrace.cellVector (𝕜 := 𝕜) n i)
    (norm_cellVector_le_one n i)
  apply h.trans
  calc
    _ ≤ M ^ (1 - 1 / p.toReal) * (‖B‖ * ((2 : ℝ) ^ n)⁻¹) ^ (1 / p.toReal) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hM _)
      exact Real.rpow_le_rpow (norm_nonneg _)
        (norm_maskedRestriction_cell_le μ B G hG M n i hi) (by positivity)
    _ = _ := by rw [Real.mul_rpow (norm_nonneg B) (by positivity), mul_assoc]

section Smoothing

variable {Ω₂ H : Type*} [MeasurableSpace Ω₂] (ν : Measure Ω₂)
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Arbitrary operators before and after an Lp-to-Hilbert smoothing operator
have vanishing concrete interval dyadic traces. The extension identity is
required on the actual L1/Lp overlap; neither measure needs to be finite. -/
theorem trace_tendsto_zero_of_smoothing
    (A : Lp 𝕜 1 ν →L[𝕜] IntervalL1 𝕜) (S : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν)
    (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp2 : p < 2) [Fact (1 ≤ p)]
    (Q : Lp 𝕜 p μ →L[𝕜] H) (j : H →L[𝕜] Lp 𝕜 1 ν)
    (hS : ∀ (g : Lp 𝕜 1 μ) (f : Lp 𝕜 p μ), g =ᵐ[μ] f → S g = j (Q f)) :
    Tendsto (fun n => DyadicTrace.trace n (A.comp (S.comp B))) atTop (𝓝 0) := by
  have hptop : p ≠ ∞ := ne_top_of_lt hp2
  have hpR : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hptop hp
  have hp0 : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hpR
  have hpR2 : p.toReal < 2 := by
    have h := (ENNReal.toReal_lt_toReal hptop (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mpr hp2
    simpa using h
  have hr : (1 : ℝ) / 2 < 1 / p.toReal := (lt_div_iff₀ hp0).mpr (by linarith)
  obtain ⟨G, hG, hGint, hGpos, _, hdom⟩ := OperatorDomination.exists_measurable_dominator μ B
  let Bm (m : ℕ) : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ :=
    (L1Masks.mask μ {x | G x ≤ (m : ℝ)} (measurableSet_le hG measurable_const)).comp B
  let Rm (m : ℕ) : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜 := A.comp (S.comp (Bm m))
  have htrace (m : ℕ) : Tendsto (fun n => DyadicTrace.trace n (Rm m)) atTop (𝓝 0) := by
    let L := OperatorDomination.maskedRestrictionLp μ B G hG hdom p hp hptop
      (m : ℝ) (Nat.cast_nonneg m)
    have hfactor : DyadicTrace.restrictLinfty (Rm m) = (A.comp j).comp (Q.comp L) := by
      apply ContinuousLinearMap.ext
      intro f
      change A (S (OperatorDomination.maskedRestriction μ B G hG (m : ℝ) f)) = A (j (Q (L f)))
      rw [hS _ _ (OperatorDomination.coeFn_maskedRestrictionLp μ B G hG hdom
        p hp hptop (m : ℝ) (Nat.cast_nonneg m) f).symm]
    apply HilbertDyadicTrace.trace_tendsto_zero_of_power_bound (Rm m) (A.comp j) (Q.comp L)
      hfactor (‖Q‖ * ((m : ℝ) ^ (1 - 1 / p.toReal) * ‖B‖ ^ (1 / p.toReal)))
      (1 / p.toReal) (by positivity) hr
    intro n i hi
    change ‖Q (L (HilbertDyadicTrace.cellVector (𝕜 := 𝕜) n i))‖ ≤ _
    have hcell : ‖L (HilbertDyadicTrace.cellVector (𝕜 := 𝕜) n i)‖ ≤
        ((m : ℝ) ^ (1 - 1 / p.toReal) * ‖B‖ ^ (1 / p.toReal)) *
          (((2 : ℝ) ^ n)⁻¹) ^ (1 / p.toReal) :=
      norm_maskedRestrictionLp_cell_le (𝕜 := 𝕜) μ B G hG hdom p hp hptop
        (m : ℝ) (Nat.cast_nonneg m) n i hi
    exact (Q.le_opNorm (L (HilbertDyadicTrace.cellVector (𝕜 := 𝕜) n i))).trans
      ((mul_le_mul_of_nonneg_left hcell (norm_nonneg Q)).trans_eq (by ring))
  apply DyadicTrace.trace_tendsto_zero_of_approximation _ Rm htrace
  have heq (m : ℕ) : DyadicTrace.restrictLinfty (A.comp (S.comp B) - Rm m) =
      (A.comp S).comp (OperatorDomination.restriction μ (B - Bm m)) := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [DyadicTrace.restrictLinfty, OperatorDomination.restriction,
      Rm, sub_apply, ContinuousLinearMap.comp_apply, map_sub]
  have hnorm (m : ℕ) : ‖DyadicTrace.restrictLinfty (A.comp (S.comp B) - Rm m)‖ ≤
      ‖A.comp S‖ * ‖OperatorDomination.restriction μ (B - Bm m)‖ := by
    rw [heq]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  apply squeeze_zero (fun m => norm_nonneg _) hnorm
  simpa only [Bm, mul_zero] using
    (OperatorDomination.cutoff_approximation μ B G hG hGint hGpos hdom).const_mul ‖A.comp S‖

theorem one_le_norm_id_sub_of_smoothing
    (A : Lp 𝕜 1 ν →L[𝕜] IntervalL1 𝕜) (S : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν)
    (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp2 : p < 2) [Fact (1 ≤ p)]
    (Q : Lp 𝕜 p μ →L[𝕜] H) (j : H →L[𝕜] Lp 𝕜 1 ν)
    (hS : ∀ (g : Lp 𝕜 1 μ) (f : Lp 𝕜 p μ), g =ᵐ[μ] f → S g = j (Q f)) :
    1 ≤ ‖DyadicTrace.restrictLinfty
      (ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜) - A.comp (S.comp B))‖ :=
  DyadicTrace.one_le_norm_id_sub _ (trace_tendsto_zero_of_smoothing μ ν A S B p hp hp2 Q j hS)

end Smoothing

end PL1.SmoothingTrace
