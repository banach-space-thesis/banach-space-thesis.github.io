import PL1.LpInterpolation
import PL1.OperatorDomination

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PL1.LpInterpolation

variable {𝕜 F Ω : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_norm_le_mul_of_unit_bound (V : F →L[𝕜] Lp 𝕜 1 μ)
    (M : ℝ) (_hM : 0 ≤ M)
    (hunit : ∀ f, ‖f‖ ≤ 1 → ∀ᵐ x ∂μ, ‖V f x‖ ≤ M) (f : F) :
    ∀ᵐ x ∂μ, ‖V f x‖ ≤ M * ‖f‖ := by
  by_cases hf : f = 0
  · subst f
    filter_upwards [Lp.coeFn_zero (E := 𝕜) (p := 1) (μ := μ)] with x hx
    simp only [map_zero, hx, Pi.zero_apply, norm_zero, mul_zero, le_refl]
  have hfn : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
  let g : F := ((‖f‖⁻¹ : ℝ) : 𝕜) • f
  have hg : ‖g‖ = 1 := by
    simp only [g, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg f)), inv_mul_cancel₀ hfn]
  have hfg : f = (‖f‖ : 𝕜) • g := by
    dsimp [g]
    rw [smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hfn, RCLike.ofReal_one, one_smul]
  have hV : V f = (‖f‖ : 𝕜) • V g :=
    (congrArg V hfg).trans (map_smul V (‖f‖ : 𝕜) g)
  filter_upwards [hunit g hg.le, Lp.coeFn_smul (‖f‖ : 𝕜) (V g)] with x hx hsmul
  rw [hV, hsmul, Pi.smul_apply, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg f)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx (norm_nonneg f)

variable (V : F →L[𝕜] Lp 𝕜 1 μ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ∞)
  [Fact (1 ≤ p)] (M : ℝ) (hM : 0 ≤ M)
  (hunit : ∀ f, ‖f‖ ≤ 1 → ∀ᵐ x ∂μ, ‖V f x‖ ≤ M)

def boundedLiftFun (f : F) : Lp 𝕜 p μ :=
  (memLp_of_ae_norm_bound (V f) p hp hptop (M * ‖f‖)
    (ae_norm_le_mul_of_unit_bound V M hM hunit f)).toLp (V f)

omit [Fact (1 ≤ p)] in
theorem coeFn_boundedLiftFun (f : F) : boundedLiftFun V p hp hptop M hM hunit f =ᵐ[μ] V f :=
  MemLp.coeFn_toLp _

omit [Fact (1 ≤ p)] in
theorem boundedLiftFun_add (f g : F) :
    boundedLiftFun V p hp hptop M hM hunit (f + g) =
      boundedLiftFun V p hp hptop M hM hunit f + boundedLiftFun V p hp hptop M hM hunit g := by
  apply Lp.ext
  filter_upwards [coeFn_boundedLiftFun V p hp hptop M hM hunit (f + g),
    coeFn_boundedLiftFun V p hp hptop M hM hunit f,
    coeFn_boundedLiftFun V p hp hptop M hM hunit g,
    Lp.coeFn_add (V f) (V g),
    Lp.coeFn_add (boundedLiftFun V p hp hptop M hM hunit f)
      (boundedLiftFun V p hp hptop M hM hunit g)] with x hfg hf hg hv hl
  rw [hfg, map_add, hv, hl, Pi.add_apply, Pi.add_apply, hf, hg]

omit [Fact (1 ≤ p)] in
theorem boundedLiftFun_smul (c : 𝕜) (f : F) :
    boundedLiftFun V p hp hptop M hM hunit (c • f) =
      c • boundedLiftFun V p hp hptop M hM hunit f := by
  apply Lp.ext
  filter_upwards [coeFn_boundedLiftFun V p hp hptop M hM hunit (c • f),
    coeFn_boundedLiftFun V p hp hptop M hM hunit f,
    Lp.coeFn_smul c (V f),
    Lp.coeFn_smul c (boundedLiftFun V p hp hptop M hM hunit f)] with x hcf hf hv hl
  rw [hcf, map_smul, hv, hl, Pi.smul_apply, Pi.smul_apply, hf]

omit [Fact (1 ≤ p)] in
theorem norm_boundedLiftFun_le (f : F) :
    ‖boundedLiftFun V p hp hptop M hM hunit f‖ ≤ (M + ‖V‖) * ‖f‖ := by
  have hpR : (1 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hptop hp
  have hp0 : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hpR
  let C : ℝ := (M + ‖V‖) * ‖f‖
  have hC : 0 ≤ C := mul_nonneg (add_nonneg hM (norm_nonneg V)) (norm_nonneg f)
  have hpoint : ∀ᵐ x ∂μ, ‖V f x‖ₑ ≤ ENNReal.ofReal C := by
    filter_upwards [ae_norm_le_mul_of_unit_bound V M hM hunit f] with x hx
    have hle : ‖V f x‖ ≤ C := hx.trans (by dsimp [C]; gcongr; exact le_add_of_nonneg_right (norm_nonneg V))
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hle
  have hL1 : eLpNorm (V f) 1 μ ≤ ENNReal.ofReal C := by
    rw [← Lp.enorm_def, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    exact (V.le_opNorm f).trans (by dsimp [C]; gcongr; exact le_add_of_nonneg_left hM)
  have hb := eLpNorm_le_of_ae_bound (V f) (Lp.aestronglyMeasurable (V f))
    p hp hptop (ENNReal.ofReal C) (ENNReal.ofReal C) hpoint hL1
  rw [← ENNReal.rpow_add_of_nonneg _ _
    (sub_nonneg.mpr ((div_le_one hp0).mpr hpR)) (by positivity), sub_add_cancel, ENNReal.rpow_one] at hb
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [boundedLiftFun, Lp.norm_toLp, ENNReal.toReal_ofReal hC] using h

/-- A continuous linear Lp lift of an L1-valued operator whose unit-ball
images have a common essential bound. -/
def boundedLift : F →L[𝕜] Lp 𝕜 p μ :=
  LinearMap.mkContinuous
    { toFun := boundedLiftFun V p hp hptop M hM hunit
      map_add' := boundedLiftFun_add V p hp hptop M hM hunit
      map_smul' := boundedLiftFun_smul V p hp hptop M hM hunit }
    (M + ‖V‖) (norm_boundedLiftFun_le V p hp hptop M hM hunit)

theorem coeFn_boundedLift (f : F) : boundedLift V p hp hptop M hM hunit f =ᵐ[μ] V f :=
  coeFn_boundedLiftFun V p hp hptop M hM hunit f

theorem norm_boundedLift_apply_le (f : F) :
    ‖boundedLift V p hp hptop M hM hunit f‖ ≤
      (M * ‖f‖) ^ (1 - 1 / p.toReal) * ‖V f‖ ^ (1 / p.toReal) :=
  norm_toLp_le_of_ae_norm_bound (V f) p hp hptop (M * ‖f‖)
    (mul_nonneg hM (norm_nonneg f)) (ae_norm_le_mul_of_unit_bound V M hM hunit f)
    (memLp_of_ae_norm_bound (V f) p hp hptop (M * ‖f‖)
      (ae_norm_le_mul_of_unit_bound V M hM hunit f))

theorem norm_boundedLift_apply_le_of_norm_le_one (f : F) (hf : ‖f‖ ≤ 1) :
    ‖boundedLift V p hp hptop M hM hunit f‖ ≤
      M ^ (1 - 1 / p.toReal) * ‖V f‖ ^ (1 / p.toReal) :=
  norm_toLp_le_of_ae_norm_bound (V f) p hp hptop M hM (hunit f hf)
    (memLp_of_ae_norm_bound (V f) p hp hptop (M * ‖f‖)
      (ae_norm_le_mul_of_unit_bound V M hM hunit f))

theorem norm_boundedLift_le : ‖boundedLift V p hp hptop M hM hunit‖ ≤ M + ‖V‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hM (norm_nonneg V))
    (norm_boundedLiftFun_le V p hp hptop M hM hunit)

end PL1.LpInterpolation

namespace PL1.OperatorDomination

variable {𝕜 Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω] (μ : Measure Ω)
variable (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ)
  (G : Ω → ℝ) (hG : Measurable G)
  (hdom : ∀ f : Lp 𝕜 ∞ intervalMeasure, ‖f‖ ≤ 1 →
    ∀ᵐ x ∂μ, ‖restriction μ B f x‖ ≤ G x)
  (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ∞) [Fact (1 ≤ p)]
  (M : ℝ) (hM : 0 ≤ M)

def maskedRestriction : Lp 𝕜 ∞ intervalMeasure →L[𝕜] Lp 𝕜 1 μ :=
  (L1Masks.mask μ {x | G x ≤ M} (measurableSet_le hG measurable_const)).comp (restriction μ B)

include hdom hM in
omit [Fact (1 ≤ p)] in
theorem maskedRestriction_unit_bound (f : Lp 𝕜 ∞ intervalMeasure) (hf : ‖f‖ ≤ 1) :
    ∀ᵐ x ∂μ, ‖maskedRestriction μ B G hG M f x‖ ≤ M := by
  filter_upwards [hdom f hf, L1Masks.coeFn_mask μ {x | G x ≤ M}
    (measurableSet_le hG measurable_const) (restriction μ B f)] with x hx hm
  change ‖L1Masks.mask μ {x | G x ≤ M} (measurableSet_le hG measurable_const)
    (restriction μ B f) x‖ ≤ M
  rw [hm]
  by_cases h : G x ≤ M
  · simpa only [Set.indicator_of_mem (show x ∈ {x | G x ≤ M} from h)] using hx.trans h
  · simpa only [Set.indicator_of_notMem (show x ∉ {x | G x ≤ M} from h), norm_zero] using hM

/-- The measurable target cutoff lifts the restricted operator genuinely to
Lp. The source is L-infinity, as required by the domination theorem. -/
def maskedRestrictionLp : Lp 𝕜 ∞ intervalMeasure →L[𝕜] Lp 𝕜 p μ :=
  LpInterpolation.boundedLift (maskedRestriction μ B G hG M) p hp hptop M hM
    (maskedRestriction_unit_bound μ B G hG hdom M hM)

theorem coeFn_maskedRestrictionLp (f : Lp 𝕜 ∞ intervalMeasure) :
    maskedRestrictionLp μ B G hG hdom p hp hptop M hM f =ᵐ[μ]
      maskedRestriction μ B G hG M f :=
  LpInterpolation.coeFn_boundedLift _ _ _ _ _ _ _ f

theorem norm_maskedRestrictionLp_apply_le (f : Lp 𝕜 ∞ intervalMeasure) (hf : ‖f‖ ≤ 1) :
    ‖maskedRestrictionLp μ B G hG hdom p hp hptop M hM f‖ ≤
      M ^ (1 - 1 / p.toReal) * ‖maskedRestriction μ B G hG M f‖ ^ (1 / p.toReal) :=
  LpInterpolation.norm_boundedLift_apply_le_of_norm_le_one _ _ _ _ _ _ _ f hf

end PL1.OperatorDomination
