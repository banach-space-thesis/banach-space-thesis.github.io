import ThesisCommon.Analysis.L1DensityOrder
import Mathlib.MeasureTheory.Function.Holder

/-! The actual positive-density L1 isometry is a lattice isomorphism and
commutes with multiplication by every actual L-infinity vector. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {g : X → ℝ≥0}

theorem memLp_top_withDensity {f : X → ℝ} (hf : MemLp f ∞ μ) :
    MemLp f ∞ (μ.withDensity (fun x => (g x : ℝ≥0∞))) := by
  refine ⟨hf.1.mono_ac (withDensity_absolutelyContinuous μ _), ?_⟩
  simp only [eLpNorm_exponent_top] at hf ⊢
  exact (eLpNormEssSup_mono_measure f (withDensity_absolutelyContinuous μ _)).trans_lt hf.2

def lInfinityWithDensity (g : X → ℝ≥0) (h : Lp ℝ ∞ μ) :
    Lp ℝ ∞ (μ.withDensity (fun x => (g x : ℝ≥0∞))) :=
  (memLp_top_withDensity (g := g) (Lp.memLp h)).toLp h

theorem lInfinityWithDensity_coe (g : X → ℝ≥0) (h : Lp ℝ ∞ μ) :
    lInfinityWithDensity g h =ᵐ[μ.withDensity (fun x => (g x : ℝ≥0∞))] h :=
  MemLp.coeFn_toLp _

theorem ae_withDensity_eq_of_pos (hg : Measurable g) (hpos : ∀ᵐ x ∂μ, 0 < g x) :
    ae (μ.withDensity (fun x => (g x : ℝ≥0∞))) = ae μ := by
  apply Filter.ext
  intro s
  exact ae_withDensity_coe_iff_of_pos hg hpos

theorem norm_lInfinityWithDensity (hg : Measurable g) (hpos : ∀ᵐ x ∂μ, 0 < g x)
    (h : Lp ℝ ∞ μ) : ‖lInfinityWithDensity g h‖ = ‖h‖ := by
  simp only [Lp.norm_def]
  rw [eLpNorm_congr_ae (lInfinityWithDensity_coe g h)]
  simp only [eLpNorm_exponent_top, eLpNormEssSup, essSup,
    ae_withDensity_eq_of_pos hg hpos]

theorem lOneWithDensityEquiv_symm_coe (hg : Measurable g)
    (hpos : ∀ᵐ x ∂μ, 0 < g x) (f : Lp ℝ 1 μ) :
    (lOneWithDensityEquiv hg hpos).symm f =ᵐ[μ] fun x => f x / (g x : ℝ) := by
  have hcoe := withDensitySMulLI_coe hg ((lOneWithDensityEquiv hg hpos).symm f)
  have heq : withDensitySMulLI μ hg ((lOneWithDensityEquiv hg hpos).symm f) = f :=
    (lOneWithDensityEquiv hg hpos).apply_symm_apply f
  rw [heq] at hcoe
  filter_upwards [hcoe, hpos] with x hx hxpos
  have hne : (g x : ℝ) ≠ 0 := by exact_mod_cast hxpos.ne'
  exact (eq_div_iff hne).mpr (by simpa only [mul_comm] using hx.symm)

theorem lOneWithDensityEquiv_le_iff (hg : Measurable g)
    (hpos : ∀ᵐ x ∂μ, 0 < g x)
    (f k : Lp ℝ 1 (μ.withDensity (fun x => (g x : ℝ≥0∞)))) :
    lOneWithDensityEquiv hg hpos f ≤ lOneWithDensityEquiv hg hpos k ↔ f ≤ k := by
  rw [← sub_nonneg, ← map_sub, lOneWithDensityEquiv_nonneg_iff, sub_nonneg]

def lOneWithDensityOrderIso (hg : Measurable g) (hpos : ∀ᵐ x ∂μ, 0 < g x) :
    Lp ℝ 1 (μ.withDensity (fun x => (g x : ℝ≥0∞))) ≃o Lp ℝ 1 μ where
  toEquiv := (lOneWithDensityEquiv hg hpos).toEquiv
  map_rel_iff' := lOneWithDensityEquiv_le_iff hg hpos _ _

theorem lOneWithDensityEquiv_multiplier (hg : Measurable g)
    (hpos : ∀ᵐ x ∂μ, 0 < g x) (h : Lp ℝ ∞ μ)
    (f : Lp ℝ 1 (μ.withDensity (fun x => (g x : ℝ≥0∞)))) :
    lOneWithDensityEquiv hg hpos (lInfinityWithDensity g h • f : Lp ℝ 1 _) =
      (h • lOneWithDensityEquiv hg hpos f : Lp ℝ 1 μ) := by
  apply Lp.ext
  have htrans := (ae_withDensity_coe_iff_of_pos hg hpos).mp (lInfinityWithDensity_coe g h)
  have hmul := (ae_withDensity_coe_iff_of_pos hg hpos).mp
    (Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) (lInfinityWithDensity g h) f)
  filter_upwards [withDensitySMulLI_coe hg (lInfinityWithDensity g h • f : Lp ℝ 1 _),
    withDensitySMulLI_coe hg f, Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) h
      (lOneWithDensityEquiv hg hpos f), htrans, hmul] with x hleft hright hout htransx hmulx
  change withDensitySMulLI μ hg _ x = _
  rw [hleft, hout, hmulx]
  change (g x : ℝ) * (lInfinityWithDensity g h x * f x) = h x * withDensitySMulLI μ hg f x
  rw [htransx, hright]
  ring

theorem lOneWithDensityEquiv_symm_multiplier (hg : Measurable g)
    (hpos : ∀ᵐ x ∂μ, 0 < g x) (h : Lp ℝ ∞ μ) (f : Lp ℝ 1 μ) :
    (lOneWithDensityEquiv hg hpos).symm (h • f : Lp ℝ 1 μ) =
      (lInfinityWithDensity g h • (lOneWithDensityEquiv hg hpos).symm f : Lp ℝ 1 _) := by
  apply (lOneWithDensityEquiv hg hpos).injective
  rw [LinearIsometryEquiv.apply_symm_apply, lOneWithDensityEquiv_multiplier,
    LinearIsometryEquiv.apply_symm_apply]

end ThesisCommon
