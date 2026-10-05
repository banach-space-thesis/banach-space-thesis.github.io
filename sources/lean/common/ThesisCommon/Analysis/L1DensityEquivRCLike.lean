import ThesisCommon.Analysis.L1DensityEquiv

/-! Positive change of density gives an onto scalar-linear L1 isometry
for either real or complex scalars. The underlying multiplication is the
actual mathlib density isometry; complex linearity is proved on a.e. classes. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {g : X → ℝ≥0}

theorem withDensitySMulLI_coe_rclike (hg : Measurable g)
    (f : Lp 𝕜 1 (μ.withDensity (fun x => (g x : ℝ≥0∞)))) :
    withDensitySMulLI μ hg f =ᵐ[μ] fun x => (g x : ℝ) • f x := by
  simpa only [withDensitySMulLI_apply, NNReal.smul_def] using
    (memL1_smul_of_L1_withDensity hg f).coeFn_toLp

theorem withDensitySMulLI_surjective_rclike (hg : Measurable g)
    (hpos : ∀ᵐ x ∂μ, 0 < g x) :
    Function.Surjective (withDensitySMulLI μ (E := 𝕜) hg) := by
  intro f
  let v : X → 𝕜 := fun x => (g x : ℝ)⁻¹ • f x
  have heq : (fun x => (g x : ℝ) • v x) =ᵐ[μ] f := hpos.mono fun x hx => by
    have hx' : (g x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hx', one_smul]
  have hi : Integrable v (μ.withDensity (fun x => (g x : ℝ≥0∞))) := by
    apply (integrable_withDensity_iff_integrable_coe_smul hg).mpr
    exact (L1.integrable_coeFn f).congr heq.symm
  refine ⟨hi.toL1 v, ?_⟩
  apply Lp.ext
  filter_upwards [withDensitySMulLI_coe_rclike hg (hi.toL1 v), heq,
    (ae_withDensity_coe_iff_of_pos hg hpos).mp (Integrable.coeFn_toL1 hi)] with x hx hx' hx''
  rw [hx, hx'', hx']

def lOneWithDensityLI_rclike (hg : Measurable g) :
    Lp 𝕜 1 (μ.withDensity (fun x => (g x : ℝ≥0∞))) →ₗᵢ[𝕜] Lp 𝕜 1 μ where
  toFun := withDensitySMulLI μ hg
  map_add' := (withDensitySMulLI μ hg).map_add
  map_smul' := by
    intro c f
    apply Lp.ext
    filter_upwards [withDensitySMulLI_coe_rclike hg (c • f),
      withDensitySMulLI_coe_rclike hg f,
      Lp.coeFn_smul c (withDensitySMulLI μ hg f),
      (ae_withDensity_iff hg.coe_nnreal_ennreal).mp (Lp.coeFn_smul c f)] with x hleft hright hout hin
    rw [RingHom.id_apply, hleft, hout, Pi.smul_apply, hright]
    by_cases hx : g x = 0
    · simp [hx]
    · rw [hin (by simpa only [ne_eq, ENNReal.coe_eq_zero] using hx), Pi.smul_apply]
      exact smul_comm _ _ _
  norm_map' := (withDensitySMulLI μ hg).norm_map

def lOneWithDensityEquiv_rclike (hg : Measurable g) (hpos : ∀ᵐ x ∂μ, 0 < g x) :
    Lp 𝕜 1 (μ.withDensity (fun x => (g x : ℝ≥0∞))) ≃ₗᵢ[𝕜] Lp 𝕜 1 μ :=
  LinearIsometryEquiv.ofSurjective (lOneWithDensityLI_rclike hg)
    (withDensitySMulLI_surjective_rclike hg hpos)

end ThesisCommon
