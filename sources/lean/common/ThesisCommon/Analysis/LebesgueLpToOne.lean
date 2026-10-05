import ThesisCommon.Analysis.LpHaarCoefficient

/-! The contractive inclusion from Lp to L1 on a probability space,
implemented on actual a.e. equivalence classes. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsProbabilityMeasure μ]

def lebesgueLpToOneValue (f : Lp 𝕜 p μ) : Lp 𝕜 1 μ :=
  (memLp_one_iff_integrable.mpr ((Lp.memLp f).integrable Fact.out)).toLp f

theorem lebesgueLpToOneValue_coe (f : Lp 𝕜 p μ) :
    lebesgueLpToOneValue f =ᵐ[μ] f := MemLp.coeFn_toLp _

theorem lebesgueLpToOneValue_norm_le (f : Lp 𝕜 p μ) : ‖lebesgueLpToOneValue f‖ ≤ ‖f‖ := by
  rw [lebesgueLpToOneValue, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le Fact.out (Lp.memLp f).1)

def lebesgueLpToOne : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 1 μ :=
  LinearMap.mkContinuous
    { toFun := lebesgueLpToOneValue
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [lebesgueLpToOneValue_coe (f + g), lebesgueLpToOneValue_coe f,
          lebesgueLpToOneValue_coe g, Lp.coeFn_add f g,
          Lp.coeFn_add (lebesgueLpToOneValue f) (lebesgueLpToOneValue g)] with x h₁ h₂ h₃ h₄ h₅
        simp only [Pi.add_apply] at h₄ h₅
        rw [h₁, h₄, h₅, h₂, h₃]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [lebesgueLpToOneValue_coe (c • f), lebesgueLpToOneValue_coe f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (lebesgueLpToOneValue f)] with x h₁ h₂ h₃ h₄
        simp only [RingHom.id_apply]
        simp only [Pi.smul_apply] at h₃ h₄
        rw [h₁, h₃, h₄, h₂] }
    1 (fun f => by simpa only [one_mul] using lebesgueLpToOneValue_norm_le f)

theorem lebesgueLpToOne_coe (f : Lp 𝕜 p μ) : lebesgueLpToOne f =ᵐ[μ] f :=
  lebesgueLpToOneValue_coe f

theorem norm_lebesgueLpToOne_le : ‖lebesgueLpToOne (𝕜 := 𝕜) (p := p) (μ := μ)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end ThesisCommon
