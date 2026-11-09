import PL1.ConcreteResolvents

/-! # The genuine strongly continuous noise semigroup and full resolvent limit -/

noncomputable section
open Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace PL1.Noise
open Walsh

variable (𝕜 : Type*) [RCLike 𝕜] (rates : ℕ → ℝ≥0)

def noiseL1 (u : ℝ≥0) : Lp 𝕜 1 haar →L[𝕜] Lp 𝕜 1 haar :=
  convolutionL1 (measure rates u)

theorem norm_noiseL1_le_one (u : ℝ≥0) : ‖noiseL1 𝕜 rates u‖ ≤ 1 :=
  norm_convolutionL1_le_one _

@[simp] theorem noiseL1_character (u : ℝ≥0) (F : Finset ℕ) :
    noiseL1 𝕜 rates u (scalarCharacterLp 𝕜 1 F) =
      ((Real.exp (-(u : ℝ) * rateSum rates F) : ℝ) : 𝕜) • scalarCharacterLp 𝕜 1 F := by
  rw [noiseL1, convolutionL1_scalarCharacter]
  congr 2
  exact integral_character rates u F

@[simp] theorem noiseL1_zero : noiseL1 𝕜 rates 0 = ContinuousLinearMap.id 𝕜 (Lp 𝕜 1 haar) := by
  apply continuousLinearMap_ext_on_scalarCharacterL1
  intro F
  simp only [noiseL1_character, NNReal.coe_zero, neg_zero, zero_mul, Real.exp_zero,
    RCLike.ofReal_one, one_smul, ContinuousLinearMap.id_apply]

theorem noiseL1_add (u v : ℝ≥0) :
    noiseL1 𝕜 rates (u + v) = (noiseL1 𝕜 rates u).comp (noiseL1 𝕜 rates v) := by
  apply continuousLinearMap_ext_on_scalarCharacterL1
  intro F
  simp only [ContinuousLinearMap.comp_apply, noiseL1_character, map_smul, smul_smul]
  congr 1
  rw [NNReal.coe_add, neg_add, add_mul, Real.exp_add, RCLike.ofReal_mul]
  exact mul_comm _ _

theorem continuous_noiseL1_apply (f : Lp 𝕜 1 haar) : Continuous (fun u => noiseL1 𝕜 rates u f) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply tendsto_apply_of_dense_span (scalarCharacterLp 𝕜 1)
    (dense_span_scalarCharacterLp 𝕜 1 (by norm_num)) (noiseL1 𝕜 rates)
    (noiseL1 𝕜 rates u) (𝓝 u) 1 (norm_noiseL1_le_one 𝕜 rates)
  intro F
  simp only [noiseL1_character]
  exact (show Continuous (fun v : ℝ≥0 =>
    ((Real.exp (-(v : ℝ) * rateSum rates F) : ℝ) : 𝕜) • scalarCharacterLp 𝕜 1 F) by
    fun_prop).tendsto u

theorem noiseL1_strong_zero (f : Lp 𝕜 1 haar) :
    Tendsto (fun u => noiseL1 𝕜 rates u f) (𝓝 0) (𝓝 f) := by
  simpa only [noiseL1_zero, ContinuousLinearMap.id_apply] using
    (continuous_noiseL1_apply 𝕜 rates f).tendsto 0

theorem noiseL1_resolvent_commute (u : ℝ≥0) (t : PositiveTime) :
    (noiseL1 𝕜 rates u).comp (resolventL1 𝕜 rates t) =
      (resolventL1 𝕜 rates t).comp (noiseL1 𝕜 rates u) := by
  apply continuousLinearMap_ext_on_scalarCharacterL1
  intro F
  simp only [ContinuousLinearMap.comp_apply, noiseL1_character,
    resolventL1_scalarCharacter, map_smul, smul_smul, mul_comm]

/-- Full strong resolvent convergence along every positive time family tending
to zero, extending the dyadic convergence used in the main construction. -/
theorem resolventL1_strong_zero {α : Type*} (l : Filter α) (t : α → PositiveTime)
    (ht : Tendsto (fun a => (t a : ℝ)) l (𝓝 0)) (f : Lp 𝕜 1 haar) :
    Tendsto (fun a => resolventL1 𝕜 rates (t a) f) l (𝓝 f) := by
  apply tendsto_apply_of_dense_span (scalarCharacterLp 𝕜 1)
    (dense_span_scalarCharacterLp 𝕜 1 (by norm_num))
    (fun a => resolventL1 𝕜 rates (t a)) (ContinuousLinearMap.id 𝕜 _) l 1
    (fun a => norm_resolventL1_le_one 𝕜 rates (t a))
  intro F
  have hreal : Tendsto (fun a => (1 + (t a : ℝ) * rateSum rates F)⁻¹) l (𝓝 (1 : ℝ)) := by
    simpa using ((ht.mul_const (rateSum rates F)).const_add 1).inv₀ (by norm_num)
  have hcast := ((RCLike.continuous_ofReal : Continuous (fun x : ℝ => (x : 𝕜))).tendsto
    (1 : ℝ)).comp hreal
  simpa only [Function.comp_def, resolventL1_scalarCharacter, RCLike.ofReal_one, one_smul,
    ContinuousLinearMap.id_apply] using hcast.smul_const (scalarCharacterLp 𝕜 1 F)

end PL1.Noise
