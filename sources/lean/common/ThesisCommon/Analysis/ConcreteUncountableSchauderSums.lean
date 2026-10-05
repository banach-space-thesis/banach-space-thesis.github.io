import ThesisCommon.Analysis.LpSchauderFamily
import ThesisCommon.Analysis.CZeroSchauderFamily
import ThesisCommon.Analysis.UncountableSchauderSumComplete

/-! Exact coordinate-preserving linear isometries between the arbitrary-index
scalar-basis sums and the actual vector-valued ℓp and c₀ spaces.
-/
noncomputable section
open Filter Topology
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 Γ Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

section CZero
variable [TopologicalSpace Γ] [DiscreteTopology Γ]

omit [NormedSpace 𝕜 Y] in
theorem memUncountableSchauderSum_cZero_iff (y : Γ → Y) :
    MemUncountableSchauderSum (scalarCZeroSchauderFamily (𝕜 := 𝕜)) y ↔
      Tendsto y cofinite (𝓝 0) := by
  constructor
  · rintro ⟨x, hx⟩
    have heval (γ : Γ) : x γ = (‖y γ‖ : 𝕜) := hx γ
    have ht := x.zero_at_infty'.norm
    rw [cocompact_eq_cofinite] at ht
    change Tendsto (fun γ => ‖x γ‖) cofinite (𝓝 ‖(0 : 𝕜)‖) at ht
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [heval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), norm_zero] using ht
  · intro hy
    refine ⟨{ toFun := fun γ => (‖y γ‖ : 𝕜)
              continuous_toFun := continuous_of_discreteTopology
              zero_at_infty' := ?_ }, fun _ => rfl⟩
    rw [cocompact_eq_cofinite]
    simpa only [norm_zero, RCLike.ofReal_zero] using
      (RCLike.continuous_ofReal.tendsto 0).comp
        (show Tendsto (fun γ => ‖y γ‖) cofinite (𝓝 0) from by simpa using hy.norm)

variable (hb : (scalarCZeroSchauderFamily (𝕜 := 𝕜) (Γ := Γ)).IsOneUnconditional)

def cZeroUncountableSchauderSumValue
    (y : UncountableSchauderSum scalarCZeroSchauderFamily hb Y) : C₀(Γ, Y) where
  toFun := y
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite]
    exact (memUncountableSchauderSum_cZero_iff y).mp y.property

@[simp] theorem cZeroUncountableSchauderSumValue_apply
    (y : UncountableSchauderSum scalarCZeroSchauderFamily hb Y) (γ : Γ) :
    cZeroUncountableSchauderSumValue hb y γ = y γ := rfl

theorem cZeroUncountableSchauderSumValue_norm
    (y : UncountableSchauderSum scalarCZeroSchauderFamily hb Y) :
    ‖cZeroUncountableSchauderSumValue hb y‖ = ‖y‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg y)).mpr
    exact UncountableSchauderSum.norm_apply_le y
  · rw [UncountableSchauderSum.norm_def]
    apply (BoundedContinuousFunction.norm_le
      (norm_nonneg (cZeroUncountableSchauderSumValue hb y))).mpr
    intro γ
    have hγ : UncountableSchauderSum.normVector y γ = (‖y γ‖ : 𝕜) :=
      UncountableSchauderSum.coord_normVector y γ
    change ‖UncountableSchauderSum.normVector y γ‖ ≤ _
    rw [hγ, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    exact BoundedContinuousFunction.norm_coe_le_norm
      (cZeroUncountableSchauderSumValue hb y).toBCF γ

def cZeroUncountableSchauderSumEquiv :
    UncountableSchauderSum scalarCZeroSchauderFamily hb Y ≃ₗᵢ[𝕜] C₀(Γ, Y) where
  toFun := cZeroUncountableSchauderSumValue hb
  invFun y := ⟨y, (memUncountableSchauderSum_cZero_iff y).mpr (by
    simpa only [cocompact_eq_cofinite] using y.zero_at_infty')⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  norm_map' := cZeroUncountableSchauderSumValue_norm hb

@[simp] theorem cZeroUncountableSchauderSumEquiv_apply
    (y : UncountableSchauderSum scalarCZeroSchauderFamily hb Y) (γ : Γ) :
    cZeroUncountableSchauderSumEquiv (Y := Y) hb y γ = y γ := rfl

@[simp] theorem cZeroUncountableSchauderSumEquiv_symm_apply (y : C₀(Γ, Y)) (γ : Γ) :
    (cZeroUncountableSchauderSumEquiv (Y := Y) hb).symm y γ = y γ := rfl

end CZero

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)

omit [NormedSpace 𝕜 Y] in
theorem memUncountableSchauderSum_lp_iff (y : Γ → Y) :
    MemUncountableSchauderSum (scalarLpSchauderFamily (𝕜 := 𝕜) p hp) y ↔ Memℓp y p := by
  constructor
  · rintro ⟨x, hx⟩
    apply mem_lp_of_norm_le_mul x y zero_le_one
    intro γ
    have hγ : x γ = (‖y γ‖ : 𝕜) := hx γ
    simp only [hγ, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), one_mul, le_refl]
  · intro hy
    refine ⟨⟨fun γ => (‖y γ‖ : 𝕜), ?_⟩, fun _ => rfl⟩
    apply mem_lp_of_norm_le_mul (⟨y, hy⟩ : lp (fun _ : Γ => Y) p)
      (fun γ => (‖y γ‖ : 𝕜)) zero_le_one
    intro γ
    simp only [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), one_mul]
    exact le_rfl

variable (hb : (scalarLpSchauderFamily (𝕜 := 𝕜) (Γ := Γ) p hp).IsOneUnconditional)

def lpUncountableSchauderSumValue
    (y : UncountableSchauderSum (scalarLpSchauderFamily p hp) hb Y) :
    lp (fun _ : Γ => Y) p :=
  ⟨fun γ => y γ, (memUncountableSchauderSum_lp_iff p hp y).mp y.property⟩

@[simp] theorem lpUncountableSchauderSumValue_apply
    (y : UncountableSchauderSum (scalarLpSchauderFamily p hp) hb Y) (γ : Γ) :
    lpUncountableSchauderSumValue p hp hb y γ = y γ := rfl

theorem lpUncountableSchauderSumValue_norm
    (y : UncountableSchauderSum (scalarLpSchauderFamily p hp) hb Y) :
    ‖lpUncountableSchauderSumValue p hp hb y‖ = ‖y‖ := by
  rw [UncountableSchauderSum.norm_def]
  have hγ (γ : Γ) : UncountableSchauderSum.normVector y γ = (‖y γ‖ : 𝕜) :=
    UncountableSchauderSum.coord_normVector y γ
  apply le_antisymm
  · simpa only [one_mul] using lp_norm_le_mul_of_pointwise
      (UncountableSchauderSum.normVector y) (lpUncountableSchauderSumValue p hp hb y)
      zero_le_one (fun γ => by simp [hγ])
  · simpa only [one_mul] using lp_norm_le_mul_of_pointwise
      (lpUncountableSchauderSumValue p hp hb y) (UncountableSchauderSum.normVector y)
      zero_le_one (fun γ => by simp [hγ])

def lpUncountableSchauderSumEquiv :
    UncountableSchauderSum (scalarLpSchauderFamily p hp) hb Y ≃ₗᵢ[𝕜]
      lp (fun _ : Γ => Y) p where
  toFun := lpUncountableSchauderSumValue p hp hb
  invFun y := ⟨y, (memUncountableSchauderSum_lp_iff p hp y).mpr y.property⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  norm_map' := lpUncountableSchauderSumValue_norm p hp hb

@[simp] theorem lpUncountableSchauderSumEquiv_apply
    (y : UncountableSchauderSum (scalarLpSchauderFamily p hp) hb Y) (γ : Γ) :
    lpUncountableSchauderSumEquiv (Y := Y) p hp hb y γ = y γ := rfl

@[simp] theorem lpUncountableSchauderSumEquiv_symm_apply
    (y : lp (fun _ : Γ => Y) p) (γ : Γ) :
    (lpUncountableSchauderSumEquiv (Y := Y) p hp hb).symm y γ = y γ := rfl

end ThesisCommon
