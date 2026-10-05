import ThesisCommon.Analysis.CZeroSchauderBasis
import ThesisCommon.Analysis.LpSchauderBasis
import ThesisCommon.Analysis.SchauderSumComplete

/-! Coordinate-preserving linear isometries from the manuscript's basis sums
to the actual c₀ and finite-exponent ℓp sequence spaces. The coefficient
space need not be complete for these identifications. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

omit [NormedSpace 𝕜 Y] in
/-- The basis-sum membership condition for the scalar c₀ basis is precisely
norm convergence of the coefficient sequence to zero. -/
theorem memSchauderSum_cZero_iff (y : ℕ → Y) :
    MemSchauderSum (scalarCZeroSchauderBasis (𝕜 := 𝕜)) y ↔
      Tendsto y atTop (𝓝 0) := by
  constructor
  · rintro ⟨x, hx⟩
    have ht := (scalarCZeroSchauderBasis (𝕜 := 𝕜)).coord_tendsto_zero x
    simp only [hx] at ht
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), norm_zero] using ht.norm
  · intro hy
    refine ⟨{ toFun := fun n => (‖y n‖ : 𝕜)
              continuous_toFun := continuous_of_discreteTopology
              zero_at_infty' := ?_ }, fun _ => rfl⟩
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    simpa only [norm_zero, RCLike.ofReal_zero] using
      (RCLike.continuous_ofReal.tendsto 0).comp
        (show Tendsto (fun n => ‖y n‖) atTop (𝓝 0) from by simpa using hy.norm)

variable (hb : (scalarCZeroSchauderBasis (𝕜 := 𝕜)).IsOneUnconditional)

/-- Read a c₀ basis sum as its actual null sequence. -/
def cZeroSchauderSumValue (y : SchauderSum scalarCZeroSchauderBasis hb Y) : CZeroSum Y where
  toFun := y
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    exact (memSchauderSum_cZero_iff y).mp y.property

@[simp] theorem cZeroSchauderSumValue_apply
    (y : SchauderSum scalarCZeroSchauderBasis hb Y) (n : ℕ) :
    cZeroSchauderSumValue hb y n = y n := rfl

theorem cZeroSchauderSumValue_norm (y : SchauderSum scalarCZeroSchauderBasis hb Y) :
    ‖cZeroSchauderSumValue hb y‖ = ‖y‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg y)).mpr
    exact SchauderSum.norm_apply_le y
  · rw [SchauderSum.norm_def]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg (cZeroSchauderSumValue hb y))).mpr
    intro n
    have hn : SchauderSum.normVector y n = (‖y n‖ : 𝕜) :=
      SchauderSum.coord_normVector y n
    change ‖SchauderSum.normVector y n‖ ≤ _
    rw [hn, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    exact BoundedContinuousFunction.norm_coe_le_norm (cZeroSchauderSumValue hb y).toBCF n

/-- The actual isometric identification c₀(Y) = (c₀-basis)(Y), with every
coordinate preserved in both directions. -/
def cZeroSchauderSumEquiv :
    SchauderSum scalarCZeroSchauderBasis hb Y ≃ₗᵢ[𝕜] CZeroSum Y where
  toFun := cZeroSchauderSumValue hb
  invFun y := ⟨y, (memSchauderSum_cZero_iff y).mpr (by
    simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using y.zero_at_infty')⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  norm_map' := cZeroSchauderSumValue_norm hb

@[simp] theorem cZeroSchauderSumEquiv_apply
    (y : SchauderSum scalarCZeroSchauderBasis hb Y) (n : ℕ) :
    cZeroSchauderSumEquiv (Y := Y) hb y n = y n := rfl

@[simp] theorem cZeroSchauderSumEquiv_symm_apply (y : CZeroSum Y) (n : ℕ) :
    (cZeroSchauderSumEquiv (Y := Y) hb).symm y n = y n := rfl

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)

omit [NormedSpace 𝕜 Y] in
/-- For the scalar ℓp basis, membership in the manuscript's basis sum is
exactly mathlib's p-summability predicate for the vector-valued coordinates. -/
theorem memSchauderSum_lp_iff (y : ℕ → Y) :
    MemSchauderSum (scalarLpSchauderBasis (𝕜 := 𝕜) p hp) y ↔ Memℓp y p := by
  constructor
  · rintro ⟨x, hx⟩
    apply mem_lp_of_norm_le_mul x y zero_le_one
    intro n
    have hn : x n = (‖y n‖ : 𝕜) := hx n
    simp only [hn, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), one_mul, le_refl]
  · intro hy
    refine ⟨⟨fun n => (‖y n‖ : 𝕜), ?_⟩, fun _ => rfl⟩
    apply mem_lp_of_norm_le_mul (⟨y, hy⟩ : lp (fun _ : ℕ => Y) p)
      (fun n => (‖y n‖ : 𝕜)) zero_le_one
    intro n
    simp only [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), one_mul]
    exact le_rfl

variable (hlp : (scalarLpSchauderBasis (𝕜 := 𝕜) p hp).IsOneUnconditional)

/-- Read an ℓp basis sum as the same actual p-summable sequence. -/
def lpSchauderSumValue (y : SchauderSum (scalarLpSchauderBasis p hp) hlp Y) :
    lp (fun _ : ℕ => Y) p := ⟨fun n => y n, (memSchauderSum_lp_iff p hp y).mp y.property⟩

@[simp] theorem lpSchauderSumValue_apply
    (y : SchauderSum (scalarLpSchauderBasis p hp) hlp Y) (n : ℕ) :
    lpSchauderSumValue p hp hlp y n = y n := rfl

theorem lpSchauderSumValue_norm (y : SchauderSum (scalarLpSchauderBasis p hp) hlp Y) :
    ‖lpSchauderSumValue p hp hlp y‖ = ‖y‖ := by
  rw [SchauderSum.norm_def]
  have hn (n : ℕ) : SchauderSum.normVector y n = (‖y n‖ : 𝕜) :=
    SchauderSum.coord_normVector y n
  apply le_antisymm
  · simpa only [one_mul] using lp_norm_le_mul_of_pointwise
      (SchauderSum.normVector y) (lpSchauderSumValue p hp hlp y) zero_le_one
      (fun n => by simp [hn])
  · simpa only [one_mul] using lp_norm_le_mul_of_pointwise
      (lpSchauderSumValue p hp hlp y) (SchauderSum.normVector y) zero_le_one
      (fun n => by simp [hn])

/-- The coordinate-preserving linear isometry from the ℓp basis sum to the
actual vector-valued ℓp space. -/
def lpSchauderSumEquiv :
    SchauderSum (scalarLpSchauderBasis p hp) hlp Y ≃ₗᵢ[𝕜] lp (fun _ : ℕ => Y) p where
  toFun := lpSchauderSumValue p hp hlp
  invFun y := ⟨y, (memSchauderSum_lp_iff p hp y).mpr y.property⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  norm_map' := lpSchauderSumValue_norm p hp hlp

@[simp] theorem lpSchauderSumEquiv_apply
    (y : SchauderSum (scalarLpSchauderBasis p hp) hlp Y) (n : ℕ) :
    lpSchauderSumEquiv (Y := Y) p hp hlp y n = y n := rfl

@[simp] theorem lpSchauderSumEquiv_symm_apply (y : lp (fun _ : ℕ => Y) p) (n : ℕ) :
    (lpSchauderSumEquiv (Y := Y) p hp hlp).symm y n = y n := rfl

end ThesisCommon
