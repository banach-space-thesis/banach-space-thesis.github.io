import PL1.TailSpikes
import PL1.L1Multiplication
import PL1.IntrinsicGraph

/-! # Exact averages of actual intrinsic tail products -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace PL1.IntrinsicSpikeAverages
open Walsh Noise IntrinsicGraph L1Multiplication

variable (K : Type*) [RCLike K]

theorem multiplier_real_smul (c : ℝ) (q : C(Walsh.Group, ℝ)) :
    multiplier K (c • q) = c • multiplier K q := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [coeFn_multiplier K (c • q) f, coeFn_multiplier K q f,
    Lp.coeFn_smul c (multiplier K q f)] with x hprod hq hsm
  change (multiplier K (c • q) f) x = (c • multiplier K q f) x
  rw [hprod, hsm]
  simp only [Pi.smul_apply]
  rw [hq]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, smul_smul]

def multiplierRealLinear : C(Walsh.Group, ℝ) →ₗ[ℝ]
    (Lp K 1 haar →L[K] Lp K 1 haar) where
  toFun := multiplier K
  map_add' := multiplier_add K
  map_smul' := multiplier_real_smul K

theorem average_multipliers {rates : ℕ → ℝ≥0} {d : ℕ} {T : PositiveTime} {δ : ℝ}
    (Q : TailSpikes.RateFamily rates d T δ) :
    (Fintype.card (FiniteCoordinateKernels.Assignments Q.coordinates) : ℝ)⁻¹ •
        ∑ a, multiplier K (Q.q a) = ContinuousLinearMap.id K (Lp K 1 haar) := by
  have hq : (Fintype.card (FiniteCoordinateKernels.Assignments Q.coordinates) : ℝ)⁻¹ •
      ∑ a, Q.q a = (1 : C(Walsh.Group, ℝ)) := by
    ext x
    simpa only [ContinuousMap.smul_apply, ContinuousMap.sum_apply,
      ContinuousMap.one_apply, smul_eq_mul] using Q.average_one x
  have h := congrArg (multiplierRealLinear K) hq
  simpa only [map_smul, map_sum, multiplierRealLinear, LinearMap.coe_mk,
    AddHom.coe_mk, multiplier_one] using h

theorem average_products {rates : ℕ → ℝ≥0} {d : ℕ} {T : PositiveTime} {δ : ℝ}
    (Q : TailSpikes.RateFamily rates d T δ)
    (D : ℕ → Lp K 1 haar →L[K] Lp K 1 haar) (f : Space D)
    (g : FiniteCoordinateKernels.Assignments Q.coordinates → Space D)
    (hg : ∀ a, evalZero D (g a) = multiplier K (Q.q a) (evalZero D f)) :
    (Fintype.card (FiniteCoordinateKernels.Assignments Q.coordinates) : ℝ)⁻¹ •
      ∑ a, g a = f := by
  apply evalZero_injective D
  let R := (evalZero D).restrictScalars ℝ
  change R (_ • ∑ a, g a) = R f
  rw [map_smul, map_sum]
  change _ • ∑ a, evalZero D (g a) = evalZero D f
  simp_rw [hg]
  have h := DFunLike.congr_fun (average_multipliers K Q) (evalZero D f)
  simpa only [smul_apply, sum_apply, ContinuousLinearMap.id_apply] using h

end PL1.IntrinsicSpikeAverages
