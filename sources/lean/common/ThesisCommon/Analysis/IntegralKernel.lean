import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

/-! Genuine integral kernels on L¹, used in PEMS Definitions 3.11/3.13 and
the standard-measure-space proof. No representation theorem is assumed.
The scalar-uniform definition is the ordinary Bochner integral formula;
for real scalars it is exactly the paper's displayed Definition 3.11. -/
noncomputable section
open MeasureTheory Filter Set
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

/-- The kernel relation for an existing bounded L¹ operator. Section
integrability is stated separately so the default value of a nonintegrable
Bochner integral cannot make the representation predicate hold spuriously. -/
structure IsIntegralKernel (k : X × Y → 𝕜) (K : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν) : Prop where
  measurable : Measurable k
  integrable_section : ∀ f : Lp 𝕜 1 μ, ∀ᵐ y ∂ν,
    Integrable (fun x => k (x, y) * f x) μ
  represents : ∀ f : Lp 𝕜 1 μ, K f =ᵐ[ν] fun y => ∫ x, k (x, y) * f x ∂μ

def IsIntegralOperator (K : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν) : Prop :=
  ∃ k : X × Y → 𝕜, IsIntegralKernel k K

/-- A specified kernel determines at most one bounded operator. -/
theorem IsIntegralKernel.unique {k : X × Y → 𝕜}
    {K L : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν}
    (hK : IsIntegralKernel k K) (hL : IsIntegralKernel k L) : K = L := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (hK.represents f).trans (hL.represents f).symm

/-- The paper's large-value truncation, retaining equality at the threshold. -/
def truncatedKernel (r : ℝ) (k : X × Y → 𝕜) : X × Y → 𝕜 :=
  {z | r ≤ ‖k z‖}.indicator k

theorem measurable_truncatedKernel {k : X × Y → 𝕜} (hk : Measurable k) (r : ℝ) :
    Measurable (truncatedKernel r k) :=
  hk.indicator (measurableSet_le measurable_const hk.norm)

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem norm_truncatedKernel_le (r : ℝ) (k : X × Y → 𝕜) (z : X × Y) :
    ‖truncatedKernel r k z‖ ≤ ‖k z‖ := by
  by_cases h : r ≤ ‖k z‖ <;> simp [truncatedKernel, h]

theorem integrable_truncatedKernel {k : X × Y → 𝕜} (hk : Measurable k)
    (hki : Integrable k (μ.prod ν)) (r : ℝ) :
    Integrable (truncatedKernel r k) (μ.prod ν) :=
  hki.indicator (measurableSet_le measurable_const hk.norm)

/-- Actual section integration, before passage to the L¹ equivalence class. -/
def kernelApply (k : X × Y → 𝕜) (f : Lp 𝕜 1 μ) (y : Y) : 𝕜 :=
  ∫ x, k (x, y) * f x ∂μ

section Construction
variable [SFinite μ] [SFinite ν]
variable {k : X × Y → 𝕜} (hk : Measurable k) {C : ℝ}

/-- The analytic input for constructing a bounded integral operator:
integrable columns with a uniform a.e. bound on their L¹ norms. -/
def HasKernelBound (μ : Measure X) (ν : Measure Y) (k : X × Y → 𝕜) (C : ℝ) : Prop :=
  ∀ᵐ x ∂μ, Integrable (fun y => k (x, y)) ν ∧ (∫ y, ‖k (x, y)‖ ∂ν) ≤ C

include hk

omit [SFinite μ] in
/-- Fubini integrability of the weighted kernel follows from the column bound,
not from an assumed bounded operator or an assumed representation. -/
theorem integrable_kernel_mul (hbound : HasKernelBound μ ν k C) (f : Lp 𝕜 1 μ) :
    Integrable (fun z : X × Y => k z * f z.1) (μ.prod ν) := by
  have hm : StronglyMeasurable (fun z : X × Y => k z * f z.1) :=
    hk.stronglyMeasurable.mul ((Lp.stronglyMeasurable f).comp_measurable measurable_fst)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hbound] with x hx
    exact hx.1.mul_const (f x)
  · apply ((L1.integrable_coeFn f).norm.const_mul C).mono'
      hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [norm_mul]
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right hx.2 (norm_nonneg _)

theorem integrable_kernelApply (hbound : HasKernelBound μ ν k C) (f : Lp 𝕜 1 μ) :
    Integrable (kernelApply k f) ν := (integrable_kernel_mul hk hbound f).integral_prod_right

def kernelApplyL1 (hbound : HasKernelBound μ ν k C) (f : Lp 𝕜 1 μ) : Lp 𝕜 1 ν :=
  (integrable_kernelApply hk hbound f).toL1 (kernelApply k f)

theorem kernelApplyL1_coe (hbound : HasKernelBound μ ν k C) (f : Lp 𝕜 1 μ) :
    kernelApplyL1 hk hbound f =ᵐ[ν] kernelApply k f := Integrable.coeFn_toL1 _

/-- The quantitative L¹ estimate is proved by Fubini and the column bound. -/
theorem norm_kernelApplyL1_le (hbound : HasKernelBound μ ν k C) (f : Lp 𝕜 1 μ) :
    ‖kernelApplyL1 hk hbound f‖ ≤ C * ‖f‖ := by
  have hprod := integrable_kernel_mul hk hbound f
  rw [kernelApplyL1, L1.norm_of_fun_eq_integral_norm]
  calc
    (∫ y, ‖kernelApply k f y‖ ∂ν) ≤ ∫ y, ∫ x, ‖k (x, y) * f x‖ ∂μ ∂ν :=
      integral_mono (integrable_kernelApply hk hbound f).norm hprod.norm.integral_prod_right
        (fun y => norm_integral_le_integral_norm _)
    _ = ∫ x, ∫ y, ‖k (x, y) * f x‖ ∂ν ∂μ := (integral_integral_swap hprod.norm).symm
    _ ≤ ∫ x, C * ‖f x‖ ∂μ := by
      apply integral_mono_ae hprod.norm.integral_prod_left ((L1.integrable_coeFn f).norm.const_mul C)
      filter_upwards [hbound] with x hx
      simp only [norm_mul]
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right hx.2 (norm_nonneg _)
    _ = C * ‖f‖ := by rw [integral_const_mul, ← L1.norm_eq_integral_norm]

theorem kernelApplyL1_add (hbound : HasKernelBound μ ν k C) (f g : Lp 𝕜 1 μ) :
    kernelApplyL1 hk hbound (f + g) = kernelApplyL1 hk hbound f + kernelApplyL1 hk hbound g := by
  apply Lp.ext
  filter_upwards [kernelApplyL1_coe hk hbound (f + g), kernelApplyL1_coe hk hbound f,
    kernelApplyL1_coe hk hbound g,
    Lp.coeFn_add (kernelApplyL1 hk hbound f) (kernelApplyL1 hk hbound g),
    (integrable_kernel_mul hk hbound f).prod_left_ae,
    (integrable_kernel_mul hk hbound g).prod_left_ae] with y hfg hf hg hadd hfi hgi
  simp only [Pi.add_apply] at hadd
  rw [hfg, hadd, hf, hg]
  dsimp [kernelApply]
  calc
    (∫ x, k (x, y) * (f + g) x ∂μ) =
        ∫ x, k (x, y) * f x + k (x, y) * g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add f g] with x hx
      simp only [hx, Pi.add_apply, mul_add]
    _ = (∫ x, k (x, y) * f x ∂μ) + ∫ x, k (x, y) * g x ∂μ := integral_add hfi hgi

theorem kernelApplyL1_smul (hbound : HasKernelBound μ ν k C) (a : 𝕜) (f : Lp 𝕜 1 μ) :
    kernelApplyL1 hk hbound (a • f) = a • kernelApplyL1 hk hbound f := by
  apply Lp.ext
  filter_upwards [kernelApplyL1_coe hk hbound (a • f), kernelApplyL1_coe hk hbound f,
    Lp.coeFn_smul a (kernelApplyL1 hk hbound f)] with y haf hf hs
  simp only [Pi.smul_apply] at hs
  rw [haf, hs, hf]
  dsimp [kernelApply]
  calc
    (∫ x, k (x, y) * (a • f) x ∂μ) = ∫ x, a * (k (x, y) * f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul a f] with x hx
      simp only [hx, Pi.smul_apply, smul_eq_mul]
      ring
    _ = a • ∫ x, k (x, y) * f x ∂μ := by rw [integral_const_mul, smul_eq_mul]

/-- The bounded integral operator constructed from the actual kernel and its
column estimate. This is a construction, not an assumed representation. -/
def integralKernelOperator (hbound : HasKernelBound μ ν k C) : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν :=
  LinearMap.mkContinuous
    { toFun := kernelApplyL1 hk hbound
      map_add' := kernelApplyL1_add hk hbound
      map_smul' := kernelApplyL1_smul hk hbound }
    C (norm_kernelApplyL1_le hk hbound)

theorem norm_integralKernelOperator_le (hbound : HasKernelBound μ ν k C) (hC : 0 ≤ C) :
    ‖integralKernelOperator hk hbound‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_kernelApplyL1_le hk hbound)

theorem isIntegralKernel_integralKernelOperator (hbound : HasKernelBound μ ν k C) :
    IsIntegralKernel k (integralKernelOperator hk hbound) := by
  refine ⟨hk, ?_, kernelApplyL1_coe hk hbound⟩
  intro f
  exact (integrable_kernel_mul hk hbound f).prod_left_ae

end Construction
end ThesisCommon
