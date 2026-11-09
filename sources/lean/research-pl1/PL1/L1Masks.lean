import PL1.Definitions
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Contractive measurable-set masks on actual scalar L1 spaces -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace PL1.L1Masks

variable {𝕜 Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω]
variable (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)

def maskFun (f : Lp 𝕜 1 μ) : Lp 𝕜 1 μ :=
  ((L1.integrable_coeFn f).indicator hA).toL1 (A.indicator f)

theorem coeFn_maskFun (f : Lp 𝕜 1 μ) : maskFun μ A hA f =ᵐ[μ] A.indicator f :=
  ((L1.integrable_coeFn f).indicator hA).coeFn_toL1

theorem maskFun_add (f g : Lp 𝕜 1 μ) :
    maskFun μ A hA (f + g) = maskFun μ A hA f + maskFun μ A hA g := by
  apply Lp.ext
  filter_upwards [coeFn_maskFun μ A hA (f + g), coeFn_maskFun μ A hA f,
    coeFn_maskFun μ A hA g, Lp.coeFn_add f g,
    Lp.coeFn_add (maskFun μ A hA f) (maskFun μ A hA g)] with x hfg hf hg ha hb
  have ha' : (f + g) x = f x + g x := ha
  have hb' : (maskFun μ A hA f + maskFun μ A hA g) x =
      maskFun μ A hA f x + maskFun μ A hA g x := hb
  rw [hfg, hb', hf, hg]
  by_cases hx : x ∈ A
  · simp only [Set.indicator_of_mem hx]
    exact ha'
  · simp only [Set.indicator_of_notMem hx, zero_add]

theorem maskFun_smul (c : 𝕜) (f : Lp 𝕜 1 μ) :
    maskFun μ A hA (c • f) = c • maskFun μ A hA f := by
  apply Lp.ext
  filter_upwards [coeFn_maskFun μ A hA (c • f), coeFn_maskFun μ A hA f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (maskFun μ A hA f)] with x hcf hf ha hb
  have ha' : (c • f) x = c • f x := ha
  have hb' : (c • maskFun μ A hA f) x = c • maskFun μ A hA f x := hb
  rw [hcf, hb', hf]
  by_cases hx : x ∈ A
  · simp only [Set.indicator_of_mem hx]
    exact ha'
  · simp only [Set.indicator_of_notMem hx, smul_zero]

theorem norm_maskFun (f : Lp 𝕜 1 μ) : ‖maskFun μ A hA f‖ = ∫ x in A, ‖f x‖ ∂μ := by
  rw [maskFun, L1.norm_of_fun_eq_integral_norm]
  simp_rw [norm_indicator_eq_indicator_norm]
  exact integral_indicator hA

theorem norm_maskFun_le (f : Lp 𝕜 1 μ) : ‖maskFun μ A hA f‖ ≤ ‖f‖ := by
  rw [norm_maskFun, L1.norm_eq_integral_norm]
  exact setIntegral_le_integral (L1.integrable_coeFn f).norm
    (ae_of_all _ (fun x => norm_nonneg _))

/-- Multiplication by a measurable-set indicator, on L1 equivalence classes. -/
def mask : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ :=
  LinearMap.mkContinuous
    { toFun := maskFun μ A hA
      map_add' := maskFun_add μ A hA
      map_smul' := maskFun_smul μ A hA }
    1 (fun f => by
      change ‖maskFun μ A hA f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_maskFun_le μ A hA f)

theorem coeFn_mask (f : Lp 𝕜 1 μ) : mask μ A hA f =ᵐ[μ] A.indicator f :=
  coeFn_maskFun μ A hA f

theorem norm_mask (f : Lp 𝕜 1 μ) : ‖mask μ A hA f‖ = ∫ x in A, ‖f x‖ ∂μ :=
  norm_maskFun μ A hA f

theorem norm_mask_le_one : ‖mask (𝕜 := 𝕜) μ A hA‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun f => by
      change ‖maskFun μ A hA f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_maskFun_le μ A hA f)

/-- Disjoint masks divide, rather than duplicate, the L1 norm. -/
theorem sum_norm_mask_le {ι : Type*} (s : Finset ι) (sets : ι → Set Ω)
    (hsets : ∀ i, MeasurableSet (sets i))
    (hdisj : Pairwise (fun i j => Disjoint (sets i) (sets j))) (f : Lp 𝕜 1 μ) :
    (∑ i ∈ s, ‖mask μ (sets i) (hsets i) f‖) ≤ ‖f‖ := by
  simp only [norm_mask]
  rw [← integral_biUnion_finset s (fun i _ => hsets i)
    (fun i _ j _ hij => hdisj hij) (fun i _ => (L1.integrable_coeFn f).norm.integrableOn)]
  rw [L1.norm_eq_integral_norm]
  exact setIntegral_le_integral (L1.integrable_coeFn f).norm
    (ae_of_all _ (fun x => norm_nonneg _))

end PL1.L1Masks
