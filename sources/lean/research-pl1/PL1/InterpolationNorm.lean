import PL1.MainInterpolation
import PL1.KFunctionalNormLaws
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# The actual real-interpolation integral as a complete Banach norm

`Space` is a dedicated type alias with the standard integral norm. The
original intrinsic norm and all its geometric theorems keep their original
instances. The identity is a continuous linear equivalence in both directions.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace PL1.InterpolationNorm
open Noise Walsh IntrinsicGraph ResolventEstimates

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

/-- The finite, actual interpolation integral evaluated on an intrinsic vector. -/
def value (x : (dyadicSystem K rates).IntrinsicSpace) : ℝ :=
  Interpolation.normValue K rates (evalZero (dyadicSystem K rates).analysis x)

theorem value_eq (x : (dyadicSystem K rates).IntrinsicSpace) :
    value K rates x =
      (KFunctional.continuousNorm K rates (evalZero (dyadicSystem K rates).analysis x)).toReal := by
  rw [value, Interpolation.normValue, Interpolation.normIntegral_eq]

theorem continuousNorm_eval_ne_top (x : (dyadicSystem K rates).IntrinsicSpace) :
    KFunctional.continuousNorm K rates (evalZero (dyadicSystem K rates).analysis x) ≠ ⊤ := by
  rw [← Interpolation.normIntegral_eq]
  exact Interpolation.normIntegral_eval_ne_top K rates x

theorem value_nonneg (x : (dyadicSystem K rates).IntrinsicSpace) : 0 ≤ value K rates x :=
  ENNReal.toReal_nonneg

theorem value_zero : value K rates 0 = 0 := by
  rw [value_eq, map_zero, KFunctional.continuousNorm_zero, ENNReal.toReal_zero]

theorem value_smul (a : K) (x : (dyadicSystem K rates).IntrinsicSpace) :
    value K rates (a • x) = ‖a‖ * value K rates x := by
  simp only [value_eq, map_smul, KFunctional.continuousNorm_smul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg a)]

theorem value_add_le (x y : (dyadicSystem K rates).IntrinsicSpace) :
    value K rates (x+y) ≤ value K rates x + value K rates y := by
  have hx := continuousNorm_eval_ne_top K rates x
  have hy := continuousNorm_eval_ne_top K rates y
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hx, hy⟩)
    (KFunctional.continuousNorm_add_le K rates
      (evalZero (dyadicSystem K rates).analysis x) (evalZero (dyadicSystem K rates).analysis y))
  simpa only [value_eq, map_add, ENNReal.toReal_add hx hy] using h

theorem value_lower (x : (dyadicSystem K rates).IntrinsicSpace) :
    (1/10 : ℝ) * ‖x‖ ≤ value K rates x := Interpolation.normValue_lower K rates x

theorem value_upper (x : (dyadicSystem K rates).IntrinsicSpace) :
    value K rates x ≤ (4 * (2 + dyadicRatio / (1-dyadicRatio))) * ‖x‖ :=
  Interpolation.normValue_upper K rates x

theorem eq_zero_of_value_eq_zero (x : (dyadicSystem K rates).IntrinsicSpace)
    (hx : value K rates x = 0) : x = 0 := by
  have h := value_lower K rates x
  apply norm_eq_zero.mp
  have hn := norm_nonneg x
  rw [hx] at h
  linarith

/-- A separating seminorm on the original intrinsic space. -/
def seminorm : Seminorm K (dyadicSystem K rates).IntrinsicSpace :=
  Seminorm.of (value K rates) (value_add_le K rates) (value_smul K rates)

/-- A dedicated copy carrying the standard interpolation integral norm. -/
def Space : Type _ := (dyadicSystem K rates).IntrinsicSpace

instance : AddCommGroup (Space K rates) :=
  inferInstanceAs (AddCommGroup (dyadicSystem K rates).IntrinsicSpace)

instance : Module K (Space K rates) :=
  inferInstanceAs (Module K (dyadicSystem K rates).IntrinsicSpace)

/-- Identity on vectors, before supplying the new norm. -/
def linearEquiv : Space K rates ≃ₗ[K] (dyadicSystem K rates).IntrinsicSpace :=
  LinearEquiv.refl K (dyadicSystem K rates).IntrinsicSpace

def groupNorm : AddGroupNorm (Space K rates) :=
  { (seminorm K rates).toAddGroupSeminorm with
    eq_zero_of_map_eq_zero' := eq_zero_of_value_eq_zero K rates }

instance : NormedAddCommGroup (Space K rates) :=
  (groupNorm K rates).toNormedAddCommGroup

theorem norm_eq (x : Space K rates) : ‖x‖ = value K rates (linearEquiv K rates x) := rfl

instance : NormedSpace K (Space K rates) where
  norm_smul_le a x := by
    rw [norm_eq, norm_eq, map_smul]
    exact (value_smul K rates a (linearEquiv K rates x)).le

/-- The original and standard integral norms give the same Banach topology. -/
def continuousLinearEquiv : Space K rates ≃L[K] (dyadicSystem K rates).IntrinsicSpace :=
  (linearEquiv K rates).toContinuousLinearEquivOfBounds
    10 (4 * (2 + dyadicRatio / (1-dyadicRatio)))
    (fun x => by
      rw [norm_eq]
      have h := value_lower K rates (linearEquiv K rates x)
      linarith)
    (fun x => by
      rw [norm_eq, LinearEquiv.apply_symm_apply]
      exact value_upper K rates x)

instance : CompleteSpace (Space K rates) := by
  apply (completeSpace_iff_isComplete_range
    (continuousLinearEquiv K rates).isUniformEmbedding.isUniformInducing).mpr
  rw [(continuousLinearEquiv K rates).surjective.range_eq]
  exact isComplete_univ

/-- Equality with the standard integral over the genuine generator-domain norm. -/
theorem norm_eq_integral (x : Space K rates) :
    ‖x‖ = (Interpolation.normIntegral K rates
      (evalZero (dyadicSystem K rates).analysis (continuousLinearEquiv K rates x))).toReal := rfl

/-- The underlying Haar function is unchanged by the Banach-space identification. -/
def inclusion : Space K rates →L[K] Lp K 1 haar :=
  (evalZero (dyadicSystem K rates).analysis).comp
    (continuousLinearEquiv K rates).toContinuousLinearMap

theorem inclusion_injective : Function.Injective (inclusion K rates) :=
  (evalZero_injective (dyadicSystem K rates).analysis).comp
    (continuousLinearEquiv K rates).injective

end PL1.InterpolationNorm
