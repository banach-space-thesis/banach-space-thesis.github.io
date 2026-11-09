import SurveyStatements.P4DFJPGauge
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# The individual Banach norms in the DFJP interpolation construction

Each coordinate is the ambient vector space equipped with its actual
Minkowski-functional norm. The explicit norm comparison constructs a bounded
linear equivalence with the original space and transports completeness.
-/

noncomputable section

set_option autoImplicit false

open Set Metric

namespace SurveyStatements.P4

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- Elementary data for the gauge norms. These are properties of the generating
set, rather than an assumed interpolation or factorization conclusion. -/
structure DFJPGaugeData (𝕜 : Type u) [RCLike 𝕜] (E : Type v)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] where
  carrier : Set E
  absConvex : AbsConvex 𝕜 carrier
  zero_mem : (0 : E) ∈ carrier
  normBound : ℝ
  normBound_nonneg : 0 ≤ normBound
  norm_le : carrier ⊆ closedBall (0 : E) normBound

/-- A copy of the original vector space, carrying the `j`th gauge norm. -/
def DFJPScale (D : DFJPGaugeData 𝕜 E) (j : ℤ) : Type v := E

namespace DFJPScale

variable (D : DFJPGaugeData 𝕜 E) (j : ℤ)

instance : AddCommGroup (DFJPScale D j) := inferInstanceAs (AddCommGroup E)

instance : Module 𝕜 (DFJPScale D j) := inferInstanceAs (Module 𝕜 E)

instance : Norm (DFJPScale D j) := ⟨fun x => dfjpGauge (E := E) D.carrier j x⟩

lemma normedCore : NormedSpace.Core 𝕜 (DFJPScale D j) where
  norm_nonneg x := dfjpGauge_nonneg (E := E) D.carrier j x
  norm_smul c x :=
    map_smul_eq_mul (dfjpGaugeSeminorm (E := E) D.absConvex D.zero_mem j) c x
  norm_triangle x y :=
    map_add_le_add (dfjpGaugeSeminorm (E := E) D.absConvex D.zero_mem j) x y
  norm_eq_zero_iff x :=
    dfjpGauge_eq_zero_iff (E := E) D.zero_mem D.normBound_nonneg D.norm_le j x

instance : NormedAddCommGroup (DFJPScale D j) :=
  NormedAddCommGroup.ofCore (normedCore D j)

instance : NormedSpace 𝕜 (DFJPScale D j) := NormedSpace.ofCore (normedCore D j)

@[simp] lemma norm_eq_gauge (x : DFJPScale D j) :
    ‖x‖ = dfjpGauge (E := E) D.carrier j x := rfl

/-- The identity on vectors, before adding its norm bounds. -/
def linearEquiv : DFJPScale D j ≃ₗ[𝕜] E where
  toFun := id
  invFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

lemma ambient_norm_le (x : DFJPScale D j) :
    ‖(linearEquiv D j) x‖ ≤
      ((2 : ℝ) ^ j * D.normBound + (2 : ℝ) ^ (-j)) * ‖x‖ := by
  have h := norm_div_le_dfjpGauge D.zero_mem D.normBound_nonneg D.norm_le j x
  have hr : 0 < (2 : ℝ) ^ j * D.normBound + (2 : ℝ) ^ (-j) := by
    have := D.normBound_nonneg
    positivity
  simpa [linearEquiv, norm_eq_gauge, mul_comm] using (div_le_iff₀ hr).mp h

lemma gauge_norm_le (x : E) :
    ‖(linearEquiv D j).symm x‖ ≤ ((2 : ℝ) ^ (-j))⁻¹ * ‖x‖ := by
  simpa [linearEquiv, norm_eq_gauge, div_eq_inv_mul] using dfjpGauge_le_norm D.zero_mem j x

/-- Each gauge norm is equivalent to the original Banach norm, with explicit
positive comparison constants. -/
def continuousLinearEquiv : DFJPScale D j ≃L[𝕜] E :=
  (linearEquiv D j).toContinuousLinearEquivOfBounds
    ((2 : ℝ) ^ j * D.normBound + (2 : ℝ) ^ (-j))
    (((2 : ℝ) ^ (-j))⁻¹) (ambient_norm_le D j) (gauge_norm_le D j)

instance [CompleteSpace E] : CompleteSpace (DFJPScale D j) :=
  ((continuousLinearEquiv D j).isUniformEmbedding.isUniformInducing.completeSpace_congr
    (continuousLinearEquiv D j).surjective).mpr inferInstance

end DFJPScale

end SurveyStatements.P4
