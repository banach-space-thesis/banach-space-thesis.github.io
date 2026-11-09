import SurveyStatements.P4DFJPRenorm
import SurveyStatements.P4DFJPDecay
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The actual DFJP space as a closed diagonal of the square-summable sum

This construction supplies its vector-space structure, exact squared norm,
completeness, and bounded injective inclusion. Reflexivity is a separate
remaining theorem; no reflexivity assertion is assumed by this construction.
-/

noncomputable section

set_option autoImplicit false

open Set Metric
open scoped ENNReal

namespace SurveyStatements.P4

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The square-summable sum of the individual gauge-renormed spaces. -/
abbrev DFJPSum (D : DFJPGaugeData 𝕜 E) := lp (DFJPScale D) 2

namespace DFJPSum

variable (D : DFJPGaugeData 𝕜 E)

/-- Coordinate evaluation as an actual bounded linear map. -/
def eval (j : ℤ) : DFJPSum D →L[𝕜] DFJPScale D j :=
  ({ toFun := fun f => f j
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : DFJPSum D →ₗ[𝕜] DFJPScale D j).mkContinuous 1
     (fun f => by simpa using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) f j)

/-- Coordinate evaluation into the original space. -/
def ambientEval (j : ℤ) : DFJPSum D →L[𝕜] E :=
  (DFJPScale.continuousLinearEquiv D j).toContinuousLinearMap.comp (eval D j)

@[simp] lemma ambientEval_apply (j : ℤ) (f : DFJPSum D) :
    ambientEval D j f = (DFJPScale.linearEquiv D j) (f j) := rfl

end DFJPSum

/-- All coordinates represent the same vector in the original ambient space. -/
def dfjpDiagonal (D : DFJPGaugeData 𝕜 E) : Submodule 𝕜 (DFJPSum D) where
  carrier := { f | ∀ j : ℤ, DFJPSum.ambientEval D j f = DFJPSum.ambientEval D 0 f }
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j
    simp only [ContinuousLinearMap.map_add, hx j, hy j]
  smul_mem' := by
    intro a x hx j
    simp only [ContinuousLinearMap.map_smul, hx j]

lemma isClosed_dfjpDiagonal (D : DFJPGaugeData 𝕜 E) :
    IsClosed ((dfjpDiagonal D : Submodule 𝕜 (DFJPSum D)) : Set (DFJPSum D)) := by
  change IsClosed {f : DFJPSum D | ∀ j : ℤ,
    DFJPSum.ambientEval D j f = DFJPSum.ambientEval D 0 f}
  simp only [setOf_forall]
  exact isClosed_iInter fun j => isClosed_eq
    (DFJPSum.ambientEval D j).continuous (DFJPSum.ambientEval D 0).continuous

/-- The closed diagonal is the DFJP interpolation space. -/
abbrev DFJPSpace (D : DFJPGaugeData 𝕜 E) := dfjpDiagonal D

/-- The diagonal carries the inherited scalar norm law directly. Registering
this instance avoids repeatedly reconstructing the nested subtype/lp instances
when elaborating its strong dual and bidual. -/
instance (priority := 1100) (D : DFJPGaugeData 𝕜 E) : NormedSpace 𝕜 (DFJPSpace D) where
  norm_smul_le c f := norm_smul_le c f.val

instance (D : DFJPGaugeData 𝕜 E) [CompleteSpace E] : CompleteSpace (DFJPSpace D) :=
  (isClosed_dfjpDiagonal D).completeSpace_coe

namespace DFJPSpace

variable (D : DFJPGaugeData 𝕜 E)

/-- Its bounded inclusion into the original space, realized by the zeroth coordinate. -/
def inclusion : DFJPSpace D →L[𝕜] E :=
  (DFJPSum.ambientEval D 0).comp (dfjpDiagonal D).subtypeL

lemma coordinate_eq (f : DFJPSpace D) (j : ℤ) :
    (DFJPScale.linearEquiv D j) (f.val j) = inclusion D f := f.property j

lemma inclusion_injective : Function.Injective (inclusion D) := by
  intro f g h
  apply Subtype.ext
  ext j
  apply (DFJPScale.linearEquiv D j).injective
  rw [coordinate_eq, coordinate_eq, h]

lemma ambient_norm_le (f : DFJPSpace D) :
    ‖inclusion D f‖ ≤ (D.normBound + 1) * ‖f‖ := by
  have hc := DFJPScale.ambient_norm_le D 0 (f.val 0)
  have he := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) f.val 0
  have hpos : 0 ≤ D.normBound + 1 := by have := D.normBound_nonneg; positivity
  change ‖(DFJPScale.linearEquiv D 0) (f.val 0)‖ ≤ (D.normBound + 1) * ‖f.val‖
  calc
    ‖(DFJPScale.linearEquiv D 0) (f.val 0)‖ ≤
        (D.normBound + 1) * ‖f.val 0‖ := by simpa using hc
    _ ≤ (D.normBound + 1) * ‖f.val‖ := mul_le_mul_of_nonneg_left he hpos

lemma norm_sq (f : DFJPSpace D) :
    ‖f‖ ^ 2 = ∑' j : ℤ, (dfjpGauge D.carrier j (inclusion D f)) ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f.val
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  change ‖f.val‖ ^ 2 = _
  rw [h]
  apply tsum_congr
  intro j
  rw [DFJPScale.norm_eq_gauge]
  change (dfjpGauge D.carrier j ((DFJPScale.linearEquiv D j) (f.val j))) ^ 2 = _
  rw [coordinate_eq]

/-- Construct an element of the closed diagonal from precisely the paper's
square-summability condition. -/
def ofSummable (x : E) (hx : Summable (fun j : ℤ => (dfjpGauge D.carrier j x) ^ 2)) :
    DFJPSpace D := by
  let f : ∀ j : ℤ, DFJPScale D j := fun j => (DFJPScale.linearEquiv D j).symm x
  have hf : Memℓp f 2 := memℓp_gen (by
    simpa [f, DFJPScale.linearEquiv, DFJPScale.norm_eq_gauge, Real.rpow_two] using hx)
  refine ⟨⟨f, hf⟩, ?_⟩
  intro j
  simp [DFJPSum.ambientEval_apply, f]

@[simp] lemma inclusion_ofSummable (x : E)
    (hx : Summable (fun j : ℤ => (dfjpGauge D.carrier j x) ^ 2)) :
    inclusion D (ofSummable D x hx) = x := rfl

/-- Every vector of the generating set belongs to the interpolation space. -/
def ofMem {x : E} (hx : x ∈ D.carrier) : DFJPSpace D :=
  ofSummable D x (summable_dfjpGauge_sq_of_mem D.zero_mem hx)

@[simp] lemma inclusion_ofMem {x : E} (hx : x ∈ D.carrier) :
    inclusion D (ofMem D hx) = x := rfl

end DFJPSpace

end SurveyStatements.P4
