import ThesisCommon.Analysis.LpCoordinateUltralimit
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! A bounded family of operators can be evaluated simultaneously; composing
with coordinate ultralimits produces an actual bounded operator. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
variable {𝕜 ι E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def boundedOperatorApply (A : lp (fun _ : ι => E →L[𝕜] F) ∞) :
    E →L[𝕜] lp (fun _ : ι => F) ∞ :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => A i x, memℓp_infty ⟨‖A‖ * ‖x‖, by
        rintro _ ⟨i,rfl⟩
        exact ((A i).le_opNorm x).trans (mul_le_mul_of_nonneg_right
          (lp.norm_apply_le_norm ENNReal.top_ne_zero A i) (norm_nonneg x))⟩⟩
      map_add' := fun x y => by apply lp.ext; funext i; exact map_add (A i) x y
      map_smul' := fun c x => by apply lp.ext; funext i; exact map_smul (A i) c x }
    ‖A‖ (fun x => lp.norm_le_of_forall_le (mul_nonneg (norm_nonneg A) (norm_nonneg x))
      (fun i => ((A i).le_opNorm x).trans (mul_le_mul_of_nonneg_right
        (lp.norm_apply_le_norm ENNReal.top_ne_zero A i) (norm_nonneg x))))

@[simp] theorem boundedOperatorApply_apply (A : lp (fun _ : ι => E →L[𝕜] F) ∞)
    (x : E) (i : ι) : boundedOperatorApply A x i = A i x := rfl

theorem norm_boundedOperatorApply_le (A : lp (fun _ : ι => E →L[𝕜] F) ∞) :
    ‖boundedOperatorApply A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

def boundedOperatorApplyL :
    lp (fun _ : ι => E →L[𝕜] F) ∞ →L[𝕜] (E →L[𝕜] lp (fun _ : ι => F) ∞) :=
  LinearMap.mkContinuous
    { toFun := boundedOperatorApply
      map_add' := fun A B => by
        apply ContinuousLinearMap.ext; intro x
        apply lp.ext; funext i; rfl
      map_smul' := fun c A => by
        apply ContinuousLinearMap.ext; intro x
        apply lp.ext; funext i; rfl }
    1 (fun A => by simpa only [one_mul] using norm_boundedOperatorApply_le A)

variable {κ : Type*}

def lpOperatorUltralimit (p : BanachExponent) (hp : 0 < p.val.toReal) (U : Ultrafilter ι) :
    lp (fun _ : ι => E →L[𝕜] lp (fun _ : κ => 𝕜) p.val) ∞ →L[𝕜]
      (E →L[𝕜] lp (fun _ : κ => 𝕜) p.val) :=
  (ContinuousLinearMap.compL 𝕜 E
    (lp (fun _ : ι => lp (fun _ : κ => 𝕜) p.val) ∞)
    (lp (fun _ : κ => 𝕜) p.val) (lpCoordinateUltralimit p hp U)).comp boundedOperatorApplyL

theorem lpOperatorUltralimit_apply (p : BanachExponent) (hp : 0 < p.val.toReal)
    (U : Ultrafilter ι) (A : lp (fun _ : ι => E →L[𝕜] lp (fun _ : κ => 𝕜) p.val) ∞) (x : E) :
    lpOperatorUltralimit p hp U A x = lpCoordinateUltralimit p hp U (boundedOperatorApply A x) := rfl

theorem lpOperatorUltralimit_apply_operator (p : BanachExponent) (hp : 0 < p.val.toReal)
    (U : Ultrafilter ι) (A : lp (fun _ : ι => E →L[𝕜] lp (fun _ : κ => 𝕜) p.val) ∞) :
    lpOperatorUltralimit p hp U A =
      (lpCoordinateUltralimit (𝕜 := 𝕜) (κ := κ) p hp U).comp (boundedOperatorApply A) := rfl

theorem norm_lpOperatorUltralimit_le (p : BanachExponent) (hp : 0 < p.val.toReal)
    (U : Ultrafilter ι) :
    ‖lpOperatorUltralimit (𝕜 := 𝕜) (E := E) (κ := κ) p hp U‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [lpOperatorUltralimit_apply_operator]
  exact ((lpCoordinateUltralimit (𝕜 := 𝕜) (κ := κ) p hp U).opNorm_comp_le (boundedOperatorApply A)).trans
    (mul_le_mul (norm_lpCoordinateUltralimit_le (𝕜 := 𝕜) (κ := κ) p hp U) (norm_boundedOperatorApply_le A)
      (norm_nonneg _) zero_le_one)

theorem lpOperatorUltralimit_coordinate_tendsto (p : BanachExponent) (hp : 0 < p.val.toReal)
    (U : Ultrafilter ι) (A : lp (fun _ : ι => E →L[𝕜] lp (fun _ : κ => 𝕜) p.val) ∞)
    (x : E) (k : κ) :
    Tendsto (fun i => A i x k) (U : Filter ι) (𝓝 (lpOperatorUltralimit p hp U A x k)) :=
  lpUltralimitCoordinate_tendsto p U (boundedOperatorApply A x) k

theorem lpOperatorUltralimit_eq_of_tendsto (p : BanachExponent) (hp : 0 < p.val.toReal)
    (U : Ultrafilter ι) (A : lp (fun _ : ι => E →L[𝕜] lp (fun _ : κ => 𝕜) p.val) ∞)
    {T : E →L[𝕜] lp (fun _ : κ => 𝕜) p.val}
    (hAT : ∀ x k, Tendsto (fun i => A i x k) U (𝓝 (T x k))) :
    lpOperatorUltralimit p hp U A = T := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  exact tendsto_nhds_unique (lpOperatorUltralimit_coordinate_tendsto p hp U A x k) (hAT x k)

end ThesisCommon

