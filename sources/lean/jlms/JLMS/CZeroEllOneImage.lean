import JLMS.FamilyImageCoordinates
import JLMS.EllOneSynthesis

/-!
# Transfer an ℓ¹ operator to its compact function image

Use the images of the ℓ¹ coordinate vectors as the family of C₀ functions.
Synthesize their coordinate functions on the compact family image. Pullback
of this new operator gives the original operator, and their norms agree on
every input. Thus a bounded-below embedding transfers without loss.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]

def cZeroEllOneBasisFamily (J : ellOne 𝕜 →L[𝕜] CZero 𝕜 K) (n : ℕ) : CZero 𝕜 K :=
  J (lp.single 1 n (1 : 𝕜))

theorem norm_cZeroEllOneFamilyCoordinate_le (J : ellOne 𝕜 →L[𝕜] CZero 𝕜 K) (n : ℕ) :
    ‖cZeroFamilyCoordinate (cZeroEllOneBasisFamily J) n‖ ≤ ‖J‖ := by
  apply (norm_cZeroFamilyCoordinate_le _ n).trans
  have h := J.le_opNorm (lp.single 1 n (1 : 𝕜))
  simpa only [lp.norm_single (by norm_num : 0 < (1 : ENNReal)), norm_one, mul_one] using h

def cZeroEllOneImageOperator (J : ellOne 𝕜 →L[𝕜] CZero 𝕜 K) :
    ellOne 𝕜 →L[𝕜] CZero 𝕜 (CZeroFamilyImage (cZeroEllOneBasisFamily J)) :=
  ellOneSynthesis (cZeroFamilyCoordinate (cZeroEllOneBasisFamily J)) ‖J‖
    (norm_nonneg J) (norm_cZeroEllOneFamilyCoordinate_le J)

theorem ellOne_operator_hasSum_units {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (J : ellOne 𝕜 →L[𝕜] E) (a : ellOne 𝕜) :
    HasSum (fun n => a n • J (lp.single 1 n (1 : 𝕜))) (J a) := by
  have h := (lp.hasSum_single (by norm_num : (1 : ENNReal) ≠ ⊤) a).map J J.continuous
  convert h using 1
  ext n
  have hsingle : (lp.single 1 n (a n) : ellOne 𝕜) = a n • lp.single 1 n (1 : 𝕜) := by
    simpa only [smul_eq_mul, mul_one] using
      lp.single_smul (E := fun _ : ℕ => 𝕜) 1 n (a n) (1 : 𝕜)
  dsimp only [Function.comp_def]
  rw [hsingle, map_smul]

theorem cZeroEllOneImageOperator_imageMap (J : ellOne 𝕜 →L[𝕜] CZero 𝕜 K)
    (a : ellOne 𝕜) (x : OnePoint K) :
    cZeroEllOneImageOperator J a (cZeroFamilyImageMap (cZeroEllOneBasisFamily J) x) =
      extendCZeroOnePoint (J a) x := by
  let f := cZeroEllOneBasisFamily J
  let v := cZeroFamilyCoordinate f
  have hs := summable_ellOne_smul v ‖J‖ (norm_cZeroEllOneFamilyCoordinate_le J) a
  change evaluation (cZeroFamilyImageMap f x) (∑' n, a n • v n) = _
  rw [(evaluation (cZeroFamilyImageMap f x)).map_tsum hs]
  simp only [map_smul, evaluation_apply, cZeroFamilyCoordinate_imageMap]
  induction x using OnePoint.rec with
  | infty => change (∑' n, a n • (0 : 𝕜)) = 0; simp
  | coe x =>
    have h := (ellOne_operator_hasSum_units J a).map (evaluation (𝕜 := 𝕜) x)
      (evaluation (𝕜 := 𝕜) x).continuous
    simpa only [map_smul, evaluation_apply] using h.tsum_eq

theorem norm_cZeroEllOneImageOperator_apply (J : ellOne 𝕜 →L[𝕜] CZero 𝕜 K)
    (a : ellOne 𝕜) : ‖cZeroEllOneImageOperator J a‖ = ‖J a‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg (J a))).mpr
    intro v
    obtain ⟨x, rfl⟩ := cZeroFamilyImageMap_surjective (cZeroEllOneBasisFamily J) v
    change ‖cZeroEllOneImageOperator J a (cZeroFamilyImageMap (cZeroEllOneBasisFamily J) x)‖ ≤ _
    rw [cZeroEllOneImageOperator_imageMap]
    induction x using OnePoint.rec with
    | infty => change ‖(0 : 𝕜)‖ ≤ ‖J a‖; simpa using norm_nonneg (J a)
    | coe x => exact norm_CZero_apply_le (J a) x
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg (cZeroEllOneImageOperator J a))).mpr
    intro x
    have h := norm_CZero_apply_le (cZeroEllOneImageOperator J a)
      (cZeroFamilyImageMap (cZeroEllOneBasisFamily J) (x : OnePoint K))
    rw [cZeroEllOneImageOperator_imageMap] at h
    exact h

end JLMS
