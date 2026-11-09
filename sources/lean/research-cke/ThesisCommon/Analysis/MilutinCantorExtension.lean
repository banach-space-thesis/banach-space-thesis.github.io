import ThesisCommon.Analysis.MilutinBinaryTreeWeights

/-! A contractive linear extension from an embedded binary Cantor space into
an arbitrary compact Hausdorff host, over either real or complex scalars. -/

noncomputable section
set_option maxHeartbeats 600000
open Set
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
variable (e : C((ℕ → Bool), Y)) (he : Function.Injective e)

def milutinFiniteCylinderExtendValue (n : ℕ) (f : C(MilutinBinaryWord n, 𝕜)) : C(Y, 𝕜) :=
  ⟨fun y => ∑ w, milutinBinaryTreeWeight e he n w y • f w, by fun_prop⟩

theorem norm_milutinFiniteCylinderExtendValue_le (n : ℕ) (f : C(MilutinBinaryWord n, 𝕜)) :
    ‖milutinFiniteCylinderExtendValue e he n f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
  intro y
  calc
    ‖∑ w, milutinBinaryTreeWeight e he n w y • f w‖ ≤
        ∑ w, ‖milutinBinaryTreeWeight e he n w y • f w‖ := norm_sum_le _ _
    _ = ∑ w, milutinBinaryTreeWeight e he n w y * ‖f w‖ := by
      apply Finset.sum_congr rfl
      intro w _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (milutinBinaryTreeWeight_nonneg e he n w y)]
    _ ≤ ∑ w, milutinBinaryTreeWeight e he n w y * ‖f‖ :=
      Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (f.norm_coe_le_norm w)
        (milutinBinaryTreeWeight_nonneg e he n w y)
    _ = ‖f‖ := by rw [← Finset.sum_mul, milutinBinaryTreeWeight_sum, one_mul]

def milutinFiniteCylinderExtend (n : ℕ) : C(MilutinBinaryWord n, 𝕜) →L[𝕜] C(Y, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := milutinFiniteCylinderExtendValue e he n
      map_add' := by
        intro f g
        ext y
        simp [milutinFiniteCylinderExtendValue, smul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a f
        ext y
        simp [milutinFiniteCylinderExtendValue, Finset.mul_sum, mul_smul_comm] }
    1 (fun f => by simpa using norm_milutinFiniteCylinderExtendValue_le e he n f)

theorem norm_milutinFiniteCylinderExtend_le (n : ℕ) :
    ‖milutinFiniteCylinderExtend (𝕜 := 𝕜) e he n‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem milutinFiniteCylinderExtend_compatible (n : ℕ) (f : C(MilutinBinaryWord n, 𝕜)) :
    milutinFiniteCylinderExtend e he (n + 1) (f.comp (milutinBinaryWordBonding n)) =
      milutinFiniteCylinderExtend e he n f := by
  ext y
  change (∑ w, milutinBinaryTreeWeight e he (n + 1) w y • f (Fin.init w)) = _
  rw [milutinBinaryWord_sum_snoc]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Fin.init_snoc, milutinBinaryTreeWeight_snoc_false, milutinBinaryTreeWeight_snoc_true,
    ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply, ← add_smul]
  congr 1
  ring

theorem milutinFiniteCylinderExtend_on_image (n : ℕ) (f : C(MilutinBinaryWord n, 𝕜))
    (x : ℕ → Bool) :
    milutinFiniteCylinderExtend e he n f (e x) = f (milutinBinaryWordPrefix n x) := by
  classical
  change (∑ w, milutinBinaryTreeWeight e he n w (e x) • f w) = _
  simp [milutinBinaryTreeWeight_on_image, ite_smul]

def milutinWordLimitExtend : C(MilutinInverseLimit milutinBinaryWordBonding, 𝕜) →L[𝕜] C(Y, 𝕜) :=
  milutinAverageExtension milutinBinaryWordBonding milutinBinaryWordBonding_surjective
    (milutinFiniteCylinderExtend e he) (milutinFiniteCylinderExtend_compatible e he)
    (norm_milutinFiniteCylinderExtend_le e he)

theorem norm_milutinWordLimitExtend_le : ‖milutinWordLimitExtend (𝕜 := 𝕜) e he‖ ≤ 1 :=
  norm_milutinAverageExtension_le _ _ _ _ _

theorem milutinWordLimitExtend_on_image (f : C(MilutinInverseLimit milutinBinaryWordBonding, 𝕜))
    (x : ℕ → Bool) :
    milutinWordLimitExtend e he f (e x) = f (milutinBinaryToWordLimit x) := by
  refine (milutinCylinderModule_denseRange (𝕜 := 𝕜) milutinBinaryWordBonding).induction_on
    (p := fun g => milutinWordLimitExtend e he g (e x) = g (milutinBinaryToWordLimit x)) f ?_ ?_
  · exact isClosed_eq ((continuous_eval_const (e x)).comp
      (milutinWordLimitExtend e he).continuous)
      (continuous_eval_const (milutinBinaryToWordLimit x))
  · intro g
    obtain ⟨n, h, hh⟩ := g.property
    change h.comp (milutinLimitProjection milutinBinaryWordBonding n) = g.val at hh
    change milutinWordLimitExtend e he g.val (e x) = g.val (milutinBinaryToWordLimit x)
    rw [← hh]
    dsimp only [milutinWordLimitExtend]
    rw [milutinAverageExtension_apply_cylinder, milutinFiniteCylinderExtend_on_image]
    rfl

/-- The norm at most one linear extension from any embedded copy of Cantor space. -/
def milutinCantorExtend : C((ℕ → Bool), 𝕜) →L[𝕜] C(Y, 𝕜) :=
  (milutinWordLimitExtend e he).comp (continuousMapPullback milutinWordLimitToBinary)

theorem norm_milutinCantorExtend_le : ‖milutinCantorExtend (𝕜 := 𝕜) e he‖ ≤ 1 := by
  let A : C(MilutinInverseLimit milutinBinaryWordBonding, 𝕜) →L[𝕜] C(Y, 𝕜) :=
    milutinWordLimitExtend e he
  let J : C((ℕ → Bool), 𝕜) →L[𝕜] C(MilutinInverseLimit milutinBinaryWordBonding, 𝕜) :=
    continuousMapPullback milutinWordLimitToBinary
  have hA : ‖A‖ ≤ 1 := norm_milutinWordLimitExtend_le (𝕜 := 𝕜) e he
  have hJ : ‖J‖ ≤ 1 := norm_continuousMapPullback_le (𝕜 := 𝕜) milutinWordLimitToBinary
  change ‖A.comp J‖ ≤ 1
  calc
    ‖A.comp J‖ ≤ ‖A‖ * ‖J‖ := A.opNorm_comp_le J
    _ ≤ 1 * 1 := mul_le_mul hA hJ (norm_nonneg J) zero_le_one
    _ = 1 := one_mul 1

@[simp] theorem milutinCantorExtend_on_image (f : C((ℕ → Bool), 𝕜)) (x : ℕ → Bool) :
    milutinCantorExtend e he f (e x) = f x := by
  change milutinWordLimitExtend e he (continuousMapPullback milutinWordLimitToBinary f) (e x) = _
  rw [milutinWordLimitExtend_on_image]
  rfl

theorem milutinCantorExtend_right_inverse :
    (continuousMapPullback e).comp (milutinCantorExtend (𝕜 := 𝕜) e he) =
      ContinuousLinearMap.id 𝕜 C((ℕ → Bool), 𝕜) := by
  ext f x
  exact milutinCantorExtend_on_image e he f x

include he in
theorem milutin_cantor_contractive_extension :
    ∃ E : C((ℕ → Bool), 𝕜) →L[𝕜] C(Y, 𝕜), ‖E‖ ≤ 1 ∧
      (continuousMapPullback e).comp E = ContinuousLinearMap.id 𝕜 C((ℕ → Bool), 𝕜) :=
  ⟨milutinCantorExtend e he, norm_milutinCantorExtend_le e he,
    milutinCantorExtend_right_inverse e he⟩

end ThesisCommon
