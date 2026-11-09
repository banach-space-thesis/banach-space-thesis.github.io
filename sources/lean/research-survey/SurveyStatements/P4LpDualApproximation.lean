import SurveyStatements.P4LpDualCoordinates

/-! Finite coordinate restrictions converge in norm for the dual of an ℓ² sum. -/

noncomputable section
set_option autoImplicit false

open scoped ENNReal
open Filter Topology

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {ι : Type v} [DecidableEq ι] {E : ι → Type w}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

def lp2NormSequence (f : lp E 2) : lp (fun _ : ι => ℝ) 2 :=
  ⟨fun i => ‖f i‖, memℓp_gen (by
    have h := (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [norm_norm] using h)⟩

@[simp] lemma lp2NormSequence_apply (f : lp E 2) (i : ι) :
    lp2NormSequence f i = ‖f i‖ := rfl

@[simp] lemma norm_lp2NormSequence (f : lp E 2) : ‖lp2NormSequence f‖ = ‖f‖ := by
  have h₁ := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f
  have h₂ := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (lp2NormSequence f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, lp2NormSequence_apply, norm_norm] at h₁ h₂
  nlinarith [norm_nonneg f, norm_nonneg (lp2NormSequence f)]

def lp2DualNormSequence (φ : StrongDual 𝕜 (lp E 2)) : lp (fun _ : ι => ℝ) 2 :=
  ⟨fun i => ‖lp2DualCoordinate φ i‖, memℓp_gen (by
    simpa only [norm_norm, ENNReal.toReal_ofNat, Real.rpow_two] using
      summable_sq_lp2DualCoordinate_norm φ)⟩

@[simp] lemma lp2DualNormSequence_apply (φ : StrongDual 𝕜 (lp E 2)) (i : ι) :
    lp2DualNormSequence φ i = ‖lp2DualCoordinate φ i‖ := rfl

lemma lp2Dual_apply_le (φ : StrongDual 𝕜 (lp E 2)) (f : lp E 2) :
    ‖φ f‖ ≤ ‖lp2DualNormSequence φ‖ * ‖f‖ := by
  have hholder := lp.tsum_mul_le_mul_norm
    (by simpa using Real.HolderConjugate.two_two : (2 : ℝ≥0∞).toReal.HolderConjugate
      (2 : ℝ≥0∞).toReal) (lp2DualNormSequence φ) (lp2NormSequence f)
  simp only [lp2DualNormSequence_apply, lp2NormSequence_apply, norm_norm,
    norm_lp2NormSequence] at hholder
  have hs := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) f).map φ φ.continuous
  have hb : ∀ i, ‖φ (lp.single 2 i (f i))‖ ≤
      ‖lp2DualCoordinate φ i‖ * ‖f i‖ := fun i => (lp2DualCoordinate φ i).le_opNorm (f i)
  exact (hs.norm_le_of_bounded hholder.1.hasSum hb).trans hholder.2

lemma lp2Dual_norm_le (φ : StrongDual 𝕜 (lp E 2)) :
    ‖φ‖ ≤ ‖lp2DualNormSequence φ‖ :=
  φ.opNorm_le_bound (norm_nonneg _) (lp2Dual_apply_le φ)

def lp2Eval (i : ι) : lp E 2 →L[𝕜] E i :=
  ({ toFun := fun f => f i
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : lp E 2 →ₗ[𝕜] E i).mkContinuous 1
    (fun f => by simpa using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) f i)

def lp2Projection (s : Finset ι) : lp E 2 →L[𝕜] lp E 2 :=
  ∑ i ∈ s, (lp.singleContinuousLinearMap 𝕜 E 2 i).comp (lp2Eval i)

lemma lp2Projection_apply (s : Finset ι) (f : lp E 2) :
    lp2Projection (𝕜 := 𝕜) s f = ∑ i ∈ s, lp.single 2 i (f i) := by
  simp [lp2Projection, lp2Eval, lp.singleContinuousLinearMap_apply]

lemma norm_lp2Projection_apply_le (s : Finset ι) (f : lp E 2) :
    ‖lp2Projection (𝕜 := 𝕜) s f‖ ≤ ‖f‖ := by
  have h₁ := lp.norm_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (fun i => f i) s
  have h₂ := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h₁ h₂
  rw [lp2Projection_apply]
  nlinarith [norm_nonneg (∑ i ∈ s, lp.single 2 i (f i)), norm_nonneg f]

lemma norm_lp2Projection_le_one (s : Finset ι) : ‖lp2Projection (𝕜 := 𝕜) (E := E) s‖ ≤ 1 := by
  apply (lp2Projection (𝕜 := 𝕜) (E := E) s).opNorm_le_bound (by norm_num)
  intro f
  simpa using norm_lp2Projection_apply_le (𝕜 := 𝕜) s f

def lp2DualTruncation (φ : StrongDual 𝕜 (lp E 2)) (s : Finset ι) : StrongDual 𝕜 (lp E 2) :=
  ∑ i ∈ s, (lp2DualCoordinate φ i).comp (lp2Eval i)

lemma lp2DualCoordinate_truncation (φ : StrongDual 𝕜 (lp E 2)) (s : Finset ι) (i : ι) :
    lp2DualCoordinate (lp2DualTruncation φ s) i =
      if i ∈ s then lp2DualCoordinate φ i else 0 := by
  classical
  ext x
  simp only [lp2DualCoordinate_apply, lp2DualTruncation, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, lp2Eval]
  change (∑ j ∈ s, φ (lp.single 2 j (Pi.single i x j))) =
    (if i ∈ s then lp2DualCoordinate φ i else 0) x
  by_cases hi : i ∈ s
  · rw [if_pos hi, lp2DualCoordinate_apply]
    have h := Finset.sum_eq_single i (s := s)
      (f := fun j => φ (lp.single 2 j (Pi.single i x j)))
      (fun j hj hji => by simp [Pi.single_eq_of_ne hji])
      (fun hnot => (hnot hi).elim)
    simpa using h
  · rw [if_neg hi]
    change (∑ j ∈ s, φ (lp.single 2 j (Pi.single i x j))) = 0
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [Pi.single_eq_of_ne hji]

lemma lp2DualNormSequence_sub_truncation (φ : StrongDual 𝕜 (lp E 2)) (s : Finset ι) :
    lp2DualNormSequence (φ - lp2DualTruncation φ s) =
      lp2DualNormSequence φ - ∑ i ∈ s, lp.single 2 i (lp2DualNormSequence φ i) := by
  classical
  ext i
  change ‖lp2DualCoordinate (φ - lp2DualTruncation φ s) i‖ = _
  have hsub : lp2DualCoordinate (φ - lp2DualTruncation φ s) i =
      lp2DualCoordinate φ i - lp2DualCoordinate (lp2DualTruncation φ s) i := rfl
  rw [hsub, lp2DualCoordinate_truncation]
  by_cases hi : i ∈ s <;> simp [hi, lp.coeFn_sub, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single, lp2DualNormSequence_apply]

lemma tendsto_lp2DualTruncation (φ : StrongDual 𝕜 (lp E 2)) :
    Tendsto (lp2DualTruncation φ) atTop (𝓝 φ) := by
  have htail : Tendsto
      (fun s : Finset ι => ‖lp2DualNormSequence φ -
        ∑ i ∈ s, lp.single 2 i (lp2DualNormSequence φ i)‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto
      (fun _ : Finset ι => lp2DualNormSequence φ) atTop (𝓝 (lp2DualNormSequence φ))).sub
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (lp2DualNormSequence φ))).norm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) ?_ htail
  intro s
  rw [norm_sub_rev]
  exact (lp2Dual_norm_le (φ - lp2DualTruncation φ s)).trans_eq
    (congrArg norm (lp2DualNormSequence_sub_truncation φ s))

end SurveyStatements.P4
