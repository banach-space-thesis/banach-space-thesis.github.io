import ThesisCommon.Analysis.EllOneColumnNorm

/-! Construct an actual bounded operator on ell1 from uniformly bounded
columns, by an absolutely convergent vector series. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
variable {ι : Type*}

theorem ellOne_columns_summable (F : ι → X →L[𝕜] Y) (C : ℝ)
    (hF : ∀ i, ‖F i‖ ≤ C) (x : EllOneSum ι X) : Summable (fun i => F i (x i)) := by
  have hn : Summable (fun i => ‖x i‖) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using (lp.memℓp x).summable (by simp : 0 < (1 : ℝ≥0∞).toReal)
  exact (hn.mul_left C).of_norm_bounded (fun i => ((F i).le_opNorm (x i)).trans
    (mul_le_mul_of_nonneg_right (hF i) (norm_nonneg _)))

def ellOneColumns (F : ι → X →L[𝕜] Y) (C : ℝ) (_hC : 0 ≤ C)
    (hF : ∀ i, ‖F i‖ ≤ C) : EllOneSum ι X →L[𝕜] Y :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' i, F i (x i)
      map_add' := by
        intro x y
        simp only [lp.coeFn_add, Pi.add_apply, map_add]
        exact (ellOne_columns_summable F C hF x).tsum_add (ellOne_columns_summable F C hF y)
      map_smul' := by
        intro a x
        simp only [lp.coeFn_smul, Pi.smul_apply, map_smul]
        exact (ellOne_columns_summable F C hF x).tsum_const_smul a }
    C (fun x => by
      have hn : HasSum (fun i => ‖x i‖) ‖x‖ := by
        simpa only [ENNReal.toReal_one, Real.rpow_one] using lp.hasSum_norm (p := 1) (by simp) x
      exact (ellOne_columns_summable F C hF x).hasSum.norm_le_of_bounded
        (hn.mul_left C) (fun i => ((F i).le_opNorm (x i)).trans
          (mul_le_mul_of_nonneg_right (hF i) (norm_nonneg _))))

theorem norm_ellOneColumns_le (F : ι → X →L[𝕜] Y) (C : ℝ) (hC hF) :
    ‖ellOneColumns F C hC hF‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _

theorem ellOneColumns_single [DecidableEq ι] (F : ι → X →L[𝕜] Y) (C : ℝ) (hC hF)
    (j : ι) (x : X) : ellOneColumns F C hC hF (lp.single 1 j x) = F j x := by
  change (∑' i, F i (lp.single (E := fun _ : ι => X) 1 j x i)) = F j x
  rw [tsum_eq_single j]
  · simp
  · intro i hij
    simp [hij]

end ThesisCommon

