import ThesisCommon.LpCut

/-! Actual bounded measurable multiplication on scalar Lp. The definition
acts on the genuine almost-everywhere quotient and retains its pointwise formula. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def lpBoundedMultiplyValue (g : X → 𝕜) (hg : AEStronglyMeasurable g μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (f : Lp 𝕜 p μ) : Lp 𝕜 p μ := by
  have hm : MemLp (fun x => g x * f x) p μ :=
    (Lp.memLp f).of_le_mul (c := C) (hg.mul (Lp.memLp f).aestronglyMeasurable) (by
      filter_upwards [hbound] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  exact hm.toLp (fun x => g x * f x)

omit [Fact (1 ≤ p)] in
theorem lpBoundedMultiplyValue_coe (g : X → 𝕜) (hg : AEStronglyMeasurable g μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (f : Lp 𝕜 p μ) :
    lpBoundedMultiplyValue g hg C hbound f =ᵐ[μ] fun x => g x * f x := by
  unfold lpBoundedMultiplyValue
  exact MemLp.coeFn_toLp _

omit [Fact (1 ≤ p)] in
theorem lpBoundedMultiplyValue_norm_le (g : X → 𝕜) (hg : AEStronglyMeasurable g μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (f : Lp 𝕜 p μ) :
    ‖lpBoundedMultiplyValue g hg C hbound f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [lpBoundedMultiplyValue_coe g hg C hbound f, hbound] with x hx hb
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

def lpBoundedMultiplier (g : X → 𝕜) (hg : AEStronglyMeasurable g μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  LinearMap.mkContinuous
    { toFun := lpBoundedMultiplyValue g hg C hbound
      map_add' := fun f h => by
        apply Lp.ext
        filter_upwards [lpBoundedMultiplyValue_coe g hg C hbound (f + h),
          lpBoundedMultiplyValue_coe g hg C hbound f, lpBoundedMultiplyValue_coe g hg C hbound h,
          Lp.coeFn_add f h, Lp.coeFn_add (lpBoundedMultiplyValue g hg C hbound f)
            (lpBoundedMultiplyValue g hg C hbound h)] with x ha hb hc hd he
        simp only [Pi.add_apply] at hd he
        rw [ha, hd, he, hb, hc, mul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [lpBoundedMultiplyValue_coe g hg C hbound (c • f),
          lpBoundedMultiplyValue_coe g hg C hbound f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (lpBoundedMultiplyValue g hg C hbound f)] with x ha hb hc hd
        simp only [Pi.smul_apply, smul_eq_mul] at hc hd
        simp only [ha, hb, hc, hd, RingHom.id_apply]
        ring }
    C (lpBoundedMultiplyValue_norm_le g hg C hbound)

theorem lpBoundedMultiplier_coe (g : X → 𝕜) (hg : AEStronglyMeasurable g μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (f : Lp 𝕜 p μ) :
    lpBoundedMultiplier g hg C hbound f =ᵐ[μ] fun x => g x * f x :=
  lpBoundedMultiplyValue_coe g hg C hbound f

theorem norm_lpBoundedMultiplier_le (g : X → 𝕜) (hg : AEStronglyMeasurable g μ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    ‖lpBoundedMultiplier (p := p) g hg C hbound‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

theorem lpBoundedMultiplier_eq_of_ae_eq {g h : X → 𝕜}
    (hg : AEStronglyMeasurable g μ) (hh : AEStronglyMeasurable h μ)
    (C D : ℝ) (hb : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (hd : ∀ᵐ x ∂μ, ‖h x‖ ≤ D)
    (heq : g =ᵐ[μ] h) :
    lpBoundedMultiplier (p := p) g hg C hb = lpBoundedMultiplier h hh D hd := by
  ext f : 1
  apply Lp.ext
  filter_upwards [lpBoundedMultiplier_coe g hg C hb f,
    lpBoundedMultiplier_coe h hh D hd f, heq] with x hx hy he
  rw [hx, hy, he]

end ThesisCommon
