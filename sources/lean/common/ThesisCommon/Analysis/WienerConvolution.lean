import ThesisCommon.Analysis.GowersMaureyOperatorTargets
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Actual absolutely summable convolution on ℤ, on the literal lp space
used by the Gowers--Maurey quotient target. All rearrangements below are
justified by summability of the double series of norms.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem wiener_summable_norm (a : WienerSequences 𝕜) : Summable (fun n => ‖a n‖) := by
  simpa using (lp.memℓp a).summable (by simp : (0 : ℝ) < (1 : ℝ≥0∞).toReal)

theorem wiener_norm_eq_tsum (a : WienerSequences 𝕜) : ‖a‖ = ∑' n, ‖a n‖ := by
  simpa using lp.norm_eq_tsum_rpow (by simp : (0 : ℝ) < (1 : ℝ≥0∞).toReal) a

def wienerConvolutionIndex : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

theorem wiener_convolution_summable_norm_pair (a b : WienerSequences 𝕜) :
    Summable (fun p : ℤ × ℤ => ‖a p.2 * b (p.1 - p.2)‖) :=
  (wienerConvolutionIndex.summable_iff (f := fun p : ℤ × ℤ => ‖a p.1 * b p.2‖)).mpr
    ((wiener_summable_norm a).mul_norm
    (wiener_summable_norm b))

theorem wiener_convolution_summable_norm (a b : WienerSequences 𝕜) (n : ℤ) :
    Summable (fun k : ℤ => ‖a k * b (n - k)‖) :=
  (wiener_convolution_summable_norm_pair a b).prod_factor n

theorem wienerConvolutionCoordinate_summable_norm (a b : WienerSequences 𝕜) :
    Summable (fun n => ‖wienerConvolutionCoordinate a b n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => norm_tsum_le_tsum_norm (wiener_convolution_summable_norm a b n))
  exact (wiener_convolution_summable_norm_pair a b).prod

/-- Convolution is a genuine element of ℓ1(ℤ), not just a formal sequence. -/
def wienerConvolution (a b : WienerSequences 𝕜) : WienerSequences 𝕜 :=
  ⟨wienerConvolutionCoordinate a b, memℓp_gen (by
    simpa using wienerConvolutionCoordinate_summable_norm a b)⟩

@[simp] theorem wienerConvolution_apply (a b : WienerSequences 𝕜) (n : ℤ) :
    wienerConvolution a b n = ∑' k : ℤ, a k * b (n - k) := rfl

theorem norm_wienerConvolution_le (a b : WienerSequences 𝕜) :
    ‖wienerConvolution a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [wiener_norm_eq_tsum]
  calc
    _ ≤ ∑' n, ∑' k, ‖a k * b (n - k)‖ :=
      Summable.tsum_le_tsum
        (fun n => norm_tsum_le_tsum_norm (wiener_convolution_summable_norm a b n))
        (wienerConvolutionCoordinate_summable_norm a b)
        (wiener_convolution_summable_norm_pair a b).prod
    _ = ∑' p : ℤ × ℤ, ‖a p.2 * b (p.1 - p.2)‖ :=
      (wiener_convolution_summable_norm_pair a b).tsum_prod.symm
    _ = ∑' p : ℤ × ℤ, ‖a p.1 * b p.2‖ :=
      wienerConvolutionIndex.tsum_eq (fun p : ℤ × ℤ => ‖a p.1 * b p.2‖)
    _ = (∑' i, ‖a i‖) * ∑' j, ‖b j‖ := by
      simp only [norm_mul]
      exact (tsum_mul_tsum_of_summable_norm (R := ℝ)
        (f := fun i => ‖a i‖) (g := fun j => ‖b j‖)
        (by simpa using wiener_summable_norm a)
        (by simpa using wiener_summable_norm b)).symm
    _ = ‖a‖ * ‖b‖ := by rw [wiener_norm_eq_tsum, wiener_norm_eq_tsum]

@[simp] theorem wienerConvolution_unit_left (a : WienerSequences 𝕜) :
    wienerConvolution (lp.single 1 0 1) a = a := by
  ext n
  rw [wienerConvolution_apply, tsum_eq_single (0 : ℤ)]
  · simp
  · intro k hk
    simp [lp.single_apply, hk]

@[simp] theorem wienerConvolution_unit_right (a : WienerSequences 𝕜) :
    wienerConvolution a (lp.single 1 0 1) = a := by
  ext n
  rw [wienerConvolution_apply, tsum_eq_single n]
  · simp
  · intro k hk
    have hnk : n - k ≠ 0 := by omega
    simp [lp.single_apply, hnk]

end ThesisCommon
