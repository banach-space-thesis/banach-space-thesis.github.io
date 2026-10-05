import ThesisCommon.Analysis.WienerConvolution
import Mathlib.Analysis.Complex.Circle

/-! The genuine unit-circle characters of absolutely summable convolution
sequences. Absolute summability justifies both the Fourier series and its
multiplicativity; the latter is proved by a bijective double-series change
of variables, not stipulated as a property of a quotient map.
-/
noncomputable section
namespace ThesisCommon

theorem wiener_weighted_summable_norm (z : Circle) (a : WienerSequences ℂ) :
    Summable (fun n : ℤ => ‖a n * (z : ℂ) ^ n‖) := by
  simpa only [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, mul_one]
    using wiener_summable_norm a

theorem wiener_weighted_summable (z : Circle) (a : WienerSequences ℂ) :
    Summable (fun n : ℤ => a n * (z : ℂ) ^ n) :=
  (wiener_weighted_summable_norm z a).of_norm

def wienerEvaluate (z : Circle) : WienerSequences ℂ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun a := ∑' n : ℤ, a n * (z : ℂ) ^ n
      map_add' := by
        intro a b
        simpa only [lp.coeFn_add, Pi.add_apply, add_mul] using
          (wiener_weighted_summable z a).tsum_add (wiener_weighted_summable z b)
      map_smul' := by
        intro c a
        simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply] using
          (wiener_weighted_summable z a).tsum_mul_left c }
    1 (by
      intro a
      calc
        _ ≤ ∑' n : ℤ, ‖a n * (z : ℂ) ^ n‖ :=
          norm_tsum_le_tsum_norm (wiener_weighted_summable_norm z a)
        _ = ‖a‖ := by
          simp only [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, mul_one]
          exact (wiener_norm_eq_tsum a).symm
        _ = 1 * ‖a‖ := (one_mul _).symm)

theorem wienerEvaluate_apply (z : Circle) (a : WienerSequences ℂ) :
    wienerEvaluate z a = ∑' n : ℤ, a n * (z : ℂ) ^ n := rfl

theorem norm_wienerEvaluate_le (z : Circle) : ‖wienerEvaluate z‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

@[simp] theorem wienerEvaluate_single (z : Circle) (n : ℤ) (c : ℂ) :
    wienerEvaluate z (lp.single 1 n c) = c * (z : ℂ) ^ n := by
  rw [wienerEvaluate_apply, tsum_eq_single n]
  · simp
  · intro k hk
    simp [lp.single_apply, hk]

@[simp] theorem wienerEvaluate_unit (z : Circle) :
    wienerEvaluate z (lp.single 1 0 1) = 1 := by simp

theorem wienerEvaluate_surjective (z : Circle) : Function.Surjective (wienerEvaluate z) := by
  intro c
  exact ⟨lp.single 1 0 c, by simp⟩

theorem wienerEvaluate_convolution (z : Circle) (a b : WienerSequences ℂ) :
    wienerEvaluate z (wienerConvolution a b) = wienerEvaluate z a * wienerEvaluate z b := by
  let f : ℤ → ℂ := fun n => a n * (z : ℂ) ^ n
  let g : ℤ → ℂ := fun n => b n * (z : ℂ) ^ n
  have hf : Summable (fun n => ‖f n‖) := wiener_weighted_summable_norm z a
  have hg : Summable (fun n => ‖g n‖) := wiener_weighted_summable_norm z b
  have hpair : Summable (fun p : ℤ × ℤ => f p.2 * g (p.1 - p.2)) :=
    (wienerConvolutionIndex.summable_iff (f := fun p : ℤ × ℤ => f p.1 * g p.2)).mpr
      (summable_mul_of_summable_norm hf hg)
  rw [wienerEvaluate_apply, wienerEvaluate_apply, wienerEvaluate_apply,
    tsum_mul_tsum_of_summable_norm hf hg]
  calc
    _ = ∑' n : ℤ, ∑' k : ℤ, f k * g (n - k) := by
      apply tsum_congr
      intro n
      rw [wienerConvolution_apply,
        ← (wiener_convolution_summable_norm a b n).of_norm.tsum_mul_right]
      apply tsum_congr
      intro k
      have hz : (z : ℂ) ^ k * (z : ℂ) ^ (n - k) = (z : ℂ) ^ n := by
        rw [← zpow_add₀ (Circle.coe_ne_zero z)]
        congr 1
        omega
      dsimp [f, g]
      rw [← hz]
      ring
    _ = ∑' p : ℤ × ℤ, f p.2 * g (p.1 - p.2) := hpair.tsum_prod.symm
    _ = ∑' p : ℤ × ℤ, f p.1 * g p.2 :=
      wienerConvolutionIndex.tsum_eq (fun p : ℤ × ℤ => f p.1 * g p.2)

end ThesisCommon
