import ThesisCommon.Analysis.WienerConvolution

/-! Algebraic laws for actual absolutely summable convolution. Associativity
is proved by an absolutely summable double-series rearrangement; all sums are
those on the literal sequence space used in the operator quotient target. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem wienerConvolution_comm (a b : WienerSequences 𝕜) :
    wienerConvolution a b = wienerConvolution b a := by
  ext n
  let e : ℤ ≃ ℤ :=
    ⟨fun k => n - k, fun k => n - k, by intro k; dsimp; omega,
      by intro k; dsimp; omega⟩
  rw [wienerConvolution_apply, wienerConvolution_apply,
    ← e.tsum_eq (fun k => b k * a (n - k))]
  apply tsum_congr
  intro k
  change a k * b (n - k) = b (n - k) * a (n - (n - k))
  rw [sub_sub_cancel]
  exact mul_comm _ _

theorem wienerConvolution_add_right (a b c : WienerSequences 𝕜) :
    wienerConvolution a (b + c) = wienerConvolution a b + wienerConvolution a c := by
  ext n
  simp only [wienerConvolution_apply, lp.coeFn_add, Pi.add_apply, mul_add]
  exact ((wiener_convolution_summable_norm a b n).of_norm.tsum_add
    (wiener_convolution_summable_norm a c n).of_norm)

theorem wienerConvolution_add_left (a b c : WienerSequences 𝕜) :
    wienerConvolution (a + b) c = wienerConvolution a c + wienerConvolution b c := by
  rw [wienerConvolution_comm (a + b), wienerConvolution_add_right,
    wienerConvolution_comm c a, wienerConvolution_comm c b]

theorem wienerConvolution_smul_right (s : 𝕜) (a b : WienerSequences 𝕜) :
    wienerConvolution a (s • b) = s • wienerConvolution a b := by
  ext n
  simp only [wienerConvolution_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (a _) s]
  exact (wiener_convolution_summable_norm a b n).of_norm.tsum_mul_left s

theorem wienerConvolution_smul_left (s : 𝕜) (a b : WienerSequences 𝕜) :
    wienerConvolution (s • a) b = s • wienerConvolution a b := by
  rw [wienerConvolution_comm (s • a), wienerConvolution_smul_right,
    wienerConvolution_comm b a]

theorem wienerConvolution_assoc (a b c : WienerSequences 𝕜) :
    wienerConvolution (wienerConvolution a b) c =
      wienerConvolution a (wienerConvolution b c) := by
  ext n
  have hb : Summable (fun p : ℤ × ℤ => ‖a p.1 * b p.2 * c (n - (p.1 + p.2))‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => ?_) (((wiener_summable_norm a).mul_norm
        (wiener_summable_norm b)).mul_right ‖c‖)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) c _) (norm_nonneg _)
  have hl : Summable (fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) * c (n - p.1)) := by
    have h := (wienerConvolutionIndex.summable_iff
      (f := fun p : ℤ × ℤ => ‖a p.1 * b p.2 * c (n - (p.1 + p.2))‖)).mpr hb
    apply Summable.of_norm
    convert h using 1
    funext p
    congr 3
    apply congrArg (fun k : ℤ => c k)
    change n - p.1 = n - (p.2 + (p.1 - p.2))
    omega
  calc
    wienerConvolution (wienerConvolution a b) c n =
        ∑' k, ∑' i, a i * b (k - i) * c (n - k) := by
      rw [wienerConvolution_apply]
      apply tsum_congr
      intro k
      rw [wienerConvolution_apply,
        ← (wiener_convolution_summable_norm a b k).of_norm.tsum_mul_right]
    _ = ∑' p : ℤ × ℤ, a p.2 * b (p.1 - p.2) * c (n - p.1) := hl.tsum_prod.symm
    _ = ∑' p : ℤ × ℤ, a p.1 * b p.2 * c (n - (p.1 + p.2)) := by
      rw [← wienerConvolutionIndex.tsum_eq
        (fun p : ℤ × ℤ => a p.1 * b p.2 * c (n - (p.1 + p.2)))]
      apply tsum_congr
      intro p
      congr 2
      apply congrArg (fun k : ℤ => c k)
      change n - p.1 = n - (p.2 + (p.1 - p.2))
      omega
    _ = ∑' i, ∑' j, a i * b j * c (n - (i + j)) := hb.of_norm.tsum_prod
    _ = wienerConvolution a (wienerConvolution b c) n := by
      rw [wienerConvolution_apply]
      apply tsum_congr
      intro i
      rw [wienerConvolution_apply,
        ← (wiener_convolution_summable_norm b c (n - i)).of_norm.tsum_mul_left]
      apply tsum_congr
      intro j
      rw [mul_assoc, sub_add_eq_sub_sub]

end ThesisCommon
