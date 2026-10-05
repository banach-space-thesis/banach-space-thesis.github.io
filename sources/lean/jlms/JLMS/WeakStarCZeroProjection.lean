import JLMS.CZeroCoordinateExtensions
import JLMS.WeakStarSequenceOperator
import JLMS.CZeroSubsequencePairs

/-!
# A complemented c₀ subcopy from weak-star sequential compactness

Extend the coordinates of a bounded-below embedding J by Hahn–Banach.
Extract a common weak-star-convergent subsequence in the dual unit ball.
Half-differences of paired functionals define an operator into c₀, and
paired coordinate insertion gives an exact right inverse through J.

The quantitative conclusion is ‖U‖≤1/c and ‖A‖≤1, with UJA=I.
It applies to any normed codomain whose dual ball satisfies the paper's
sequential compactness hypothesis, without separability assumptions.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Quantitative complementation of a paired subcopy of a given c₀ embedding. -/
theorem exists_cZero_projection_of_weakStar
    (hX : DualBallWeakStarSeqCompact 𝕜 X) (J : cZero 𝕜 →L[𝕜] X)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ a, c * ‖a‖ ≤ ‖J a‖) :
    ∃ U : X →L[𝕜] cZero 𝕜, ∃ A : cZero 𝕜 →L[𝕜] cZero 𝕜,
      (U.comp J).comp A = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧
      ‖U‖ ≤ 1 / c ∧ ‖A‖ ≤ 1 := by
  letI : NormSMulClass 𝕜 (X →L[𝕜] cZero 𝕜) :=
    @NormedSpace.toNormSMulClass 𝕜 (X →L[𝕜] cZero 𝕜) _ _ _
  obtain ⟨f, hf, hfa⟩ := exists_cZero_coordinateExtensions J hc hlower
  let g (n : ℕ) : X →L[𝕜] 𝕜 := (c : 𝕜) • f n
  have hg (n : ℕ) : ‖g n‖ ≤ 1 := by
    change ‖(c : 𝕜) • f n‖ ≤ 1
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hc]
    calc
      c * ‖f n‖ ≤ c * (1 / c) := mul_le_mul_of_nonneg_left (hf n) hc.le
      _ = 1 := by field_simp
  obtain ⟨s, hs, hψ, hzero⟩ := exists_weakStarNull_halfDifferences hX g hg
  let ψ (n : ℕ) := ((1 / 2 : ℝ) : 𝕜) • (g (s (2 * n)) - g (s (2 * n + 1)))
  let L := weakStarSequenceOperator ψ 1 zero_le_one hψ hzero
  let U : X →L[𝕜] cZero 𝕜 := ((c⁻¹ : ℝ) : 𝕜) • L
  let A := cZeroPairInsertion (𝕜 := 𝕜) s hs
  have hU : ‖U‖ ≤ 1 / c := by
    change ‖((c⁻¹ : ℝ) : 𝕜) • L‖ ≤ 1 / c
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hc)]
    calc
      c⁻¹ * ‖L‖ ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left
        (norm_weakStarSequenceOperator_le ψ 1 zero_le_one hψ hzero) (inv_nonneg.mpr hc.le)
      _ = 1 / c := by simp
  refine ⟨U, A, ?_, hU, norm_cZeroPairInsertion_le s hs⟩
  apply ContinuousLinearMap.ext
  intro a
  ext n
  change ((c⁻¹ : ℝ) : 𝕜) *
    (((1 / 2 : ℝ) : 𝕜) * (g (s (2 * n)) (J (A a)) -
      g (s (2 * n + 1)) (J (A a)))) = a n
  change ((c⁻¹ : ℝ) : 𝕜) *
    (((1 / 2 : ℝ) : 𝕜) * ((c : 𝕜) * f (s (2 * n)) (J (A a)) -
      (c : 𝕜) * f (s (2 * n + 1)) (J (A a)))) = a n
  rw [hfa, hfa]
  change ((c⁻¹ : ℝ) : 𝕜) *
    (((1 / 2 : ℝ) : 𝕜) * ((c : 𝕜) * cZeroPairInsertion s hs a (s (2 * n)) -
      (c : 𝕜) * cZeroPairInsertion s hs a (s (2 * n + 1)))) = a n
  rw [cZeroPairInsertion_even, cZeroPairInsertion_odd]
  have hcast : ((c⁻¹ : ℝ) : 𝕜) * (c : 𝕜) = 1 := by
    rw [← RCLike.ofReal_mul, inv_mul_cancel₀ hc.ne', RCLike.ofReal_one]
  have hhalf : ((1 / 2 : ℝ) : 𝕜) = (1 / 2 : 𝕜) := by
    simp [RCLike.ofReal_div, RCLike.ofReal_ofNat]
  rw [hhalf]
  calc
    _ = (((c⁻¹ : ℝ) : 𝕜) * (c : 𝕜)) * a n := by ring
    _ = a n := by rw [hcast, one_mul]

end JLMS
