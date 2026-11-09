import SurveyStatements.P5GridScalarApproximationRoot
import SurveyStatements.P5GridStabilityNormLimits

/-! Scalar approximation of the actual diagonal norm limit, and exact
square-grid approximation of the difference of the two norm limits. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SurveyStatements.P5
open P5Support BiTree
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem diagonalGrid_zero (d : DyadicIndex → DyadicIndex → 𝕜) :
    diagonalGrid (p := p) d 0 =
      d root root • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p) := by
  unfold diagonalGrid
  rw [mixedDyadicGridOperator_zero]
  rfl

theorem norm_diagonalGrid_limit_sub_scalar_le
    (d : DyadicIndex → DyadicIndex → 𝕜) (η : ℕ → ℕ → ℝ)
    {δ : ℝ} (hs : SemiStable d η δ) (hη : ∀ n, 0 ≤ η n n)
    (hsum : Summable (fun n => η n n))
    (M1 : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (hM1 : Tendsto (diagonalGrid (p := p) d) atTop (𝓝 M1)) (lam : 𝕜) :
    ‖M1 - lam • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p)‖ ≤
      (∑' n, η n n) + ‖d root root - lam‖ := by
  obtain ⟨M, hM, htail⟩ := exists_diagonalGrid_norm_limit (p := p) d η hs hη hsum
  have heq : M = M1 := tendsto_nhds_unique hM hM1
  have hbase : ‖M1 - diagonalGrid d 0‖ ≤ ∑' n, η n n := by
    simpa only [heq, Nat.zero_add] using htail 0
  have hroot : ‖diagonalGrid (p := p) d 0 -
      lam • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p)‖ ≤ ‖d root root - lam‖ := by
    rw [diagonalGrid_zero, ← sub_smul, norm_smul]
    have hid : ‖ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p)‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    exact (mul_le_mul_of_nonneg_left hid (norm_nonneg _)).trans_eq (mul_one _)
  have htriangle : ‖M1 - lam • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p)‖ ≤
      ‖M1 - diagonalGrid d 0‖ +
        ‖diagonalGrid d 0 - lam • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p)‖ := by
    simpa only [dist_eq_norm] using
      dist_triangle M1 (diagonalGrid (p := p) d 0)
        (lam • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p))
  exact htriangle.trans (add_le_add hbase hroot)

theorem diagonal_superdiagonal_difference_square
    (d : DyadicIndex → DyadicIndex → 𝕜) (n : ℕ) :
    diagonalGrid (p := p) d n - superdiagonalGrid d n =
      mixedDyadicGridOperator (n + 1) (n + 1) (fun i j =>
        d ⟨n, lpHaarParentIndex n i⟩ ⟨n, lpHaarParentIndex n j⟩ -
          d ⟨n, lpHaarParentIndex n i⟩ ⟨n + 1, j⟩) := by
  let a : Fin (2 ^ (n + 1)) → Fin (2 ^ (n + 1)) → 𝕜 := fun i j =>
    d ⟨n, lpHaarParentIndex n i⟩ ⟨n, lpHaarParentIndex n j⟩
  let b : Fin (2 ^ (n + 1)) → Fin (2 ^ (n + 1)) → 𝕜 := fun i j =>
    d ⟨n, lpHaarParentIndex n i⟩ ⟨n + 1, j⟩
  have ha : mixedDyadicGridOperator (p := p) (n + 1) (n + 1) a =
      diagonalGrid d n := by
    dsimp only [a]
    rw [mixedDyadicGridOperator_refine_inner (𝕜 := 𝕜) (p := p) (n + 1) n
      (fun i j => d ⟨n, lpHaarParentIndex n i⟩ ⟨n, j⟩)]
    exact mixedDyadicGridOperator_refine_outer (𝕜 := 𝕜) (p := p) n n
      (fun i j => d ⟨n, i⟩ ⟨n, j⟩)
  have hb : mixedDyadicGridOperator (p := p) (n + 1) (n + 1) b =
      superdiagonalGrid d n := by
    dsimp only [b]
    exact mixedDyadicGridOperator_refine_outer (𝕜 := 𝕜) (p := p) n (n + 1)
      (fun i j => d ⟨n, i⟩ ⟨n + 1, j⟩)
  rw [← ha, ← hb]
  change (mixedDyadicGridLinear (𝕜 := 𝕜) (p := p) (n + 1) (n + 1)) a -
      (mixedDyadicGridLinear (𝕜 := 𝕜) (p := p) (n + 1) (n + 1)) b =
        (mixedDyadicGridLinear (𝕜 := 𝕜) (p := p) (n + 1) (n + 1)) (a - b)
  exact (map_sub (mixedDyadicGridLinear (𝕜 := 𝕜) (p := p) (n + 1) (n + 1)) a b).symm

theorem diagonal_superdiagonal_difference_square_approx
    (d : DyadicIndex → DyadicIndex → 𝕜)
    (M1 M2 : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (hM1 : Tendsto (diagonalGrid (p := p) d) atTop (𝓝 M1))
    (hM2 : Tendsto (superdiagonalGrid (p := p) d) atTop (𝓝 M2)) :
    ∀ ε : ℝ, 0 < ε → ∃ m : ℕ,
      ∃ a : Fin (2 ^ m) → Fin (2 ^ m) → 𝕜,
        ‖(M1 - M2) - mixedDyadicGridOperator m m a‖ < ε := by
  intro ε hε
  have hzero : Tendsto (fun n =>
      ‖(M1 - M2) - (diagonalGrid (p := p) d n - superdiagonalGrid d n)‖)
        atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds (x := M1 - M2)).sub (hM1.sub hM2)).norm
  have hsmall : ∀ᶠ n in atTop,
      ‖(M1 - M2) - (diagonalGrid (p := p) d n - superdiagonalGrid d n)‖ < ε :=
    (tendsto_order.mp hzero).2 ε hε
  obtain ⟨n, hn⟩ := hsmall.exists
  refine ⟨n + 1, fun i j =>
    d ⟨n, lpHaarParentIndex n i⟩ ⟨n, lpHaarParentIndex n j⟩ -
      d ⟨n, lpHaarParentIndex n i⟩ ⟨n + 1, j⟩, ?_⟩
  rw [← diagonal_superdiagonal_difference_square (p := p) d n]
  exact hn

end SurveyStatements.P5
