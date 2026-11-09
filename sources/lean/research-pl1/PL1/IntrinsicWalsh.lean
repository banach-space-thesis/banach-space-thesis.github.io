import PL1.IntrinsicApproximations
import PL1.WalshExpectations

/-! # Actual contractive finite-dimensional approximations in the intrinsic norm -/

noncomputable section
open Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace PL1.Noise

open IntrinsicGraph WalshExpectations ResolventEstimates

variable (𝕜 : Type*) [RCLike 𝕜] (rates : ℕ → ℝ≥0)

theorem expectation_analysis_commute (m n : ℕ) (f : Lp 𝕜 1 Walsh.haar) :
    expectationL1 𝕜 m ((dyadicSystem 𝕜 rates).analysis n f) =
      (dyadicSystem 𝕜 rates).analysis n (expectationL1 𝕜 m f) := by
  cases n with
  | zero => rfl
  | succ n =>
    change expectationL1 𝕜 m
      (((((dyadicRatio ^ (n + 1))⁻¹ : ℝ) : 𝕜)) •
        (f - resolventL1 𝕜 rates (dyadicTime (n + 1)) f)) = _
    rw [map_smul, map_sub]
    have hc := DFunLike.congr_fun
      (expectationL1_resolvent_commute 𝕜 m rates (dyadicTime (n + 1))) f
    change expectationL1 𝕜 m (resolventL1 𝕜 rates (dyadicTime (n + 1)) f) =
      resolventL1 𝕜 rates (dyadicTime (n + 1)) (expectationL1 𝕜 m f) at hc
    rw [hc]
    rfl

/-- Finite-coordinate conditional expectation acting on the actual intrinsic graph. -/
def intrinsicExpectation (m : ℕ) :
    (dyadicSystem 𝕜 rates).IntrinsicSpace →L[𝕜] (dyadicSystem 𝕜 rates).IntrinsicSpace :=
  commutingLift (dyadicSystem 𝕜 rates).analysis rfl (expectationL1 𝕜 m)
    (expectation_analysis_commute 𝕜 rates m)

@[simp] theorem evalZero_intrinsicExpectation (m : ℕ) (x : (dyadicSystem 𝕜 rates).IntrinsicSpace) :
    evalZero (dyadicSystem 𝕜 rates).analysis (intrinsicExpectation 𝕜 rates m x) =
      expectationL1 𝕜 m (evalZero (dyadicSystem 𝕜 rates).analysis x) :=
  evalZero_commutingLift _ _ _ _ _

@[simp] theorem coord_intrinsicExpectation (m n : ℕ) (x : (dyadicSystem 𝕜 rates).IntrinsicSpace) :
    coord (dyadicSystem 𝕜 rates).analysis n (intrinsicExpectation 𝕜 rates m x) =
      expectationL1 𝕜 m (coord (dyadicSystem 𝕜 rates).analysis n x) :=
  coord_commutingLift _ _ _ _ _ _

theorem norm_intrinsicExpectation_le (m : ℕ) : ‖intrinsicExpectation 𝕜 rates m‖ ≤ 1 :=
  (norm_commutingLift_le _ _ _ _).trans (norm_expectationL1_le_one 𝕜 m)

theorem intrinsicExpectation_isProjection (m : ℕ) :
    IsProjection (intrinsicExpectation 𝕜 rates m) :=
  commutingLift_isProjection _ _ _ _ (expectationL1_idempotent 𝕜 m)

instance intrinsicExpectation_range_finiteDimensional (m : ℕ) :
    FiniteDimensional 𝕜 (intrinsicExpectation 𝕜 rates m).range :=
  commutingLift_range_finiteDimensional _ _ _ _

theorem intrinsicExpectation_comp_of_le (m n : ℕ) (hmn : m ≤ n) :
    (intrinsicExpectation 𝕜 rates m).comp (intrinsicExpectation 𝕜 rates n) =
      intrinsicExpectation 𝕜 rates m :=
  commutingLift_comp_eq_left _ _ _ _ _ _ (expectationL1_comp_of_le 𝕜 m n hmn)

theorem tendsto_intrinsicExpectation (x : (dyadicSystem 𝕜 rates).IntrinsicSpace) :
    Tendsto (fun m => intrinsicExpectation 𝕜 rates m x) atTop (𝓝 x) :=
  commutingLift_tendsto _ _ (expectationL1 𝕜) (norm_expectationL1_le_one 𝕜)
    (expectation_analysis_commute 𝕜 rates) (tendsto_expectationL1 𝕜) x

/-- One family of genuine contractive finite-rank projections converges to
the identity in precisely the inherited intrinsic norm, for every rate sequence. -/
theorem intrinsic_finite_dimensional_approximation :
    ∃ A : ℕ → (dyadicSystem 𝕜 rates).IntrinsicSpace →L[𝕜] (dyadicSystem 𝕜 rates).IntrinsicSpace,
      (∀ m, ‖A m‖ ≤ 1) ∧ (∀ m, IsProjection (A m)) ∧
      (∀ m, FiniteDimensional 𝕜 (A m).range) ∧
      (∀ m n, m ≤ n → (A m).comp (A n) = A m) ∧
      (∀ x, Tendsto (fun m => A m x) atTop (𝓝 x)) :=
  ⟨intrinsicExpectation 𝕜 rates, norm_intrinsicExpectation_le 𝕜 rates,
    intrinsicExpectation_isProjection 𝕜 rates, intrinsicExpectation_range_finiteDimensional 𝕜 rates,
    intrinsicExpectation_comp_of_le 𝕜 rates, tendsto_intrinsicExpectation 𝕜 rates⟩

end PL1.Noise
