import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Local exponential coordinates for orthogonal orbit slices

The inverse function theorem supplies an actual locally Lipschitz logarithm
near the identity of a real Banach algebra. In a Banach star algebra it takes
unitaries to skew-adjoint elements. This is the local coordinate step for the
explicit matrix-exponential orbit-slice route.
-/

namespace BanachIsometric

open Filter Set
open scoped Topology NNReal

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

private theorem exponential_strictDerivative :
    HasStrictFDerivAt (NormedSpace.exp ℝ : A → A)
      (ContinuousLinearEquiv.refl ℝ A : A →L[ℝ] A) 0 := by
  simpa using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))

/-- The actual local inverse supplied by the inverse function theorem. -/
noncomputable def localAlgebraLog : A → A :=
  (exponential_strictDerivative A).localInverse (NormedSpace.exp ℝ)
    (ContinuousLinearEquiv.refl ℝ A) 0

theorem localAlgebraLog_one : localAlgebraLog A 1 = 0 := by
  simpa only [NormedSpace.exp_zero, localAlgebraLog] using
    (exponential_strictDerivative A).localInverse_apply_image

theorem localAlgebraLog_exp :
    ∀ᶠ x : A in 𝓝 0, localAlgebraLog A (NormedSpace.exp ℝ x) = x :=
  (exponential_strictDerivative A).eventually_left_inverse

theorem exp_localAlgebraLog :
    ∀ᶠ x : A in 𝓝 1, NormedSpace.exp ℝ (localAlgebraLog A x) = x := by
  simpa only [NormedSpace.exp_zero, localAlgebraLog] using
    (exponential_strictDerivative A).eventually_right_inverse

theorem localAlgebraLog_hasStrictFDerivAt :
    HasStrictFDerivAt (localAlgebraLog A)
      (ContinuousLinearMap.id ℝ A) 1 := by
  simpa only [NormedSpace.exp_zero, localAlgebraLog] using
    (exponential_strictDerivative A).to_localInverse

theorem localAlgebraLog_continuousAt : ContinuousAt (localAlgebraLog A) 1 :=
  (localAlgebraLog_hasStrictFDerivAt A).continuousAt

/-- Two-point local Lipschitz regularity, rather than mere continuity. -/
theorem localAlgebraLog_lipschitzOn_nhds :
    ∃ U ∈ 𝓝 (1 : A), ∃ L : ℝ≥0, LipschitzOnWith L (localAlgebraLog A) U := by
  obtain ⟨U, hU, happrox⟩ :=
    (localAlgebraLog_hasStrictFDerivAt A).approximates_deriv_on_nhds
      (c := 1) (Or.inr zero_lt_one)
  refine ⟨U, hU, ‖ContinuousLinearMap.id ℝ A‖₊ + 1, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  exact happrox.lipschitz.dist_le_mul (⟨x, hx⟩ : U) (⟨y, hy⟩ : U)

section Star

variable [StarRing A] [ContinuousStar A]

/-- Local logarithms of unitaries are genuinely skew-adjoint. This is derived
from local injectivity of the exponential, not assumed as spectral calculus. -/
theorem localAlgebraLog_skew_of_unitary :
    ∀ᶠ R : A in 𝓝 1, R ∈ unitary A → star (localAlgebraLog A R) = -localAlgebraLog A R := by
  let chart := (exponential_strictDerivative A).toOpenPartialHomeomorph (NormedSpace.exp ℝ)
  have hsource : (0 : A) ∈ chart.source :=
    (exponential_strictDerivative A).mem_toOpenPartialHomeomorph_source
  have hsourceN : chart.source ∈ 𝓝 (0 : A) := chart.open_source.mem_nhds hsource
  have hstar : Tendsto (fun R : A => star (localAlgebraLog A R)) (𝓝 1) (𝓝 0) := by
    simpa only [Function.comp_apply, localAlgebraLog_one, star_zero] using
      (continuous_star.continuousAt.comp (localAlgebraLog_continuousAt A)).tendsto
  have hneg : Tendsto (fun R : A => -localAlgebraLog A R) (𝓝 1) (𝓝 0) := by
    simpa only [localAlgebraLog_one, neg_zero] using
      (localAlgebraLog_continuousAt A).neg.tendsto
  filter_upwards [exp_localAlgebraLog A, hstar.eventually hsourceN, hneg.eventually hsourceN]
    with R hR hstarR hnegR hunitary
  apply chart.injOn hstarR hnegR
  change NormedSpace.exp ℝ (star (localAlgebraLog A R)) =
    NormedSpace.exp ℝ (-localAlgebraLog A R)
  have hleft : NormedSpace.exp ℝ (star (localAlgebraLog A R)) * R = 1 := by
    rw [← NormedSpace.star_exp, hR]
    exact (unitary.mem_iff.mp hunitary).1
  have hright : R * NormedSpace.exp ℝ (-localAlgebraLog A R) = 1 := by
    conv_lhs => lhs; rw [← hR]
    rw [← NormedSpace.exp_add_of_commute (Commute.refl (localAlgebraLog A R)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  calc
    NormedSpace.exp ℝ (star (localAlgebraLog A R)) =
        NormedSpace.exp ℝ (star (localAlgebraLog A R)) *
          (R * NormedSpace.exp ℝ (-localAlgebraLog A R)) := by rw [hright, mul_one]
    _ = (NormedSpace.exp ℝ (star (localAlgebraLog A R)) * R) *
        NormedSpace.exp ℝ (-localAlgebraLog A R) := (mul_assoc _ _ _).symm
    _ = NormedSpace.exp ℝ (-localAlgebraLog A R) := by rw [hleft, one_mul]

theorem unitary_iff_localAlgebraLog_skew :
    ∀ᶠ R : A in 𝓝 1, R ∈ unitary A ↔ localAlgebraLog A R ∈ skewAdjoint A := by
  filter_upwards [localAlgebraLog_skew_of_unitary A, exp_localAlgebraLog A] with R hskew hR
  constructor
  · intro hu
    exact skewAdjoint.mem_iff.mpr (hskew hu)
  · intro hx
    rw [← hR]
    exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ hx

end Star

end BanachIsometric
