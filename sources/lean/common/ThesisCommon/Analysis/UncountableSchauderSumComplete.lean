import ThesisCommon.Analysis.UncountableSchauderSum
import Mathlib.Topology.MetricSpace.Cauchy

/-! Completeness of the actual vector-valued basis sum. A Cauchy sequence
has Cauchy coordinates in Y and Cauchy norm vectors in X. Their limits satisfy
the defining coefficient relation. Finite coordinate sums then prove norm
convergence, not merely convergence in the product topology.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
namespace UncountableSchauderSum
variable {𝕜 Γ X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {b : NormalizedSchauderFamily 𝕜 Γ X} {hb : b.IsOneUnconditional}

/-- Coordinate evaluation as an actual bounded linear map. -/
def coordinate (n : Γ) : UncountableSchauderSum b hb Y →L[𝕜] Y :=
  LinearMap.mkContinuous
    { toFun := fun y => y n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun y => by simpa only [one_mul] using norm_apply_le y n)

@[simp] theorem coordinate_apply (n : Γ) (y : UncountableSchauderSum b hb Y) :
    coordinate (b := b) (hb := hb) (Y := Y) n y = y n := rfl

theorem norm_coordinate_le (n : Γ) : ‖coordinate (b := b) (hb := hb) (Y := Y) n‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The norm-vector map is contractive for differences, although it is
nonlinear. This controls its behavior on Cauchy sequences. -/
theorem normVector_sub_le (y z : UncountableSchauderSum b hb Y) :
    ‖normVector y - normVector z‖ ≤ ‖y - z‖ := by
  apply b.norm_le_of_coord_le hb
  intro n
  rw [map_sub, coord_normVector, coord_normVector, coord_normVector,
    ← RCLike.ofReal_sub]
  simp only [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), sub_apply]
  exact abs_norm_sub_norm_le _ _

theorem normVector_lipschitz :
    LipschitzWith 1 (normVector : UncountableSchauderSum b hb Y → X) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using normVector_sub_le y z

theorem finite_norm_sum_le (y : UncountableSchauderSum b hb Y) (F : Finset Γ) :
    ‖∑ n ∈ F, (‖y n‖ : 𝕜) • b.vector n‖ ≤ ‖y‖ := by
  simpa only [coord_normVector] using b.finite_projection_norm_le hb F (normVector y)

/-- Lower semicontinuity of the sum norm under coordinatewise convergence.
The limit is required to belong to the actual sum space. -/
theorem norm_le_of_coordinatewise_limit (u : ℕ → UncountableSchauderSum b hb Y)
    (y : UncountableSchauderSum b hb Y) (hu : ∀ n, Tendsto (fun k => u k n) atTop (𝓝 (y n)))
    {C : ℝ} (hC : ∀ᶠ k in atTop, ‖u k‖ ≤ C) : ‖y‖ ≤ C := by
  apply le_of_tendsto' (normVector_expansion y).norm
  intro F
  have ht : Tendsto (fun k => ∑ n ∈ F, (‖u k n‖ : 𝕜) • b.vector n)
      atTop (𝓝 (∑ n ∈ F, (‖y n‖ : 𝕜) • b.vector n)) := by
    apply tendsto_finset_sum
    intro n _
    exact ((RCLike.continuous_ofReal.tendsto _).comp (hu n).norm).smul tendsto_const_nhds
  apply le_of_tendsto ht.norm
  filter_upwards [hC] with k hk
  exact (finite_norm_sum_le (u k) _).trans hk

/-- A vector-valued basis sum of Banach spaces is a Banach space. -/
instance instCompleteSpace [CompleteSpace Y] : CompleteSpace (UncountableSchauderSum b hb Y) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hc (n : Γ) : CauchySeq (fun k => u k n) :=
    (coordinate (b := b) (hb := hb) (Y := Y) n).uniformContinuous.comp_cauchySeq hu
  choose y hy using fun n => cauchySeq_tendsto_of_complete (hc n)
  have hv : CauchySeq (fun k => normVector (u k)) :=
    normVector_lipschitz.uniformContinuous.comp_cauchySeq hu
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hv
  have hxy (n : Γ) : b.coord n x = (‖y n‖ : 𝕜) := by
    have ht := ((b.coord n).continuous.tendsto x).comp hx
    have hs : Tendsto (fun k => (‖u k n‖ : 𝕜)) atTop (𝓝 (‖y n‖ : 𝕜)) :=
      (RCLike.continuous_ofReal.tendsto (‖y n‖)).comp (hy n).norm
    apply tendsto_nhds_unique ht
    simpa only [Function.comp_def, coord_normVector] using hs
  let v : UncountableSchauderSum b hb Y := ⟨y, x, hxy⟩
  refine ⟨v, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro k hk
  rw [dist_eq_norm]
  have hbound : ‖u k - v‖ ≤ ε / 2 := by
    apply norm_le_of_coordinatewise_limit (fun j => u k - u j) (u k - v)
    · intro n
      exact tendsto_const_nhds.sub (hy n)
    · filter_upwards [eventually_ge_atTop N] with j hj
      exact (show ‖u k - u j‖ < ε / 2 from by simpa only [dist_eq_norm] using hN k hk j hj).le
  exact hbound.trans_lt (by linarith)

end UncountableSchauderSum
end ThesisCommon

