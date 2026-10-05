import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Sequences

/-! The concrete c₀ sum of a dependent family, as the subspace of the
uniformly bounded product whose coordinate norms vanish along the cofinite filter. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] {P : Type*}
variable (X : P → Type*) [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]

def cZeroSumSubmodule : Submodule 𝕜 (lp X ∞) where
  carrier := {x | Tendsto (fun p => ‖x p‖) cofinite (𝓝 0)}
  zero_mem' := by simpa using (tendsto_const_nhds : Tendsto (fun _ : P => (0 : ℝ)) cofinite (𝓝 0))
  add_mem' := by
    intro f g hf hg
    apply squeeze_zero (fun p => norm_nonneg _) (fun p => norm_add_le (f p) (g p))
    simpa using hf.add hg
  smul_mem' := by
    intro a f hf
    change Tendsto (fun p => ‖(a • f) p‖) cofinite (𝓝 0)
    simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, mul_zero] using
      (tendsto_const_nhds.mul hf : Tendsto (fun p => ‖a‖ * ‖f p‖) cofinite (𝓝 (‖a‖ * 0)))

abbrev DependentCZeroSum := cZeroSumSubmodule 𝕜 X

/-- Uniform limits preserve vanishing at infinity. -/
theorem cZeroSum_isClosed : IsClosed (cZeroSumSubmodule 𝕜 X : Set (lp X ∞)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro F f hF hlim
  change Tendsto (fun p => ‖f p‖) cofinite (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := (hlim.eventually (Metric.ball_mem_nhds f (half_pos hε))).exists
  have hcoord := (hF n).eventually (Metric.ball_mem_nhds 0 (half_pos hε))
  filter_upwards [hcoord] with i hi
  calc
    dist ‖f i‖ 0 = ‖f i‖ := by simp
    _ ≤ ‖f i - F n i‖ + ‖F n i‖ := by
      simpa [add_comm, norm_sub_rev] using norm_le_insert (F n i) (f i)
    _ ≤ ‖f - F n‖ + ‖F n i‖ :=
      add_le_add_right (lp.norm_apply_le_norm ENNReal.top_ne_zero (f - F n) i) _
    _ < ε / 2 + ε / 2 := add_lt_add
      (by simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hn)
      (by simpa [Metric.mem_ball] using hi)
    _ = ε := add_halves ε

instance [∀ p, CompleteSpace (X p)] : CompleteSpace (DependentCZeroSum 𝕜 X) :=
  (cZeroSum_isClosed 𝕜 X).completeSpace_coe

/-- The actual bounded coordinate projection πₚ. -/
def sumProjection (p : P) : DependentCZeroSum 𝕜 X →L[𝕜] X p :=
  ({toFun := fun x => x.val p
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl} : DependentCZeroSum 𝕜 X →ₗ[𝕜] X p).mkContinuous 1
    (fun x => by simpa using lp.norm_apply_le_norm ENNReal.top_ne_zero x.val p)

/-- The coordinate injection jₚ, proved to take values in the genuine c₀ sum. -/
def sumInjection (p : P) : X p →L[𝕜] DependentCZeroSum 𝕜 X := by
  classical
  refine (lp.singleContinuousLinearMap 𝕜 X ∞ p).codRestrict (cZeroSumSubmodule 𝕜 X) ?_
  intro x
  change Tendsto (fun q => ‖lp.single ∞ p x q‖) cofinite (𝓝 0)
  apply tendsto_const_nhds.congr'
  filter_upwards [(Set.finite_singleton p).compl_mem_cofinite] with q hq
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq
  simp [Pi.single_eq_of_ne hq]

def operatorBlock {Q : Type*} (Z : Q → Type*)
    [∀ q, NormedAddCommGroup (Z q)] [∀ q, NormedSpace 𝕜 (Z q)]
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z) (s : Q) (t : P) : X t →L[𝕜] Z s :=
  (sumProjection 𝕜 Z s).comp (T.comp (sumInjection 𝕜 X t))

end ThesisCommon
