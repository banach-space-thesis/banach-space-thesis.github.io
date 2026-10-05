import Posets.WolfeOperatorRows
import Posets.WolfeMassBounds
import JLMS.DisjointWeakNull

/-! Continuous lifted evaluations supplied by an actual identity factorization.
This proves the lifting and norming input to Wolfe necessity. It does not assert
that arbitrary images of disjoint functions have disjoint supports. That further
selection step is needed for the transfinite preservation criterion. -/

noncomputable section
open Set Filter Topology
namespace Posets

variable {𝕜 K L X : Type*} [RCLike 𝕜]
    [TopologicalSpace K] [TopologicalSpace L]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]

local instance wolfeNecessaryLiftDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeNecessaryLiftDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeNecessaryLiftRangeGroup :
    NormedAddCommGroup (X →L[𝕜] JLMS.CZero 𝕜 L) := inferInstance
local instance wolfeNecessaryLiftRangeSpace :
    NormedSpace 𝕜 (X →L[𝕜] JLMS.CZero 𝕜 L) := inferInstance

def wolfeFactorizationLift (T : JLMS.CZero 𝕜 K →L[𝕜] X)
    (R : X →L[𝕜] JLMS.CZero 𝕜 L) (c : 𝕜) (x : L) :
    WeakDual 𝕜 (JLMS.CZero 𝕜 K) :=
  weakStarAdjoint T (weakStarAdjoint (c • R) (wolfeDirac x))

@[simp] theorem wolfeFactorizationLift_apply (T : JLMS.CZero 𝕜 K →L[𝕜] X)
    (R : X →L[𝕜] JLMS.CZero 𝕜 L) (c : 𝕜) (x : L) (f : JLMS.CZero 𝕜 K) :
    wolfeFactorizationLift T R c x f = c * R (T f) x := rfl

theorem wolfeFactorizationLift_continuous (T : JLMS.CZero 𝕜 K →L[𝕜] X)
    (R : X →L[𝕜] JLMS.CZero 𝕜 L) (c : 𝕜) :
    Continuous (wolfeFactorizationLift T R c) :=
  (weakStarAdjoint_continuous T).comp
    ((weakStarAdjoint_continuous (c • R)).comp wolfeDirac_continuous)

theorem wolfeFactorizationLift_mem_adjointUnitBall
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (c : 𝕜) (hc : ‖c‖ * ‖R‖ ≤ 1) (x : L) :
    wolfeFactorizationLift T R c x ∈ adjointUnitBall T := by
  refine ⟨weakStarAdjoint (c • R) (wolfeDirac x), ?_, rfl⟩
  change ‖(JLMS.evaluation x).comp (c • R) - 0‖ ≤ 1
  rw [sub_zero]
  calc
    ‖(JLMS.evaluation x).comp (c • R)‖ ≤
        ‖JLMS.evaluation (𝕜 := 𝕜) x‖ * ‖c • R‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖c • R‖ := mul_le_mul_of_nonneg_right
      (JLMS.norm_evaluation_le (𝕜 := 𝕜) x) (norm_nonneg (c • R))
    _ ≤ 1 := by simpa only [one_mul, norm_smul] using hc

theorem wolfeFactorizationLift_norm_le
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (c : 𝕜) (hc : ‖c‖ * ‖R‖ ≤ 1) (x : L) :
    ‖WeakDual.toStrongDual (wolfeFactorizationLift T R c x)‖ ≤ ‖T‖ := by
  obtain ⟨φ, hφ, heq⟩ := wolfeFactorizationLift_mem_adjointUnitBall T R c hc x
  rw [← heq]
  have hn : ‖WeakDual.toStrongDual φ‖ ≤ 1 := by
    simpa only [weakStarUnitBall, mem_preimage, Metric.mem_closedBall, dist_zero_right] using hφ
  exact (ContinuousLinearMap.opNorm_comp_le _ T).trans
    (by simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg T))

theorem wolfeFactorizationLift_pullback
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (x : L) :
    weakStarAdjoint S (wolfeFactorizationLift T R c x) = c • wolfeDirac x := by
  apply DFunLike.ext
  intro f
  have hf : R (T (S f)) = f := DFunLike.congr_fun hfactor f
  simp only [weakStarAdjoint_apply, wolfeFactorizationLift_apply, hf]
  rfl

theorem wolfeFactorizationLift_norming
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (x : L) (f : JLMS.CZero 𝕜 L) (hf : f x = 1) :
    wolfeFactorizationLift T R c x (S f) = c := by
  have h := DFunLike.congr_fun (wolfeFactorizationLift_pullback T R S hfactor c x) f
  change wolfeFactorizationLift T R c x (S f) = c * f x at h
  simpa only [hf, mul_one] using h

theorem exists_wolfeFactorizationLift_scale (R : X →L[𝕜] JLMS.CZero 𝕜 L) :
    ∃ c : 𝕜, c ≠ 0 ∧ ‖c‖ * ‖R‖ ≤ 1 := by
  let c : 𝕜 := ((‖R‖ + 1 : ℝ) : 𝕜)⁻¹
  have hr : 0 < ‖R‖ + 1 := by positivity
  refine ⟨c, inv_ne_zero (by exact_mod_cast hr.ne'), ?_⟩
  have hn : ‖c‖ = (‖R‖ + 1)⁻¹ := by
    simp only [c, norm_inv, RCLike.norm_ofReal, abs_of_pos hr]
  rw [hn, inv_mul_le_iff₀ hr]
  linarith

end Posets
