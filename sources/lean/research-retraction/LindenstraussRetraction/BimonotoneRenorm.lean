import LindenstraussRetraction.BasisTransport
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! The equivalent interval norm that makes a bounded Schauder basis bimonotone.
We realize the norm as a closed range in a bounded family space, so all normed
space and completeness structures are inherited from Mathlib. -/

noncomputable section
open Filter Topology
open scoped ENNReal

namespace LindenstraussRetraction

universe u v
variable {𝕜 : Type v} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (b : SchauderBasis 𝕜 X) (B : ℝ) (hB : 0 ≤ B)
variable (hP : ∀ N, ‖b.partialSum N‖ ≤ B)

include hP in
theorem basis_interval_bound (a c : ℕ) (x : X) :
    ‖b.partialSum c x - b.partialSum a x‖ ≤ (2*B)*‖x‖ := by
  calc
    ‖b.partialSum c x - b.partialSum a x‖ ≤ ‖b.partialSum c x‖ + ‖b.partialSum a x‖ :=
      norm_sub_le _ _
    _ ≤ B*‖x‖ + B*‖x‖ := add_le_add
      ((b.partialSum c).le_opNorm x |>.trans
        (mul_le_mul_of_nonneg_right (hP c) (norm_nonneg x)))
      ((b.partialSum a).le_opNorm x |>.trans
        (mul_le_mul_of_nonneg_right (hP a) (norm_nonneg x)))
    _ = (2*B)*‖x‖ := by ring

def basisIntervalLinear : X →ₗ[𝕜] lp (fun _ : ℕ × ℕ => X) ∞ where
  toFun x := ⟨fun p => b.partialSum p.2 x - b.partialSum p.1 x,
    memℓp_infty ⟨(2*B)*‖x‖, by
      rintro _ ⟨p, rfl⟩
      exact basis_interval_bound b B hP p.1 p.2 x⟩⟩
  map_add' x y := by
    ext p
    change b.partialSum p.2 (x+y) - b.partialSum p.1 (x+y) =
      (b.partialSum p.2 x-b.partialSum p.1 x) + (b.partialSum p.2 y-b.partialSum p.1 y)
    rw [map_add, map_add]
    abel
  map_smul' a x := by
    ext p
    change b.partialSum p.2 (a • x) - b.partialSum p.1 (a • x) =
      a • (b.partialSum p.2 x-b.partialSum p.1 x)
    rw [map_smul, map_smul, smul_sub]

def basisIntervalEmbedding : X →L[𝕜] lp (fun _ : ℕ × ℕ => X) ∞ :=
  (basisIntervalLinear b B hP).mkContinuous (2*B) (by
    intro x
    apply lp.norm_le_of_forall_le (mul_nonneg (mul_nonneg (by norm_num) hB) (norm_nonneg x))
    intro p
    exact basis_interval_bound b B hP p.1 p.2 x)

@[simp] theorem basisIntervalEmbedding_apply (x : X) (a c : ℕ) :
    basisIntervalEmbedding b B hB hP x (a,c) = b.partialSum c x - b.partialSum a x := rfl

theorem basisIntervalEmbedding_norm_lower (x : X) :
    ‖x‖ ≤ ‖basisIntervalEmbedding b B hB hP x‖ := by
  apply le_of_tendsto (b.tendsto_partialSum x |>.norm)
  apply Filter.Eventually.of_forall
  intro N
  have h := lp.norm_apply_le_norm ENNReal.top_ne_zero
    (basisIntervalEmbedding b B hB hP x) (0,N)
  simpa only [basisIntervalEmbedding_apply, b.partialSum_zero,
    ContinuousLinearMap.zero_apply, sub_zero] using h

theorem basisIntervalEmbedding_antilipschitz :
    AntilipschitzWith 1 (basisIntervalEmbedding b B hB hP) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, map_sub] using
    basisIntervalEmbedding_norm_lower b B hB hP (x-y)

/-- The carrier with the equivalent norm `sup_{a,c} ‖P_c x-P_a x‖`. -/
abbrev BimonotoneSpace : Type u := LinearMap.range (basisIntervalEmbedding b B hB hP).toLinearMap

theorem bimonotoneSpace_isClosed [CompleteSpace X] :
    IsClosed ((LinearMap.range (basisIntervalEmbedding b B hB hP).toLinearMap) :
      Set (lp (fun _ : ℕ × ℕ => X) ∞)) :=
  (basisIntervalEmbedding_antilipschitz b B hB hP).isClosed_range
    (basisIntervalEmbedding b B hB hP).uniformContinuous

instance bimonotoneSpace_complete [CompleteSpace X] :
    CompleteSpace (BimonotoneSpace b B hB hP) :=
  (bimonotoneSpace_isClosed b B hB hP).completeSpace_coe

def bimonotoneEquiv [CompleteSpace X] : X ≃L[𝕜] BimonotoneSpace b B hB hP :=
  (basisIntervalEmbedding b B hB hP).equivRange
    (basisIntervalEmbedding_antilipschitz b B hB hP).injective
    (bimonotoneSpace_isClosed b B hB hP)

@[simp] theorem bimonotoneEquiv_coe [CompleteSpace X] (x : X) :
    (bimonotoneEquiv b B hB hP x).val = basisIntervalEmbedding b B hB hP x := rfl

theorem basisIntervalEmbedding_prefix_norm_le (N : ℕ) (x : X) :
    ‖basisIntervalEmbedding b B hB hP (b.partialSum N x)‖ ≤
      ‖basisIntervalEmbedding b B hB hP x‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  rintro ⟨a,c⟩
  have hp (m : ℕ) : b.partialSum m (b.partialSum N x) = b.partialSum (min m N) x :=
    congrArg (fun T : X →L[𝕜] X => T x) (b.partialSum_comp m N)
  rw [basisIntervalEmbedding_apply, hp c, hp a]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero
    (basisIntervalEmbedding b B hB hP x) (min a N, min c N)

theorem basisIntervalEmbedding_tail_norm_le (N : ℕ) (x : X) :
    ‖basisIntervalEmbedding b B hB hP (x-b.partialSum N x)‖ ≤
      ‖basisIntervalEmbedding b B hB hP x‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  rintro ⟨a,c⟩
  have hp (m : ℕ) : b.partialSum m (b.partialSum N x) = b.partialSum (min m N) x :=
    congrArg (fun T : X →L[𝕜] X => T x) (b.partialSum_comp m N)
  have hm (m : ℕ) : b.partialSum m x - b.partialSum (min m N) x =
      b.partialSum (max m N) x - b.partialSum N x := by
    rcases le_total m N with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h, max_eq_left h]
  rw [basisIntervalEmbedding_apply, map_sub, map_sub, hp c, hp a, hm c, hm a]
  have he : (b.partialSum (max c N) x - b.partialSum N x) -
      (b.partialSum (max a N) x - b.partialSum N x) =
      b.partialSum (max c N) x - b.partialSum (max a N) x := by abel
  rw [he]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero
    (basisIntervalEmbedding b B hB hP x) (max a N, max c N)

def bimonotoneBasis [CompleteSpace X] : SchauderBasis 𝕜 (BimonotoneSpace b B hB hP) :=
  b.map (bimonotoneEquiv b B hB hP)

theorem bimonotoneBasis_isBimonotone [CompleteSpace X] :
    (bimonotoneBasis b B hB hP).IsBimonotone := by
  let e := bimonotoneEquiv b B hB hP
  constructor
  · intro N
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    obtain ⟨x,rfl⟩ := e.surjective z
    simp only [one_mul]
    change ‖(b.map e).partialSum N (e x)‖ ≤ ‖e x‖
    rw [SchauderBasis.map_partialSum_apply, e.symm_apply_apply]
    exact basisIntervalEmbedding_prefix_norm_le b B hB hP N x
  · intro N
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    obtain ⟨x,rfl⟩ := e.surjective z
    simp only [one_mul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    change ‖e x - (b.map e).partialSum N (e x)‖ ≤ ‖e x‖
    rw [SchauderBasis.map_partialSum_apply, e.symm_apply_apply, ← map_sub]
    exact basisIntervalEmbedding_tail_norm_le b B hB hP N x

theorem bimonotoneSpace_separable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] :
    TopologicalSpace.SeparableSpace (BimonotoneSpace b B hB hP) :=
  (bimonotoneEquiv b B hB hP).surjective.denseRange.separableSpace
    (bimonotoneEquiv b B hB hP).continuous

end LindenstraussRetraction
