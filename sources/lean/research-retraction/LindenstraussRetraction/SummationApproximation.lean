import LindenstraussRetraction.SummationQuotient
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The compatible finite-rank approximations of the summation space

`summationApproximationOperator 𝕜 N` is the paper's `A_N`, with `A_0 = 0`.
For `N = m+1` it retains blocks before `m`, merges the remaining tail into
block `m`, and truncates that block's c₀ coordinates at `N`.
-/

noncomputable section

open Filter Topology
open scoped BigOperators ENNReal

namespace LindenstraussRetraction

universe v
variable (𝕜 : Type v) [RCLike 𝕜]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

-- Cache the canonical instances for the dependent ℓ₁ sum.
local instance : NormedAddCommGroup (SummationSpace 𝕜) := inferInstance
local instance : Module 𝕜 (SummationSpace 𝕜) := inferInstance
local instance : NormedSpace 𝕜 (SummationSpace 𝕜) := inferInstance

/-- The first `N` blocks of an element of the dependent ℓ₁ sum. -/
def summationHead (N : ℕ) (u : SummationSpace 𝕜) : SummationSpace 𝕜 :=
  ∑ m ∈ Finset.range N, lp.single 1 m (u m)

@[simp] theorem summationHead_apply (N k : ℕ) (u : SummationSpace 𝕜) :
    summationHead 𝕜 N u k = if k < N then u k else 0 := by
  simp only [summationHead, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single,
    Finset.sum_pi_single, Finset.mem_range]

theorem norm_summationHead (N : ℕ) (u : SummationSpace 𝕜) :
    ‖summationHead 𝕜 N u‖ = ∑ m ∈ Finset.range N, ‖u m‖ := by
  simpa [summationHead] using lp.norm_sum_single (p := (1 : ℝ≥0∞))
    (by norm_num) (fun m => u m) (Finset.range N)

theorem norm_summationHead_le (N : ℕ) (u : SummationSpace 𝕜) :
    ‖summationHead 𝕜 N u‖ ≤ ‖u‖ := by
  rw [norm_summationHead]
  simpa using lp.sum_rpow_le_norm_rpow (p := (1 : ℝ≥0∞))
    (by norm_num) u (Finset.range N)

theorem norm_summationTail (N : ℕ) (u : SummationSpace 𝕜) :
    ‖u - summationHead 𝕜 N u‖ = ‖u‖ - ‖summationHead 𝕜 N u‖ := by
  rw [norm_summationHead]
  simpa [summationHead] using lp.norm_compl_sum_single (p := (1 : ℝ≥0∞))
    (by norm_num) u (Finset.range N)

def summationHeadOperator (N : ℕ) : SummationSpace 𝕜 →L[𝕜] SummationSpace 𝕜 :=
  ({ toFun := summationHead 𝕜 N
     map_add' := by
       intro u v
       simp only [summationHead, lp.coeFn_add, Pi.add_apply, lp.single_add,
         Finset.sum_add_distrib]
     map_smul' := by
       intro c u
       simp only [summationHead, lp.coeFn_smul, Pi.smul_apply, lp.single_smul,
         Finset.smul_sum, RingHom.id_apply]
     } : SummationSpace 𝕜 →ₗ[𝕜] SummationSpace 𝕜).mkContinuous 1
    (fun u => by simpa only [one_mul] using norm_summationHead_le 𝕜 N u)

@[simp] theorem summationHeadOperator_apply (N : ℕ) (u : SummationSpace 𝕜) :
    summationHeadOperator 𝕜 N u = summationHead 𝕜 N u := rfl

@[simp] theorem summationOperator_head (N : ℕ) (u : SummationSpace 𝕜) :
    summationOperator 𝕜 (summationHead 𝕜 N u) =
      ∑ m ∈ Finset.range N, (u m).val := by
  rw [summationHead, map_sum]
  simp only [summationOperator_single]

/-- The finite-rank operators `A_N` from Section 5. -/
def summationApproximationOperator : ℕ → SummationSpace 𝕜 →L[𝕜] SummationSpace 𝕜
  | 0 => 0
  | m+1 => summationHeadOperator 𝕜 m + (summationApproximateLift 𝕜 m).comp
      ((summationOperator 𝕜).comp (ContinuousLinearMap.id 𝕜 _ - summationHeadOperator 𝕜 m))

@[simp] theorem summationApproximationOperator_zero : summationApproximationOperator 𝕜 0 = 0 := rfl

@[simp] theorem summationApproximationOperator_succ_apply (m : ℕ) (u : SummationSpace 𝕜) :
    summationApproximationOperator 𝕜 (m+1) u = summationHead 𝕜 m u +
      summationApproximateLift 𝕜 m (summationOperator 𝕜 (u - summationHead 𝕜 m u)) := rfl

theorem summationApproximationOperator_norm_apply_le (N : ℕ) (u : SummationSpace 𝕜) :
    ‖summationApproximationOperator 𝕜 N u‖ ≤ ‖u‖ := by
  cases N with
  | zero => simp
  | succ m =>
    rw [summationApproximationOperator_succ_apply]
    calc
      ‖_ + _‖ ≤ ‖summationHead 𝕜 m u‖ +
          ‖summationApproximateLift 𝕜 m (summationOperator 𝕜 (u - summationHead 𝕜 m u))‖ :=
        norm_add_le _ _
      _ ≤ ‖summationHead 𝕜 m u‖ + ‖u - summationHead 𝕜 m u‖ := add_le_add_left
        ((norm_summationApproximateLift_le 𝕜 m _).trans (summationLinear_norm_le 𝕜 _)) _
      _ = ‖u‖ := by rw [norm_summationTail]; ring

theorem norm_summationApproximationOperator_le (N : ℕ) :
    ‖summationApproximationOperator 𝕜 N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using summationApproximationOperator_norm_apply_le 𝕜 N u

theorem summationApproximationOperator_error_le (m : ℕ) (u : SummationSpace 𝕜) :
    ‖summationApproximationOperator 𝕜 (m+1) u - u‖ ≤ 2 * ‖u - summationHead 𝕜 m u‖ := by
  rw [summationApproximationOperator_succ_apply]
  have heq : summationHead 𝕜 m u +
      summationApproximateLift 𝕜 m (summationOperator 𝕜 (u - summationHead 𝕜 m u)) - u =
      summationApproximateLift 𝕜 m (summationOperator 𝕜 (u - summationHead 𝕜 m u)) -
        (u - summationHead 𝕜 m u) := by abel
  rw [heq]
  calc
    _ ≤ ‖summationApproximateLift 𝕜 m (summationOperator 𝕜 (u - summationHead 𝕜 m u))‖ +
        ‖u - summationHead 𝕜 m u‖ := norm_sub_le _ _
    _ ≤ ‖u - summationHead 𝕜 m u‖ + ‖u - summationHead 𝕜 m u‖ := add_le_add_right
      ((norm_summationApproximateLift_le 𝕜 m _).trans (summationLinear_norm_le 𝕜 _)) _
    _ = 2 * ‖u - summationHead 𝕜 m u‖ := by ring

theorem summationHead_tendsto (u : SummationSpace 𝕜) :
    Tendsto (fun N => summationHead 𝕜 N u) atTop (𝓝 u) :=
  (lp.hasSum_single (by simp) u).tendsto_sum_nat

theorem summationApproximationOperator_tendsto (u : SummationSpace 𝕜) :
    Tendsto (fun N => summationApproximationOperator 𝕜 N u) atTop (𝓝 u) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun N => norm_nonneg _) (summationApproximationOperator_error_le 𝕜 · u)
  have ht : Tendsto (fun N => ‖u - summationHead 𝕜 N u‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => u) atTop (𝓝 u)).sub
      (summationHead_tendsto 𝕜 u)).norm
  simpa only [mul_zero] using tendsto_const_nhds.mul ht

theorem c0Truncation_fix_of_le {m N : ℕ} (h : m+1 ≤ N)
    (x : FiniteCoordinateSpace 𝕜 m) : c0Truncation 𝕜 N x.val = x.val := by
  ext k
  by_cases hk : k < N
  · simp [hk]
  · simp [hk, x.property k (h.trans (Nat.le_of_not_gt hk))]

theorem summationOperator_head_truncation (m : ℕ) (u : SummationSpace 𝕜) :
    c0Truncation 𝕜 (m+1) (summationOperator 𝕜 (summationHead 𝕜 m u)) =
      summationOperator 𝕜 (summationHead 𝕜 m u) := by
  rw [summationOperator_head]
  change c0TruncationOperator 𝕜 (m+1) (∑ k ∈ Finset.range m, (u k).val) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact c0Truncation_fix_of_le 𝕜 (Nat.succ_le_succ (Finset.mem_range.mp hk).le) (u k)

theorem summationOperator_approximation (N : ℕ) (u : SummationSpace 𝕜) :
    summationOperator 𝕜 (summationApproximationOperator 𝕜 N u) =
      c0Truncation 𝕜 N (summationOperator 𝕜 u) := by
  cases N with
  | zero =>
    simp only [summationApproximationOperator_zero, ContinuousLinearMap.zero_apply, map_zero]
    ext k
    simp
  | succ m =>
    rw [summationApproximationOperator_succ_apply, map_add,
      summationOperator_approximateLift, map_sub]
    change summationOperator 𝕜 (summationHead 𝕜 m u) +
      c0TruncationOperator 𝕜 (m+1)
        (summationOperator 𝕜 u - summationOperator 𝕜 (summationHead 𝕜 m u)) = _
    rw [map_sub]
    simp only [c0TruncationOperator_apply]
    rw [summationOperator_head_truncation]
    abel

theorem summationApproximationOperator_apply_of_lt (m k : ℕ) (hk : k < m)
    (u : SummationSpace 𝕜) : summationApproximationOperator 𝕜 (m+1) u k = u k := by
  rw [summationApproximationOperator_succ_apply]
  simp [summationHead_apply, hk, (ne_of_lt hk), summationApproximateLift_apply]

theorem summationApproximationOperator_apply_eq_zero (N k : ℕ) (hk : N ≤ k)
    (u : SummationSpace 𝕜) : summationApproximationOperator 𝕜 N u k = 0 := by
  cases N with
  | zero => simp
  | succ m =>
    rw [summationApproximationOperator_succ_apply]
    have hkm : k ≠ m := ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self m) hk)
    have hnot : ¬ k < m := not_lt.mpr ((Nat.le_succ m).trans hk)
    simp [summationHead_apply, hnot, hkm, summationApproximateLift_apply]

theorem summationHead_approximation_of_le (M n : ℕ) (h : M ≤ n)
    (u : SummationSpace 𝕜) :
    summationHead 𝕜 M (summationApproximationOperator 𝕜 (n+1) u) = summationHead 𝕜 M u := by
  unfold summationHead
  apply Finset.sum_congr rfl
  intro k hk
  rw [summationApproximationOperator_apply_of_lt 𝕜 n k ((Finset.mem_range.mp hk).trans_le h)]

theorem summationApproximationOperator_fix (N : ℕ) (u : SummationSpace 𝕜)
    (hu : ∀ k, N ≤ k → u k = 0) : summationApproximationOperator 𝕜 N u = u := by
  cases N with
  | zero =>
    apply lp.ext
    funext k
    simpa using (hu k (Nat.zero_le k)).symm
  | succ m =>
    have htail : u - summationHead 𝕜 m u = lp.single 1 m (u m) := by
      apply lp.ext
      funext k
      by_cases hkm : k = m
      · subst k; simp
      · by_cases hk : k < m
        · simp [summationHead_apply, hk, hkm]
        · have hum : u k = 0 := hu k (by omega)
          simp [summationHead_apply, hk, hkm, hum]
    have hlift : summationApproximateLift 𝕜 m (summationOperator 𝕜
        (u - summationHead 𝕜 m u)) = lp.single 1 m (u m) := by
      rw [htail, summationOperator_single, summationApproximateLift_apply]
      congr 1
      apply Subtype.ext
      exact c0Truncation_fix 𝕜 m (u m)
    rw [summationApproximationOperator_succ_apply, hlift, ← htail]
    abel

theorem summationApproximateLift_truncation {m N : ℕ} (h : m+1 ≤ N) (x : C0 𝕜) :
    summationApproximateLift 𝕜 m (c0Truncation 𝕜 N x) = summationApproximateLift 𝕜 m x := by
  rw [summationApproximateLift_apply, summationApproximateLift_apply]
  congr 1
  apply Subtype.ext
  change c0Truncation 𝕜 (m+1) (c0Truncation 𝕜 N x) = c0Truncation 𝕜 (m+1) x
  rw [c0Truncation_comp, min_eq_left h]

theorem summationApproximationOperator_comp_small (M N : ℕ) (h : M ≤ N)
    (u : SummationSpace 𝕜) :
    summationApproximationOperator 𝕜 M (summationApproximationOperator 𝕜 N u) =
      summationApproximationOperator 𝕜 M u := by
  cases M with
  | zero => simp
  | succ m =>
    cases N with
    | zero => omega
    | succ n =>
      have hmn : m ≤ n := Nat.le_of_succ_le_succ h
      rw [summationApproximationOperator_succ_apply,
        summationHead_approximation_of_le 𝕜 m n hmn, map_sub,
        summationOperator_approximation, map_sub,
        summationApproximateLift_truncation 𝕜 h]
      rw [summationApproximationOperator_succ_apply, map_sub, map_sub]

theorem summationApproximationOperator_comp (N M : ℕ) :
    (summationApproximationOperator 𝕜 N).comp (summationApproximationOperator 𝕜 M) =
      summationApproximationOperator 𝕜 (min N M) := by
  apply ContinuousLinearMap.ext
  intro u
  change summationApproximationOperator 𝕜 N (summationApproximationOperator 𝕜 M u) = _
  rcases le_total N M with h | h
  · rw [min_eq_left h]
    exact summationApproximationOperator_comp_small 𝕜 N M h u
  · rw [min_eq_right h]
    apply summationApproximationOperator_fix
    intro k hk
    exact summationApproximationOperator_apply_eq_zero 𝕜 M k (h.trans hk) u

def finiteBlockSubmodule (N : ℕ) : Submodule 𝕜 (SummationSpace 𝕜) where
  carrier := {u | ∀ k, N ≤ k → u k = 0}
  zero_mem' := by intro k hk; rfl
  add_mem' := by intro u v hu hv k hk; simp [hu k hk, hv k hk]
  smul_mem' := by intro c u hu k hk; simp [hu k hk]

def finiteBlockRestriction (N : ℕ) :
    finiteBlockSubmodule 𝕜 N →ₗ[𝕜] (∀ k : Fin N, FiniteCoordinateSpace 𝕜 k.val) where
  toFun u k := u.val k.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finiteBlockRestriction_injective (N : ℕ) :
    Function.Injective (finiteBlockRestriction 𝕜 N) := by
  intro u v h
  apply Subtype.ext
  apply lp.ext
  funext k
  by_cases hk : k < N
  · exact congrFun h ⟨k, hk⟩
  · rw [u.property k (Nat.le_of_not_gt hk), v.property k (Nat.le_of_not_gt hk)]

instance finiteBlockSubmodule_finiteDimensional (N : ℕ) :
    FiniteDimensional 𝕜 (finiteBlockSubmodule 𝕜 N) :=
  FiniteDimensional.of_injective (finiteBlockRestriction 𝕜 N)
    (finiteBlockRestriction_injective 𝕜 N)

theorem summationApproximationOperator_finite_rank (N : ℕ) :
    FiniteDimensional 𝕜 (LinearMap.range (summationApproximationOperator 𝕜 N).toLinearMap) := by
  have hle : LinearMap.range (summationApproximationOperator 𝕜 N).toLinearMap ≤
      finiteBlockSubmodule 𝕜 N := by
    rintro u ⟨v, rfl⟩ k hk
    exact summationApproximationOperator_apply_eq_zero 𝕜 N k hk v
  exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end LindenstraussRetraction
