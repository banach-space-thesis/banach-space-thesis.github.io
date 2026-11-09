import LindenstraussRetraction.C0SumCoordinates
import LindenstraussRetraction.SchauderBasis

/-! A monotone finite-dimensional decomposition of a dependent c₀ sum. -/

noncomputable section
open Filter Topology
open scoped ENNReal

namespace LindenstraussRetraction

universe u v
variable (𝕜 : Type v) [RCLike 𝕜]
variable (E : ℕ → Type u) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]
variable (b : ∀ n, MonotoneFDD 𝕜 (E n))

/-- Retain the first `N` coordinates and apply each coordinate's `N`th
finite-dimensional projection. -/
def c0SumFDDProjection (N : ℕ) : C0Sum 𝕜 E →L[𝕜] C0Sum 𝕜 E :=
  ∑ n ∈ Finset.range N, (c0SumSingle 𝕜 E n).comp
    (((b n).projection N).comp (c0SumCoordinate 𝕜 E n))

theorem c0SumFDDProjection_apply (N : ℕ) (x : C0Sum 𝕜 E) (m : ℕ) :
    (c0SumFDDProjection 𝕜 E b N x).val m =
      if m < N then (b m).projection N (x.val m) else 0 := by
  classical
  change c0SumCoordinate 𝕜 E m (c0SumFDDProjection 𝕜 E b N x) = _
  simp only [c0SumFDDProjection, ContinuousLinearMap.sum_apply, map_sum,
    ContinuousLinearMap.comp_apply, c0SumCoordinate_apply]
  by_cases hm : m < N
  · rw [if_pos hm, Finset.sum_eq_single m]
    · exact lp.single_apply_self ∞ m _
    · intro n _ hnm
      exact lp.single_apply_ne ∞ n _ (Ne.symm hnm)
    · intro h
      exact (h (Finset.mem_range.mpr hm)).elim
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro n hn
    apply lp.single_apply_ne
    intro h
    exact hm (h ▸ Finset.mem_range.mp hn)

theorem coordinateFDD_norm_apply_le (n N : ℕ) (x : E n) :
    ‖(b n).projection N x‖ ≤ ‖x‖ :=
  ((b n).projection N).le_opNorm x |>.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ((b n).contractive N) (norm_nonneg x))

theorem c0SumFDDProjection_norm_apply_le (N : ℕ) (x : C0Sum 𝕜 E) :
    ‖c0SumFDDProjection 𝕜 E b N x‖ ≤ ‖x‖ := by
  apply c0Sum_norm_le 𝕜 E (norm_nonneg x)
  intro n
  rw [c0SumFDDProjection_apply]
  split_ifs
  · exact (coordinateFDD_norm_apply_le 𝕜 E b n N _).trans (c0Sum_norm_coordinate_le 𝕜 E x n)
  · simp

theorem c0SumFDDProjection_norm_le (N : ℕ) : ‖c0SumFDDProjection 𝕜 E b N‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
    intro x
    simpa only [one_mul] using c0SumFDDProjection_norm_apply_le 𝕜 E b N x)

theorem c0SumFDDProjection_zero : c0SumFDDProjection 𝕜 E b 0 = 0 := by
  simp [c0SumFDDProjection]

theorem c0SumFDDProjection_comp (N M : ℕ) :
    (c0SumFDDProjection 𝕜 E b N).comp (c0SumFDDProjection 𝕜 E b M) =
      c0SumFDDProjection 𝕜 E b (min N M) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  apply lp.ext
  funext m
  change (c0SumFDDProjection 𝕜 E b N (c0SumFDDProjection 𝕜 E b M x)).val m = _
  rw [c0SumFDDProjection_apply, c0SumFDDProjection_apply, c0SumFDDProjection_apply]
  by_cases hmN : m < N <;> by_cases hmM : m < M
  · simp only [hmN, hmM, lt_min_iff.mpr ⟨hmN, hmM⟩, if_true]
    exact congrArg (fun f : E m →L[𝕜] E m => f (x.val m)) ((b m).compatible N M)
  · simp [hmN, hmM]
  · simp [hmN, hmM]
  · simp [hmN, hmM]

theorem c0SumFDDProjection_range_zero {N m : ℕ} (hm : N ≤ m)
    (x : LinearMap.range (c0SumFDDProjection 𝕜 E b N).toLinearMap) : x.val.val m = 0 := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  change (c0SumFDDProjection 𝕜 E b N y).val m = 0
  rw [c0SumFDDProjection_apply, if_neg (not_lt.mpr hm)]

theorem c0SumFDDProjection_range_coordinate {N : ℕ}
    (x : LinearMap.range (c0SumFDDProjection 𝕜 E b N).toLinearMap) (n : Fin N) :
    x.val.val n.val ∈ LinearMap.range ((b n.val).projection N).toLinearMap := by
  obtain ⟨y, hy⟩ := x.property
  refine ⟨y.val n.val, ?_⟩
  rw [← hy]
  change (b n.val).projection N (y.val n.val) = (c0SumFDDProjection 𝕜 E b N y).val n.val
  rw [c0SumFDDProjection_apply, if_pos n.isLt]

def c0SumFDDRangeRestriction (N : ℕ) :
    LinearMap.range (c0SumFDDProjection 𝕜 E b N).toLinearMap →ₗ[𝕜]
      (∀ n : Fin N, LinearMap.range ((b n.val).projection N).toLinearMap) where
  toFun x n := ⟨x.val.val n.val, c0SumFDDProjection_range_coordinate 𝕜 E b x n⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem c0SumFDDRangeRestriction_injective (N : ℕ) :
    Function.Injective (c0SumFDDRangeRestriction 𝕜 E b N) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply lp.ext
  funext m
  by_cases hm : m < N
  · exact congrArg Subtype.val (congrFun h ⟨m, hm⟩)
  · rw [c0SumFDDProjection_range_zero 𝕜 E b (Nat.le_of_not_lt hm) x,
      c0SumFDDProjection_range_zero 𝕜 E b (Nat.le_of_not_lt hm) y]

theorem c0SumFDDProjection_finite_rank (N : ℕ) :
    FiniteDimensional 𝕜 (LinearMap.range (c0SumFDDProjection 𝕜 E b N).toLinearMap) := by
  letI (n : Fin N) : FiniteDimensional 𝕜 (LinearMap.range ((b n.val).projection N).toLinearMap) :=
    (b n.val).finite_rank N
  exact FiniteDimensional.of_injective (c0SumFDDRangeRestriction 𝕜 E b N)
    (c0SumFDDRangeRestriction_injective 𝕜 E b N)

theorem c0SumFDDProjection_tendsto (x : C0Sum 𝕜 E) :
    Tendsto (fun N => c0SumFDDProjection 𝕜 E b N x) atTop (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 x.property) (ε / 4) (by positivity)
  have hhead : ∀ᶠ N in atTop, ∀ n : Fin K,
      ‖(b n.val).projection N (x.val n.val) - x.val n.val‖ < ε / 2 := by
    apply Filter.eventually_all.2
    intro n
    simpa only [dist_eq_norm] using
      (Metric.tendsto_nhds.1 ((b n.val).tendsTo_identity (x.val n.val))) (ε / 2) (half_pos hε)
  filter_upwards [hhead, eventually_ge_atTop K] with N hhead hKN
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (b := ε / 2) ?_ (half_lt_self hε)
  apply c0Sum_norm_le 𝕜 E (half_pos hε).le
  intro m
  change ‖(c0SumFDDProjection 𝕜 E b N x).val m - x.val m‖ ≤ ε / 2
  rw [c0SumFDDProjection_apply]
  by_cases hmK : m < K
  · rw [if_pos (hmK.trans_le hKN)]
    exact (hhead ⟨m, hmK⟩).le
  · have htail : ‖x.val m‖ < ε / 4 := by
      simpa only [dist_zero_right, norm_norm] using hK m (Nat.le_of_not_lt hmK)
    split_ifs
    · exact (norm_sub_le _ _).trans (by
        linarith [coordinateFDD_norm_apply_le 𝕜 E b m N (x.val m)])
    · simp only [zero_sub, norm_neg]
      linarith

/-- The diagonal monotone FDD on the dependent c₀ sum. -/
def c0SumMonotoneFDD : MonotoneFDD 𝕜 (C0Sum 𝕜 E) where
  projection := c0SumFDDProjection 𝕜 E b
  projection_zero := c0SumFDDProjection_zero 𝕜 E b
  finite_rank := c0SumFDDProjection_finite_rank 𝕜 E b
  compatible := c0SumFDDProjection_comp 𝕜 E b
  contractive := c0SumFDDProjection_norm_le 𝕜 E b
  tendsTo_identity := c0SumFDDProjection_tendsto 𝕜 E b

end LindenstraussRetraction
