import JLMS.CZeroSum

/-!
# Coordinates and finite truncations in Banach c₀ sums

The finite-coordinate projections converge in the supremum norm. These
lemmas provide the finite-sum reconstruction interface for ordinal blocks.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Filter Topology
open scoped ENNReal
namespace JLMS.CZeroSum
universe u v w
variable {𝕜 : Type w} [RCLike 𝕜] {I : Type u} {E : I → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

def evalCLM (i : I) : CZeroSum 𝕜 E →L[𝕜] E i :=
  ({ toFun x := x i
     map_add' x y := rfl
     map_smul' c x := rfl } : CZeroSum 𝕜 E →ₗ[𝕜] E i).mkContinuous 1
    (fun x => by simpa only [one_mul] using x.norm_apply_le_norm i)

@[simp] theorem evalCLM_apply (i : I) (x : CZeroSum 𝕜 E) : evalCLM i x = x i := rfl

@[simp] theorem sum_apply {J : Type*} (s : Finset J) (f : J → CZeroSum 𝕜 E) (i : I) :
    (∑ j ∈ s, f j) i = ∑ j ∈ s, f j i :=
  map_sum (evalCLM (𝕜 := 𝕜) (E := E) i) f s

def single (i : I) (v : E i) : CZeroSum 𝕜 E := by
  classical
  refine ⟨lp.single ∞ i v, ?_⟩
  apply (tendsto_norm_cofinite_iff_finite _).mpr
  intro ε hε
  apply (Set.finite_singleton i).subset
  intro j hj
  by_contra hji
  have hj' : ε ≤ ‖lp.single ∞ i v j‖ := hj
  rw [lp.single_apply_ne _ _ _ hji, norm_zero] at hj'
  exact hε.not_ge hj'

@[simp] theorem single_apply_self (i : I) (v : E i) : single (𝕜 := 𝕜) i v i = v := by
  classical
  exact lp.single_apply_self _ _ _

theorem single_apply_ne (i : I) (v : E i) {j : I} (hji : j ≠ i) :
    single (𝕜 := 𝕜) i v j = 0 := by
  classical
  exact lp.single_apply_ne _ _ _ hji

@[simp] theorem norm_single (i : I) (v : E i) : ‖single (𝕜 := 𝕜) i v‖ = ‖v‖ := by
  classical
  exact lp.norm_single (by simp : (0 : ℝ≥0∞) < ∞) _ _

def singleIsometry (i : I) : E i →ₗᵢ[𝕜] CZeroSum 𝕜 E where
  toFun := single i
  map_add' a b := by
    classical
    apply Subtype.ext
    exact lp.single_add _ _ _ _
  map_smul' c a := by
    classical
    apply Subtype.ext
    exact lp.single_smul _ _ _ _
  norm_map' := norm_single i

@[simp] theorem singleIsometry_apply (i : I) (v : E i) :
    singleIsometry (𝕜 := 𝕜) i v = single i v := rfl

def truncate (s : Finset I) (x : CZeroSum 𝕜 E) : CZeroSum 𝕜 E := by
  classical
  apply CZeroSum.mk (fun i => if i ∈ s then x i else 0)
  apply (tendsto_norm_cofinite_iff_finite _).mpr
  intro ε hε
  apply s.finite_toSet.subset
  intro i hi
  change i ∈ s
  by_contra his
  have hi' : ε ≤ ‖if i ∈ s then x i else 0‖ := hi
  simp only [if_neg his, norm_zero] at hi'
  exact hε.not_ge hi'

@[simp] theorem truncate_apply (s : Finset I) (x : CZeroSum 𝕜 E) (i : I) :
    truncate s x i = if i ∈ s then x i else 0 := by
  classical
  rfl

theorem norm_truncate_le (s : Finset I) (x : CZeroSum 𝕜 E) : ‖truncate s x‖ ≤ ‖x‖ := by
  classical
  apply norm_le (norm_nonneg x)
  intro i
  by_cases hi : i ∈ s
  · simpa only [truncate_apply, if_pos hi] using x.norm_apply_le_norm i
  · simp only [truncate_apply, if_neg hi, norm_zero, norm_nonneg]

theorem truncate_eq_sum_single (s : Finset I) (x : CZeroSum 𝕜 E) :
    truncate s x = ∑ i ∈ s, single i (x i) := by
  classical
  ext i
  rw [sum_apply]
  by_cases hi : i ∈ s
  · rw [truncate_apply, if_pos hi, Finset.sum_eq_single i]
    · exact (single_apply_self i (x i)).symm
    · intro j hj hji
      exact single_apply_ne j (x j) hji.symm
    · exact fun h => (h hi).elim
  · rw [truncate_apply, if_neg hi]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    exact single_apply_ne j (x j) (fun h => hi (h ▸ hj))

/-- A finite set containing every coordinate of size at least ε leaves a
tail of norm at most ε. -/
theorem norm_sub_truncate_le (x : CZeroSum 𝕜 E) (s : Finset I) {ε : ℝ} (hε : 0 ≤ ε)
    (hs : ∀ i, ε ≤ ‖x i‖ → i ∈ s) : ‖x - truncate s x‖ ≤ ε := by
  classical
  apply norm_le hε
  intro i
  by_cases hi : i ∈ s
  · simp only [sub_apply, truncate_apply, if_pos hi, sub_self, norm_zero, hε]
  · simpa only [sub_apply, truncate_apply, if_neg hi, sub_zero] using
      (lt_of_not_ge (fun h => hi (hs i h))).le

theorem tendsto_truncate (x : CZeroSum 𝕜 E) :
    Tendsto (fun s : Finset I => truncate s x) atTop (𝓝 x) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let s : Finset I := (x.finite_norm_ge (half_pos hε)).toFinset
  filter_upwards [eventually_ge_atTop s] with t ht
  have hbound : ‖x - truncate t x‖ ≤ ε / 2 :=
    norm_sub_truncate_le x t (half_pos hε).le (fun i hi => ht (by simpa [s] using hi))
  rw [dist_eq_norm, norm_sub_rev]
  exact hbound.trans_lt (half_lt_self hε)

theorem hasSum_single (x : CZeroSum 𝕜 E) : HasSum (fun i => single i (x i)) x := by
  simpa only [truncate_eq_sum_single] using tendsto_truncate x

end JLMS.CZeroSum
