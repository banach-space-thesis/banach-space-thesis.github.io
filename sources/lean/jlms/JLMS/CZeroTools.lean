import JLMS.Adjoint

/-!
# Section 4: evaluation and compact clopen characteristic functions

These constructions use the actual mathlib space C₀(K). They do not need
scatteredness: that hypothesis is used later to produce enough compact clopen
neighborhoods, rather than to define the functions on neighborhoods supplied.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Filter Topology
open scoped ZeroAtInfty

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K]

theorem norm_CZero_apply_le (f : CZero 𝕜 K) (x : K) : ‖f x‖ ≤ ‖f‖ :=
  BoundedContinuousFunction.norm_coe_le_norm f.toBCF x

/-- The point evaluation δₖ in Section 4. -/
def evaluation (x : K) : CZero 𝕜 K →L[𝕜] 𝕜 :=
  ({ toFun := fun f => f x
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : CZero 𝕜 K →ₗ[𝕜] 𝕜).mkContinuous 1
    (fun f => by simpa using norm_CZero_apply_le f x)

@[simp] theorem evaluation_apply (x : K) (f : CZero 𝕜 K) : evaluation x f = f x := rfl

theorem norm_evaluation_le (x : K) : ‖evaluation (𝕜 := 𝕜) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using norm_CZero_apply_le f x

/-- The characteristic function 1_U belongs to C₀(K): continuity uses clopenness,
and vanishing at infinity uses compactness. -/
def clopenIndicator (U : Set K) (hU : IsClopen U) (hc : IsCompact U) : CZero 𝕜 K where
  toFun := U.indicator (fun _ => 1)
  continuous_toFun := continuous_indicator (by simp [hU]) continuous_const.continuousOn
  zero_at_infty' := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hc.compl_mem_cocompact] with x hx
    simp only [Set.mem_compl_iff] at hx
    simp [hx]

@[simp] theorem clopenIndicator_apply (U : Set K) (hU : IsClopen U) (hc : IsCompact U)
    (x : K) : clopenIndicator (𝕜 := 𝕜) U hU hc x = if x ∈ U then 1 else 0 := by
  classical
  simp [clopenIndicator, Set.indicator_apply]

theorem norm_clopenIndicator_le (U : Set K) (hU : IsClopen U) (hc : IsCompact U) :
    ‖clopenIndicator (𝕜 := 𝕜) U hU hc‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro x
  change ‖clopenIndicator (𝕜 := 𝕜) U hU hc x‖ ≤ 1
  by_cases hx : x ∈ U <;> simp [hx]

theorem norm_clopenIndicator_eq_one (U : Set K) (hU : IsClopen U) (hc : IsCompact U)
    (hne : U.Nonempty) : ‖clopenIndicator (𝕜 := 𝕜) U hU hc‖ = 1 := by
  apply le_antisymm (norm_clopenIndicator_le U hU hc)
  obtain ⟨x, hx⟩ := hne
  simpa [hx] using norm_CZero_apply_le (clopenIndicator (𝕜 := 𝕜) U hU hc) x

/-- Disjoint unit-ball functions satisfy the pointwise summability condition
in the Arnott–Laustsen theorem: at most one summand is nonzero at each point. -/
theorem pointwise_tsum_norm_le_one_of_disjoint
    {ι : Type*} (η : ι → CZero 𝕜 K) (hunit : ∀ i, ‖η i‖ ≤ 1)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (Function.support (η i)) (Function.support (η j))) (x : K) :
    (∑' i, ‖η i x‖) ≤ 1 := by
  classical
  by_cases hx : ∃ i, η i x ≠ 0
  · obtain ⟨i, hi⟩ := hx
    have hzero : ∀ j, j ≠ i → ‖η j x‖ = 0 := by
      intro j hji
      have hj : η j x = 0 := by
        by_contra hj
        exact Set.disjoint_left.mp (hdisjoint hji) hj hi
      simp [hj]
    rw [tsum_eq_single i hzero]
    exact (norm_CZero_apply_le (η i) x).trans (hunit i)
  · push_neg at hx
    simp [hx]

end JLMS
