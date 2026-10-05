import ThesisCommon.Analysis.CoordinateMaskSubspaces

/-! Actual single-coordinate maps and the finite-subset expansion in c0
over any discrete index set. -/
noncomputable section
open Filter Topology
open scoped ZeroAtInfty BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def cZeroSingleAt (α : Γ) (x : X) : C₀(Γ, X) where
  toFun γ := if γ = α then x else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite]
    apply tendsto_const_nhds.congr'
    filter_upwards [(Set.finite_singleton α).compl_mem_cofinite] with γ hγ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hγ
    simp only [if_neg hγ]

@[simp] theorem cZeroSingleAt_apply (α γ : Γ) (x : X) :
    cZeroSingleAt α x γ = if γ = α then x else 0 := rfl

theorem norm_cZeroSingleAt_le (α : Γ) (x : X) : ‖cZeroSingleAt α x‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro γ
  change ‖if γ = α then x else 0‖ ≤ ‖x‖
  split_ifs <;> simp

def cZeroSingleAtL (α : Γ) : X →L[𝕜] C₀(Γ, X) :=
  LinearMap.mkContinuous
    { toFun := cZeroSingleAt α
      map_add' := by intro x y; ext γ; simp; split_ifs <;> simp
      map_smul' := by intro a x; ext γ; simp }
    1 (fun x => by simpa using norm_cZeroSingleAt_le α x)

@[simp] theorem cZeroSingleAtL_apply (α : Γ) (x : X) :
    cZeroSingleAtL (𝕜 := 𝕜) α x = cZeroSingleAt α x := rfl

include 𝕜

theorem cZero_finite_singleAt_apply (S : Finset Γ) (x : Γ → X) (γ : Γ) :
    (∑ α ∈ S, cZeroSingleAt α (x α)) γ = if γ ∈ S then x γ else 0 := by
  change cZeroCoordinate (𝕜 := 𝕜) γ (∑ α ∈ S, cZeroSingleAt α (x α)) = _
  simp only [map_sum, cZeroCoordinate_apply, cZeroSingleAt_apply]
  exact Finset.sum_ite_eq S γ x

theorem cZero_hasSum_singleAt (x : C₀(Γ, X)) : HasSum (fun γ => cZeroSingleAt γ (x γ)) x := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht := Metric.tendsto_nhds.mp x.zero_at_infty' (ε / 2) (half_pos hε)
  rw [cocompact_eq_cofinite] at ht
  have hS : {γ | ¬ ‖x γ‖ < ε / 2}.Finite := by
    simpa only [dist_zero_right] using (mem_cofinite.mp ht)
  filter_upwards [eventually_ge_atTop hS.toFinset] with S hSS
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ?_ (half_lt_self hε)
  apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
  intro γ
  change ‖(∑ α ∈ S, cZeroSingleAt α (x α)) γ - x γ‖ ≤ ε / 2
  rw [cZero_finite_singleAt_apply (𝕜 := 𝕜)]
  by_cases hγ : γ ∈ S
  · simp only [if_pos hγ, sub_self, norm_zero]
    exact (half_pos hε).le
  · rw [if_neg hγ, zero_sub, norm_neg]
    apply le_of_lt
    by_contra hn
    exact hγ (hSS (hS.mem_toFinset.mpr hn))

theorem cZero_singleAt_finite_norm_bound {n : ℕ} (e : Fin n ↪ Γ)
    (x : Fin n → X) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ‖∑ i, cZeroSingleAt (e i) (x i)‖ ≤ 1 := by
  classical
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro γ
  change ‖cZeroCoordinate (𝕜 := 𝕜) γ (∑ i, cZeroSingleAt (e i) (x i))‖ ≤ 1
  rw [map_sum]
  simp only [cZeroCoordinate_apply, cZeroSingleAt_apply]
  by_cases h : ∃ i, γ = e i
  · obtain ⟨i, rfl⟩ := h
    rw [Finset.sum_eq_single i]
    · simpa using hx i
    · intro j _ hji
      exact if_neg (fun heq => hji (e.injective heq).symm)
    · simp
  · have hz (i : Fin n) : γ ≠ e i := fun hi => h ⟨i, hi⟩
    simp only [if_neg (hz _), Finset.sum_const_zero, norm_zero, zero_le_one]

end ThesisCommon
