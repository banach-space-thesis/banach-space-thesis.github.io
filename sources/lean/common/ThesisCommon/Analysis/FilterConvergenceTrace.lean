import ThesisCommon.Analysis.FilterConvergenceSpace

/-! Restriction and zero extension identify the actual coordinate subspace
X_F(A) isometrically with c_(F_A)(A), including improper trace filters. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 : Type*} [RCLike 𝕜] {Γ : Type*} (F : Filter Γ) (A : Set Γ)

/-- Restriction to A, with both boundedness and trace-filter convergence proved. -/
def filterTraceRestrict (x : FilterSupportedSpace (𝕜 := 𝕜) F A) :
    FilterNullSpace 𝕜 (filterTrace F A) :=
  ⟨⟨fun α => x.val α.val, memℓp_infty (by
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨α, rfl⟩
    exact x.val.norm_apply_le α.val)⟩,
    x.val.tendsto_zero.comp Filter.tendsto_comap⟩

@[simp] theorem filterTraceRestrict_apply (x : FilterSupportedSpace (𝕜 := 𝕜) F A) (α : A) :
    filterTraceRestrict F A x α = x.val α.val := rfl

/-- Zero insertion from the trace space into the original filter-null space. -/
def filterTraceExtendValue (y : FilterNullSpace 𝕜 (filterTrace F A)) : FilterNullSpace 𝕜 F :=
  ⟨⟨fun γ => if h : γ ∈ A then y ⟨γ, h⟩ else 0, memℓp_infty (by
    refine ⟨‖y‖, ?_⟩
    rintro _ ⟨γ, rfl⟩
    by_cases h : γ ∈ A
    · simpa only [dif_pos h] using y.norm_apply_le ⟨γ, h⟩
    · simp [h])⟩, by
    rw [mem_filterNullSubmodule_iff]
    intro ε hε
    have hy := (mem_filterNullSubmodule_iff (filterTrace F A) y.val).mp y.property ε hε
    rw [mem_filterTrace_iff] at hy
    filter_upwards [hy] with γ hγ
    rcases hγ with ⟨α, hα, rfl⟩ | hγ
    · change ‖if h : α.val ∈ A then y ⟨α.val, h⟩ else 0‖ < ε
      simpa only [dif_pos α.property] using hα
    · change ‖if h : γ ∈ A then y ⟨γ, h⟩ else 0‖ < ε
      simpa only [dif_neg hγ, norm_zero] using hε⟩

@[simp] theorem filterTraceExtendValue_apply (y : FilterNullSpace 𝕜 (filterTrace F A)) (γ : Γ) :
    filterTraceExtendValue F A y γ = if h : γ ∈ A then y ⟨γ, h⟩ else 0 := rfl

theorem filterTraceRestrict_norm (x : FilterSupportedSpace (𝕜 := 𝕜) F A) :
    ‖filterTraceRestrict F A x‖ = ‖x‖ := by
  apply le_antisymm
  · apply FilterNullSpace.norm_le (norm_nonneg x)
    intro α
    exact x.val.norm_apply_le α.val
  · change ‖x.val‖ ≤ ‖filterTraceRestrict F A x‖
    apply FilterNullSpace.norm_le (norm_nonneg _)
    intro γ
    by_cases hγ : γ ∈ A
    · exact (filterTraceRestrict F A x).norm_apply_le ⟨γ, hγ⟩
    · simp [x.property γ hγ]

/-- The source's actual trace-space identification, with exact supremum norm.
The improper case requires no separate definition or additional assumption. -/
def filterTraceEquiv :
    FilterSupportedSpace (𝕜 := 𝕜) F A ≃ₗᵢ[𝕜] FilterNullSpace 𝕜 (filterTrace F A) where
  toFun := filterTraceRestrict F A
  invFun y := ⟨filterTraceExtendValue F A y, by intro γ hγ; simp [hγ]⟩
  left_inv x := by
    apply Subtype.ext
    apply FilterNullSpace.ext
    intro γ
    by_cases hγ : γ ∈ A
    · simp [hγ]
    · simp [hγ, x.property γ hγ]
  right_inv y := by ext α; simp
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  norm_map' := filterTraceRestrict_norm F A

@[simp] theorem filterTraceEquiv_apply (x : FilterSupportedSpace (𝕜 := 𝕜) F A) (α : A) :
    filterTraceEquiv (𝕜 := 𝕜) F A x α = x.val α.val := rfl

end ThesisCommon
