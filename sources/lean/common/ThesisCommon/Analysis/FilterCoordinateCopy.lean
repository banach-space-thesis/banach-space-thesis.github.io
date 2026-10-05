import ThesisCommon.Analysis.FilterConvergenceCriteria
import ThesisCommon.Analysis.FilterConvergenceTrace

/-! Coordinate copies of filters yield actual surjective linear isometries
of the corresponding coordinate subspaces. This proves the primariness-under-
sums part of Proposition 6.9, without asserting its diagonalisation part. -/
noncomputable section
open Filter Topology
open scoped ENNReal Cardinal
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
universe u v
variable {𝕜 : Type*} [RCLike 𝕜] {Γ : Type u} {Λ : Type v}

/-- Reading coordinates along a filter-convergent map preserves boundedness
and convergence to zero. -/
def filterNullReadValue (F : Filter Γ) (G : Filter Λ) (f : Λ → Γ)
    (hf : Tendsto f G F) (x : FilterNullSpace 𝕜 F) : FilterNullSpace 𝕜 G :=
  ⟨⟨fun β => x (f β), memℓp_infty (by
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨β, rfl⟩
    exact x.norm_apply_le (f β))⟩, x.tendsto_zero.comp hf⟩

@[simp] theorem filterNullReadValue_apply (F : Filter Γ) (G : Filter Λ) (f : Λ → Γ)
    (hf : Tendsto f G F) (x : FilterNullSpace 𝕜 F) (β : Λ) :
    filterNullReadValue F G f hf x β = x (f β) := rfl

theorem filterNullReadValue_norm_le (F : Filter Γ) (G : Filter Λ) (f : Λ → Γ)
    (hf : Tendsto f G F) (x : FilterNullSpace 𝕜 F) :
    ‖filterNullReadValue F G f hf x‖ ≤ ‖x‖ := by
  apply FilterNullSpace.norm_le (norm_nonneg x)
  intro β
  exact x.norm_apply_le (f β)

theorem filterEquiv_symm_tendsto (F : Filter Γ) (G : Filter Λ) (e : Γ ≃ Λ)
    (he : Filter.map e F = G) : Tendsto e.symm G F := by
  rw [Tendsto, ← he, Filter.map_map]
  simp

/-- Reindexing by a filter isomorphism is an actual linear isometry of the
filter-null spaces; both maps are literal coordinate reindexings. -/
def filterNullReindexEquiv (F : Filter Γ) (G : Filter Λ) (e : Γ ≃ Λ)
    (he : Filter.map e F = G) : FilterNullSpace 𝕜 F ≃ₗᵢ[𝕜] FilterNullSpace 𝕜 G where
  toFun := filterNullReadValue F G e.symm (filterEquiv_symm_tendsto F G e he)
  invFun := filterNullReadValue G F e (show Tendsto e F G from he.le)
  left_inv x := by ext γ; simp
  right_inv x := by ext β; simp
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  norm_map' x := by
    apply le_antisymm (filterNullReadValue_norm_le F G e.symm _ x)
    apply FilterNullSpace.norm_le (norm_nonneg _)
    intro γ
    have h := (filterNullReadValue F G e.symm
      (filterEquiv_symm_tendsto F G e he) x).norm_apply_le (e γ)
    simpa only [filterNullReadValue_apply, Equiv.symm_apply_apply] using h

@[simp] theorem filterNullReindexEquiv_apply (F : Filter Γ) (G : Filter Λ) (e : Γ ≃ Λ)
    (he : Filter.map e F = G) (x : FilterNullSpace 𝕜 F) (β : Λ) :
    filterNullReindexEquiv (𝕜 := 𝕜) F G e he x β = x (e.symm β) := rfl

/-- The coordinate-copy set identity is exactly the assertion that θ carries
the original filter onto the trace filter. -/
theorem IsFilterCoordinateCopy.map_eq_trace {F : Filter Γ} {C : Set Γ} {θ : Γ ≃ C}
    (h : IsFilterCoordinateCopy F C θ) : Filter.map θ F = filterTrace F C := by
  ext B
  rw [Filter.mem_map, mem_filterTrace_iff]
  have hi : (fun γ => (θ γ).val) '' (θ ⁻¹' B) = Subtype.val '' B := by
    ext γ
    constructor
    · rintro ⟨α, hα, rfl⟩
      exact ⟨θ α, hα, rfl⟩
    · rintro ⟨β, hβ, rfl⟩
      refine ⟨θ.symm β, ?_, ?_⟩
      · simpa using hβ
      · simp
  simpa only [hi] using h (θ ⁻¹' B)

set_option maxHeartbeats 800000 in
/-- The source's U_θ: a surjective coordinate linear isometry from X_F
onto X_F(C), proved from the set-theoretic coordinate-copy hypothesis alone. -/
def filterCoordinateCopyEquiv (F : Filter Γ) (C : Set Γ) (θ : Γ ≃ C)
    (h : IsFilterCoordinateCopy F C θ) :
    FilterNullSpace 𝕜 F ≃ₗᵢ[𝕜] FilterSupportedSpace (𝕜 := 𝕜) F C :=
  (filterNullReindexEquiv (𝕜 := 𝕜) F (filterTrace F C) θ h.map_eq_trace).trans
    (filterTraceEquiv (𝕜 := 𝕜) F C).symm

@[simp] theorem filterCoordinateCopyEquiv_apply_image (F : Filter Γ) (C : Set Γ)
    (θ : Γ ≃ C) (h : IsFilterCoordinateCopy F C θ) (x : FilterNullSpace 𝕜 F) (γ : Γ) :
    (filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ h x).val (θ γ).val = x γ := by
  change (if hγ : (θ γ).val ∈ C then
    x (θ.symm ⟨(θ γ).val, hγ⟩) else 0) = x γ
  simp

theorem filterCoordinateCopyEquiv_apply_off (F : Filter Γ) (C : Set Γ)
    (θ : Γ ≃ C) (h : IsFilterCoordinateCopy F C θ) (x : FilterNullSpace 𝕜 F)
    {γ : Γ} (hγ : γ ∉ C) : (filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ h x).val γ = 0 :=
  (filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ h x).property γ hγ

/-- A surjective linear isometry has distortion at most one, even when its
domain is the zero space. The estimate is checked before specialising to
the nested coordinate-subspace types. -/
theorem isomorphicWithBound_one_of_linearIsometryEquiv
    {E Z : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (e : E ≃ₗᵢ[𝕜] Z) :
    IsomorphicWithBound 𝕜 E Z 1 := by
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  have he := e.toLinearIsometry.norm_toContinuousLinearMap_le
  have he' := e.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  simpa only [one_mul] using mul_le_mul he he' (norm_nonneg _) zero_le_one

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- A coordinate copy is a 1-copying set. Norms of the equivalence and its
inverse are bounded by one, including the possible zero-space case. -/
theorem IsFilterCoordinateCopy.isCopyingSet {F : Filter Γ} {C : Set Γ} {θ : Γ ≃ C}
    (h : IsFilterCoordinateCopy F C θ) : IsFilterCopyingSet (𝕜 := 𝕜) F 1 C :=
  ⟨le_rfl, isomorphicWithBound_one_of_linearIsometryEquiv
    (filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ h)⟩

/-- Every partition of an infinite set into two pieces has a piece of full
cardinality. This includes singular-cardinality index sets. -/
theorem cardinal_eq_of_set_or_compl [Infinite Γ] (A : Set Γ) :
    Cardinal.mk A = Cardinal.mk Γ ∨ Cardinal.mk (Aᶜ : Set Γ) = Cardinal.mk Γ := by
  by_cases hA : Cardinal.mk A = Cardinal.mk Γ
  · exact Or.inl hA
  · exact Or.inr (Cardinal.mk_compl_of_infinite A
      (lt_of_le_of_ne (Cardinal.mk_subtype_le A) hA))

/-- The first half of Proposition 6.9: large-set self-similarity yields
1-primary-under-sums. No diagonalisation or PFP conclusion is assumed here. -/
theorem IsLargeSetSelfSimilarFilter.primaryUnderSums [Infinite Γ] {F : Filter Γ}
    (hF : IsLargeSetSelfSimilarFilter F) : IsFilterPrimaryUnderSums (𝕜 := 𝕜) F 1 := by
  refine ⟨le_rfl, ?_⟩
  intro A
  rcases cardinal_eq_of_set_or_compl A with hA | hA
  · obtain ⟨C, hCA, θ, hθ⟩ := hF A hA
    exact Or.inl ⟨C, hCA, hθ.isCopyingSet⟩
  · obtain ⟨C, hCA, θ, hθ⟩ := hF Aᶜ hA
    exact Or.inr ⟨C, hCA, hθ.isCopyingSet⟩

end ThesisCommon
