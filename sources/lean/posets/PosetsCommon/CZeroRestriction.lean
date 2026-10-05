import PosetsCommon.CountableCZero

noncomputable section
open Filter Topology
open scoped ZeroAtInfty
namespace ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜] {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]

theorem cZero_superlevel_compact (f : C₀(K, 𝕜)) {ε : ℝ} (hε : 0 < ε) :
    IsCompact {x | ε ≤ ‖f x‖} := by
  obtain ⟨C, hC, hsmall⟩ := hasBasis_cocompact.mem_iff.mp
    ((Metric.tendsto_nhds.mp (zero_at_infty f)) ε hε)
  apply hC.of_isClosed_subset (isClosed_le continuous_const f.continuous.norm)
  intro x hx
  by_contra hnot
  have hs : ‖f x‖ < ε := by simpa using hsmall hnot
  exact (not_lt_of_ge hx) hs

/-- Restrict a C₀ function to an embedded subspace containing its nonzero set. -/
def restrictSupportedCZero (e : L → K) (he : IsEmbedding e) (f : C₀(K, 𝕜))
    (hf : ∀ x, x ∉ Set.range e → f x = 0) : C₀(L, 𝕜) where
  toFun x := f (e x)
  continuous_toFun := f.continuous.comp he.continuous
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hrange : {x | ε ≤ ‖f x‖} ⊆ Set.range e := by
      intro x hx
      by_contra hnot
      have hz := hf x hnot
      change ε ≤ ‖f x‖ at hx
      rw [hz, norm_zero] at hx
      exact (not_le_of_gt hε) hx
    have hcompact := he.isInducing.isCompact_preimage' (cZero_superlevel_compact f hε) hrange
    filter_upwards [hcompact.compl_mem_cocompact] with x hx
    simpa only [dist_zero_right] using (lt_of_not_ge hx : ‖f (e x)‖ < ε)

theorem norm_restrictSupportedCZero (e : L → K) (he : IsEmbedding e) (f : C₀(K, 𝕜))
    (hf : ∀ x, x ∉ Set.range e → f x = 0) : ‖restrictSupportedCZero e he f hf‖ = ‖f‖ := by
  apply le_antisymm
  · exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
      (fun x => f.toBCF.norm_coe_le_norm (e x))
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg (restrictSupportedCZero e he f hf))).mpr
    intro x
    by_cases hx : x ∈ Set.range e
    · obtain ⟨y, rfl⟩ := hx
      exact (restrictSupportedCZero e he f hf).toBCF.norm_coe_le_norm y
    · change ‖f x‖ ≤ ‖restrictSupportedCZero e he f hf‖
      rw [hf x hx, norm_zero]
      exact norm_nonneg _

def supportedSubmoduleRestriction (e : L → K) (he : IsEmbedding e)
    (X : Submodule 𝕜 C₀(K, 𝕜)) (hX : ∀ f : X, ∀ x, x ∉ Set.range e → f.val x = 0) :
    X →ₗᵢ[𝕜] C₀(L, 𝕜) where
  toFun f := restrictSupportedCZero e he f.val (hX f)
  map_add' f g := by ext x; rfl
  map_smul' a f := by ext x; rfl
  norm_map' f := norm_restrictSupportedCZero e he f.val (hX f)

theorem supportedSubmodule_separable [T2Space L] [LocallyCompactSpace L] [Countable L]
    (e : L → K) (he : IsEmbedding e) (X : Submodule 𝕜 C₀(K, 𝕜))
    (hX : ∀ f : X, ∀ x, x ∉ Set.range e → f.val x = 0) : TopologicalSpace.SeparableSpace X := by
  letI := countable_cZero_separable (𝕜 := 𝕜) L
  exact (supportedSubmoduleRestriction e he X hX).isometry.isEmbedding.separableSpace

end ThesisCommon
