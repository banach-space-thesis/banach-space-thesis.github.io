import ThesisCommon.Analysis.CZeroCountableIncoming
import ThesisCommon.Analysis.CountableInvariantPartition

/-! Countable invariant coordinate blocks of actual c0 projections with
separable coefficients. Finite-subset convergence proves support invariance;
all distinct blocks have zero interaction, at every index cardinality. -/
noncomputable section
open Filter Topology TopologicalSpace
open scoped ZeroAtInfty BigOperators
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem cZero_operator_supported_of_singleAt (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X))
    (A B : Set Γ)
    (hAB : ∀ α ∈ A, ∀ x : X, ∀ β ∉ B, T (cZeroSingleAt α x) β = 0)
    (x : C₀(Γ, X)) (hx : ∀ α ∉ A, x α = 0) : ∀ β ∉ B, T x β = 0 := by
  classical
  intro β hβ
  let R : C₀(Γ, X) →L[𝕜] X := (cZeroCoordinate β).comp T
  have hz (α : Γ) : R (cZeroSingleAt α (x α)) = 0 := by
    by_cases hα : α ∈ A
    · exact hAB α hα (x α) β hβ
    · change R (cZeroSingleAtL (𝕜 := 𝕜) α (x α)) = 0
      rw [hx α hα, map_zero, map_zero]
  have ht := (R.continuous.tendsto x).comp (cZero_hasSum_singleAt (𝕜 := 𝕜) x)
  have hs : Tendsto (fun S : Finset Γ => R (∑ α ∈ S, cZeroSingleAt α (x α)))
      atTop (𝓝 0) := by
    simpa only [map_sum, hz, Finset.sum_const_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Finset Γ => (0 : X)) atTop (𝓝 0))
  exact tendsto_nhds_unique ht hs

theorem cZero_invariant_countable_blocks [SeparableSpace X]
    (P : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) (hP : P.comp P = P) :
    ∃ B : (Cardinal.mk Γ).ord.toType → Set Γ,
      (Pairwise (fun α β => Disjoint (B α) (B β)) ∧
        (∀ α, (B α).Countable) ∧ (⋃ α, B α) = Set.univ) ∧
      (∀ α, (cZeroBlockCompression P (B α)).comp (cZeroBlockCompression P (B α)) =
        cZeroBlockCompression P (B α)) ∧
      ∀ α β, α ≠ β → ((cZeroCoordinateProjection (𝕜 := 𝕜) (B β)).comp P).comp
        (cZeroSupportedSubmodule (𝕜 := 𝕜) (X := X) (B α)).subtypeL = 0 := by
  classical
  let F (α : Γ) : Set Γ := {β | cZeroFibreRelation P α β ∨ cZeroFibreRelation P β α}
  have hF (α : Γ) : (F α).Countable :=
    (cZeroFibreRelation_outgoing_countable P α).union (cZeroFibreRelation_incoming_countable P α)
  obtain ⟨B, hdisj, hcount, hcover, hclosed⟩ := countable_invariant_partition F hF
    (fun _ _ h => h.symm)
  have hinv (i : (Cardinal.mk Γ).ord.toType) :
      ∀ x : C₀(Γ, X), (∀ γ ∉ B i, x γ = 0) → ∀ γ ∉ B i, P x γ = 0 := by
    apply cZero_operator_supported_of_singleAt P (B i) (B i)
    intro α hα x β hβ
    exact cZeroFibreRelation_zero P (fun h => hβ (hclosed i α hα (Or.inl h))) x
  have hfix (A : Set Γ) (y : C₀(Γ, X)) (hy : ∀ γ ∉ A, y γ = 0) :
      cZeroCoordinateProjection (𝕜 := 𝕜) A y = y := by
    ext γ
    by_cases hγ : γ ∈ A
    · simp only [cZeroCoordinateProjection_apply, if_pos hγ]
    · simp only [cZeroCoordinateProjection_apply, if_neg hγ, hy γ hγ]
  refine ⟨B, ⟨hdisj, hcount, hcover⟩, ?_, ?_⟩
  · intro i
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change cZeroCoordinateProjection (B i) (P (cZeroCoordinateProjection (B i) (P x.val))) =
      cZeroCoordinateProjection (B i) (P x.val)
    rw [hfix (B i) (P x.val) (hinv i x.val x.property)]
    have hPP := DFunLike.congr_fun hP x.val
    change P (P x.val) = P x.val at hPP
    rw [hPP]
    exact hfix (B i) (P x.val) (hinv i x.val x.property)
  · intro i j hij
    apply ContinuousLinearMap.ext
    intro x
    ext γ
    change cZeroCoordinateProjection (B j) (P x.val) γ = 0
    by_cases hγ : γ ∈ B j
    · rw [cZeroCoordinateProjection_apply, if_pos hγ]
      exact hinv i x.val x.property γ (fun hγi => Set.disjoint_left.mp (hdisj hij) hγi hγ)
    · simp only [cZeroCoordinateProjection_apply, if_neg hγ]

end ThesisCommon
