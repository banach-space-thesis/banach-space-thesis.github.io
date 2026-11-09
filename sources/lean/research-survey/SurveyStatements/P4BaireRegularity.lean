import SurveyStatements.P4BaireAdjoint
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.GDelta.Basic

/-! The exact Fσ/Gδ regularity of the adjoint used before the source's
Lebesgue--Hausdorff Baire-one characterization. -/

noncomputable section
set_option autoImplicit false

open Set Topology TopologicalSpace

namespace SurveyStatements.P4

/-- A map with separable metric range and closed inverse images of closed
balls has a countable closed-set decomposition of every open inverse image. -/
theorem open_preimage_countable_closed_cover
    {A E : Type*} [TopologicalSpace A] [MetricSpace E] (f : A → E)
    (hsep : IsSeparable (Set.range f))
    (hclosed : ∀ y r, IsClosed (f ⁻¹' Metric.closedBall y r))
    {U : Set E} (hU : IsOpen U) :
    ∃ S : Set (Set A), S.Countable ∧ (∀ s ∈ S, IsClosed s) ∧
      f ⁻¹' U = ⋃₀ S := by
  classical
  let R := Set.range f
  letI : SeparableSpace R := hsep.separableSpace
  letI : SecondCountableTopology R := inferInstance
  let V : Set R := Subtype.val ⁻¹' U
  let I := {p : R × ℝ // 0 < p.2 ∧ Metric.closedBall p.1.val p.2 ⊆ U}
  let O : I → Set R := fun p => Subtype.val ⁻¹' Metric.ball p.val.1.val p.val.2
  have hO : ∀ p, IsOpen (O p) := fun p =>
    Metric.isOpen_ball.preimage continuous_subtype_val
  have hcover : V ⊆ ⋃ p, O p := by
    intro y hy
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hy)
    exact Set.mem_iUnion.mpr ⟨⟨(y, r), hr, hball⟩, by simpa [O] using hr⟩
  obtain ⟨C, hC, hVC⟩ :=
    (HereditarilyLindelof_LindelofSets V).elim_countable_subcover O hO hcover
  let B : I → Set A := fun p => f ⁻¹' Metric.closedBall p.val.1.val p.val.2
  refine ⟨B '' C, hC.image B, ?_, ?_⟩
  · rintro s ⟨p, hp, rfl⟩
    exact hclosed _ _
  · apply Set.Subset.antisymm
    · intro a ha
      let y : R := ⟨f a, a, rfl⟩
      have hy : y ∈ V := ha
      obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp (hVC hy)
      apply Set.mem_sUnion.mpr
      refine ⟨B p, ⟨p, hp, rfl⟩, ?_⟩
      exact Metric.ball_subset_closedBall hyp
    · rintro a ⟨s, ⟨p, hp, rfl⟩, ha⟩
      exact p.property.2 ha

/-- In the same setting, inverse images of closed sets are Gδ. -/
theorem closed_preimage_isGδ
    {A E : Type*} [TopologicalSpace A] [MetricSpace E] (f : A → E)
    (hsep : IsSeparable (Set.range f))
    (hclosed : ∀ y r, IsClosed (f ⁻¹' Metric.closedBall y r))
    {F : Set E} (hF : IsClosed F) : IsGδ (f ⁻¹' F) := by
  obtain ⟨S, hS, hclosedS, heq⟩ :=
    open_preimage_countable_closed_cover f hsep hclosed hF.isOpen_compl
  have h : IsGδ (⋂ s ∈ S, sᶜ) :=
    IsGδ.biInter_of_isOpen hS (fun s hs => (hclosedS s hs).isOpen_compl)
  have heq' : (f ⁻¹' Fᶜ)ᶜ = ⋂ s ∈ S, sᶜ := by
    rw [heq]
    ext a
    simp
  rw [← heq'] at h
  simpa using h

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Actual Fσ inverse images of all norm-open dual sets under the weak-star
adjoint of a weakly compact operator into a separable space. -/
theorem adjoint_open_preimage_countable_closed_cover [SeparableSpace Y]
    (T : X →L[𝕜] Y) (hT : IsWeaklyCompactOperator 𝕜 T)
    {U : Set (StrongDual 𝕜 X)} (hU : IsOpen U) :
    ∃ S : Set (Set (WeakDual 𝕜 Y)), S.Countable ∧
      (∀ s ∈ S, IsClosed s) ∧
      (fun φ => banachAdjoint T (WeakDual.toStrongDual φ)) ⁻¹' U = ⋃₀ S := by
  apply open_preimage_countable_closed_cover _ _ _ hU
  · have heq : Set.range (fun φ : WeakDual 𝕜 Y =>
        banachAdjoint T (WeakDual.toStrongDual φ)) = Set.range (banachAdjoint T) := by
      ext η
      constructor
      · rintro ⟨φ, rfl⟩
        exact ⟨WeakDual.toStrongDual φ, rfl⟩
      · rintro ⟨φ, rfl⟩
        exact ⟨StrongDual.toWeakDual φ, rfl⟩
    rw [heq]
    exact weaklyCompact_adjoint_range_isSeparable T hT
  · intro η r
    simpa only [Set.preimage, Metric.mem_closedBall, dist_eq_norm] using
      adjoint_normBall_preimage_isClosed T η r

/-- Actual Gδ inverse images of norm-closed dual sets for the same adjoint. -/
theorem adjoint_closed_preimage_isGδ [SeparableSpace Y]
    (T : X →L[𝕜] Y) (hT : IsWeaklyCompactOperator 𝕜 T)
    {F : Set (StrongDual 𝕜 X)} (hF : IsClosed F) :
    IsGδ ((fun φ => banachAdjoint T (WeakDual.toStrongDual φ)) ⁻¹' F) := by
  obtain ⟨S, hS, hclosedS, heq⟩ :=
    adjoint_open_preimage_countable_closed_cover T hT hF.isOpen_compl
  have h : IsGδ (⋂ s ∈ S, sᶜ) :=
    IsGδ.biInter_of_isOpen hS (fun s hs => (hclosedS s hs).isOpen_compl)
  have heq' : ((fun φ => banachAdjoint T (WeakDual.toStrongDual φ)) ⁻¹' Fᶜ)ᶜ =
      ⋂ s ∈ S, sᶜ := by
    rw [heq]
    ext φ
    simp
  rw [← heq'] at h
  simpa using h

end SurveyStatements.P4
