import ThesisCommon.Analysis.Gantmacher

/-! Weakly compact approximation of an operator's unit-ball image passes
to its bidual with the same error. Goldstine density and compactness of the
weak-star error ball prove the assertion without assuming a convergent sequence. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option maxSynthPendingDepth 3
open Set Topology
open scoped Pointwise
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem exists_bidual_weakCompact_approximation
    (T : E →L[𝕜] F) (D : Set F)
    (hD : IsCompact (toWeakSpace 𝕜 F '' D)) {ε : ℝ}
    (hcover : ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ D, ‖T x - y‖ ≤ ε)
    (ξ : StrongDual 𝕜 (StrongDual 𝕜 E)) (hξ : ‖ξ‖ ≤ 1) :
    ∃ y ∈ D, ‖bidualMap T ξ - NormedSpace.inclusionInDoubleDual 𝕜 F y‖ ≤ ε := by
  let J := weakBidualInclusion (𝕜 := 𝕜) (E := F)
  let K := J '' (toWeakSpace 𝕜 F '' D)
  let B : Set (WeakDual 𝕜 (StrongDual 𝕜 F)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 ε
  have hK : IsCompact K := hD.image J.continuous
  have hB : IsCompact B :=
    WeakDual.isCompact_closedBall 𝕜 (0 : StrongDual 𝕜 (StrongDual 𝕜 F)) ε
  have hc : IsClosed ((weakStarBidualMap T) ⁻¹' (K + B)) :=
    (hK.add hB).isClosed.preimage (weakStarBidualMap T).continuous
  have hsub : weakStarBidualInclusion (𝕜 := 𝕜) (E := E) '' Metric.closedBall 0 1 ⊆
      (weakStarBidualMap T) ⁻¹' (K + B) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := hcover x (by simpa using hx)
    refine Set.mem_add.mpr ⟨J (toWeakSpace 𝕜 F y), ⟨_, ⟨y, hy, rfl⟩, rfl⟩,
      StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual 𝕜 F (T x-y)), ?_, ?_⟩
    · change ‖NormedSpace.inclusionInDoubleDual 𝕜 F (T x-y)-0‖ ≤ ε
      rw [sub_zero]
      change ‖NormedSpace.inclusionInDoubleDualLi 𝕜 (T x-y)‖ ≤ ε
      rwa [(NormedSpace.inclusionInDoubleDualLi 𝕜 (E := F)).norm_map]
    · apply DFunLike.ext
      intro φ
      change φ y + φ (T x-y) = φ (T x)
      rw [map_sub]
      abel
  have hm := closure_minimal hsub hc (goldstine_unitBall ξ hξ)
  obtain ⟨z, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, η, hη, he⟩ := Set.mem_add.mp hm
  refine ⟨y, hy, ?_⟩
  have heq : bidualMap T ξ - NormedSpace.inclusionInDoubleDual 𝕜 F y =
      WeakDual.toStrongDual η := by
    apply ContinuousLinearMap.ext
    intro φ
    have hh := DFunLike.congr_fun he φ
    change φ y + η φ = bidualMap T ξ φ at hh
    change bidualMap T ξ φ - φ y = η φ
    exact sub_eq_of_eq_add (by simpa only [add_comm] using hh.symm)
  rw [heq]
  simpa only [B, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hη

end ThesisCommon
