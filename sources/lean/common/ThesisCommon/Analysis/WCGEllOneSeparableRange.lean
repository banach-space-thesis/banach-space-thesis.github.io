import ThesisCommon.Analysis.RCLikeEllOneWeakCompact
import ThesisCommon.Analysis.UniformPrimariness

/-! Operators from WCG spaces to arbitrary scalar ℓ₁ sums have separable
range. The weakly compact generating set has norm-compact image by Schur;
the image of the dense linear span lies in the separable closed image span.
-/
noncomputable section
open Set TopologicalSpace
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The separable-range input in the WCG alternative of Corollary 4.16. -/
theorem IsWeaklyCompactlyGenerated.ellOne_operator_separable_range
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (S : X →L[𝕜] lp (fun _ : Γ => 𝕜) 1) : IsSeparable (Set.range S) := by
  obtain ⟨K, hK, hspan⟩ := hX
  have hcompact : IsCompact (S '' K) := by
    have h := isCompact_norm_of_weakScalarEllOne
      (hK.image (WeakSpace.map S).continuous)
    simpa only [Set.image_image, Function.comp_def, WeakSpace.map_apply,
      toWeakSpace, LinearEquiv.refl_apply] using h
  have hsep := (hcompact.isSeparable.span (R := 𝕜)).closure
  apply hsep.mono
  rintro _ ⟨x, rfl⟩
  have hmap := Submodule.topologicalClosure_map S (Submodule.span 𝕜 K)
  rw [hspan] at hmap
  have hx : S x ∈ ((Submodule.span 𝕜 K).map S.toLinearMap).topologicalClosure :=
    hmap ⟨x, Submodule.mem_top, rfl⟩
  simpa only [Submodule.map_span] using hx

end ThesisCommon
