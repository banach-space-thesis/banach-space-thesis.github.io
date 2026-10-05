import Posets.Models

/-! Turn the paper's exact-range representations into algebra coordinates. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets

variable {𝕜 C E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem representedBy_subalgebra_coordinates (S : Subalgebra 𝕜 (E →L[𝕜] E))
    (h : RepresentedBy 𝕜 C E (S : Set (E →L[𝕜] E))) :
    IsometricallyIsomorphic 𝕜 C S := by
  obtain ⟨f, hf, hr⟩ := h
  let g : C →ₗᵢ[𝕜] S :=
    { toLinearMap := f.toContinuousLinearMap.toLinearMap.codRestrict S.toSubmodule
        (fun x => by change f x ∈ (S : Set (E →L[𝕜] E)); rw [← hr]; exact ⟨x, rfl⟩)
      norm_map' := fun x =>
        (AddMonoidHomClass.isometry_iff_norm f.toContinuousLinearMap).mp hf x }
  have hg : Function.Surjective g := by
    intro y
    have hy : y.val ∈ Set.range f := by rw [hr]; exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨LinearIsometryEquiv.ofSurjective g hg, ?_⟩
  intro a b
  apply Subtype.ext
  exact f.map_mul' a b

theorem representedBy_univ_coordinates (h : RepresentedBy 𝕜 C E Set.univ) :
    IsometricallyIsomorphic 𝕜 C (E →L[𝕜] E) := by
  obtain ⟨f, hf, hr⟩ := h
  let g : C →ₗᵢ[𝕜] (E →L[𝕜] E) :=
    { toLinearMap := f.toContinuousLinearMap.toLinearMap
      norm_map' := fun x =>
        (AddMonoidHomClass.isometry_iff_norm f.toContinuousLinearMap).mp hf x }
  have hg : Function.Surjective g := by
    intro y
    have hy : y ∈ Set.range f := by rw [hr]; trivial
    exact hy
  exact ⟨LinearIsometryEquiv.ofSurjective g hg, f.map_mul'⟩

end Posets
