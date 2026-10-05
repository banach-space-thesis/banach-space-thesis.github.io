import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.WeakDual

/-! A continuous linear functional on a weak dual is evaluation at a vector.
This expands the finite-family continuity argument needed by Goldstine. -/
noncomputable section
open Set Topology TopologicalSpace
namespace ThesisCommon
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

theorem weakDual_functional_eq_eval (ψ : WeakDual 𝕜 E →L[𝕜] 𝕜) :
    ∃ x : E, ∀ f : WeakDual 𝕜 E, ψ f = f x := by
  let B := (topDualPairing 𝕜 E).flip
  have hcont : Continuous[⨅ x : E, induced (B x) inferInstance, inferInstance] ψ := by
    have htop : (inferInstance : TopologicalSpace (WeakDual 𝕜 E)) =
        ⨅ x : E, induced (B x) inferInstance := by
      change induced (fun f : WeakDual 𝕜 E => fun x : E => f x) Pi.topologicalSpace = _
      rw [induced_to_pi]
      rfl
    exact htop ▸ ψ.continuous
  have hm : ψ.toLinearMap ∈ Submodule.span 𝕜 (range B) :=
    (LinearMap.mem_span_iff_continuous ψ.toLinearMap).mpr hcont
  have hm' : ψ.toLinearMap ∈ LinearMap.range B :=
    (Submodule.span_le.mpr (fun _ h => h)) hm
  obtain ⟨x, hx⟩ := hm'
  refine ⟨x, fun f => ?_⟩
  exact (LinearMap.congr_fun hx f).symm

end ThesisCommon
