import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Quotient.Basic

/-! A closed subspace is determined by the continuous functionals vanishing on it. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem mem_closedSubmodule_iff_dual (p : Submodule 𝕜 E) (hp : IsClosed (p : Set E))
    (x : E) : x ∈ p ↔ ∀ f : StrongDual 𝕜 E, (∀ y ∈ p, f y = 0) → f x = 0 := by
  constructor
  · exact fun hx f hf => hf x hx
  · intro hx
    letI : IsClosed (p : Set E) := hp
    let Q : E →L[𝕜] E ⧸ p :=
      { toLinearMap := p.mkQ
        cont := continuous_quot_mk }
    have hzero : Q x = 0 := by
      apply NormedSpace.eq_zero_of_forall_dual_eq_zero 𝕜
      intro f
      apply hx (f.comp Q)
      intro y hy
      have hy0 : Q y = 0 := (Submodule.Quotient.mk_eq_zero p).mpr hy
      simp only [ContinuousLinearMap.comp_apply, hy0, map_zero]
    exact (Submodule.Quotient.mk_eq_zero p).mp hzero

end ThesisCommon
