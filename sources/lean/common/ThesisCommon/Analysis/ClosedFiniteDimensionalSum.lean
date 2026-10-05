import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Basic

/-! A closed linear subspace plus a finite-dimensional subspace is closed,
proved via the actual normed quotient by the closed subspace. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem submodule_isClosed_sup_of_finiteDimensional_right
    (M N : Submodule 𝕜 X) (hM : IsClosed (M : Set X)) [FiniteDimensional 𝕜 N] :
    IsClosed ((M ⊔ N : Submodule 𝕜 X) : Set X) := by
  letI := hM
  have hn := (N.map M.mkQ).closed_of_finiteDimensional
  have he : (N.map M.mkQ).comap M.mkQ = M ⊔ N := by
    rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_comm]
  have hh := hn.preimage M.isOpenQuotientMap_mkQ.continuous
  change IsClosed (((N.map M.mkQ).comap M.mkQ : Submodule 𝕜 X) : Set X) at hh
  rwa [he] at hh

end ThesisCommon
