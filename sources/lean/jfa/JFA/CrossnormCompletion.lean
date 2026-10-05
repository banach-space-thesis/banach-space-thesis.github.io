import JFA.TensorProducts

/-! A concrete completion for every reasonable crossnorm. This makes the
completion quantifier in Theorem 1.1 nonvacuous for every supplied assignment. -/

noncomputable section
open scoped TensorProduct
namespace JFA.ReasonableCrossnorm
universe u
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E X : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (p : ReasonableCrossnorm 𝕜 E X)

/-- A type synonym to keep different tensor norms from sharing metric instances. -/
def Algebraic (_p : ReasonableCrossnorm 𝕜 E X) := E ⊗[𝕜] X

instance : AddCommGroup p.Algebraic := inferInstanceAs (AddCommGroup (E ⊗[𝕜] X))
instance : Module 𝕜 p.Algebraic := inferInstanceAs (Module 𝕜 (E ⊗[𝕜] X))
instance : Norm p.Algebraic := ⟨fun z => p.seminorm z⟩

def normCore : NormedSpace.Core 𝕜 p.Algebraic where
  norm_nonneg := apply_nonneg p.seminorm
  norm_smul := map_smul_eq_mul p.seminorm
  norm_triangle := map_add_le_add p.seminorm
  norm_eq_zero_iff z := ⟨p.definite z, fun hz => hz ▸ map_zero p.seminorm⟩

instance : NormedAddCommGroup p.Algebraic := NormedAddCommGroup.ofCore p.normCore
instance : NormedSpace 𝕜 p.Algebraic := NormedSpace.ofCore p.normCore

abbrev Completion := UniformSpace.Completion p.Algebraic

def inclusion : E ⊗[𝕜] X →ₗ[𝕜] p.Completion :=
  (UniformSpace.Completion.toComplₗᵢ : p.Algebraic →ₗᵢ[𝕜] p.Completion).toLinearMap

theorem isTensorCompletion : IsTensorCompletion 𝕜 E X p.Completion p p.inclusion := by
  refine ⟨(UniformSpace.Completion.toComplₗᵢ :
    p.Algebraic →ₗᵢ[𝕜] p.Completion).injective, ?_, ?_⟩
  · exact UniformSpace.Completion.denseRange_coe (α := p.Algebraic)
  · intro z
    exact (UniformSpace.Completion.toComplₗᵢ :
      p.Algebraic →ₗᵢ[𝕜] p.Completion).norm_map z

end JFA.ReasonableCrossnorm
