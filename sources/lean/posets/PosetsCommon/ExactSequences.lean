import PosetsCommon.Algebra

noncomputable section
namespace ThesisCommon
variable {𝕜 I A B : Type*} [RCLike 𝕜]
    [NormedAddCommGroup I] [NormedSpace 𝕜 I] [Mul I]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A] [Mul A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B] [Mul B]

/-- Definition 2.1: injective inclusion, surjective quotient, and exact kernel. -/
def ShortExact (j : BoundedHom 𝕜 I A) (θ : BoundedHom 𝕜 A B) : Prop :=
  Function.Injective j ∧ Function.Surjective θ ∧
    ∀ a, θ a = 0 ↔ a ∈ Set.range j

/-- Definition 2.2: short exactness and a continuous multiplicative right inverse. -/
def StronglySplit (j : BoundedHom 𝕜 I A) (θ : BoundedHom 𝕜 A B) : Prop :=
  ShortExact j θ ∧ ∃ ρ : BoundedHom 𝕜 B A, Function.RightInverse ρ θ

end ThesisCommon
