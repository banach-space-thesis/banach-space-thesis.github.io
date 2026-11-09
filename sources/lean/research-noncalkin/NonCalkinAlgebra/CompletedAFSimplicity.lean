import NonCalkinAlgebra.CompletedAFSystem
import NonCalkinAlgebra.ClosedIdealQuotient
import NonCalkinAlgebra.FiniteCStarEmbedding

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.NormedStarDirectLimit
open UniformSpace SurveyStatements.P2
open scoped NonCalkinAlgebra.NormedStarCompletion

universe u v
variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {A : ι → Type v} [∀ i, CStarAlgebra (A i)] [∀ i, FiniteDimensional ℂ (A i)]
variable (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
variable [DirectedSystem A (f · · ·)] [PreservesNorm f] [∀ i, NormOneClass (A i)]

instance completedNormOneClass : NormOneClass (Completed f) where
  norm_one := by
    change ‖((1 : Carrier f) : Completed f)‖ = 1
    rw [Completion.norm_coe, norm_one]

instance completedCStarAlgebra : CStarAlgebra (Completed f) where

/-- It suffices that every finite stage injects into every nonzero unital quotient of
the limit. In a full block refinement this follows by taking one later mixing stage. -/
theorem completed_simple
    (hmix : ∀ i, ∃ j, ∃ h : i ≤ j, ∀ (B : Type (max u v)) [Ring B] [Algebra ℂ B]
      [Nontrivial B] (g : A j →ₐ[ℂ] B), Function.Injective (g.comp (f i j h).toAlgHom)) :
    IsTopologicallySimple (Completed f) := by
  intro I hI
  by_cases htop : I = ⊤
  · exact Or.inr htop
  letI : IsClosed (I : Set (Completed f)) := hI
  letI : Nontrivial (ClosedIdealQuotient.Space I) :=
    ClosedIdealQuotient.quotient_nontrivial I htop
  let q := ClosedIdealQuotient.qStarAlgHom I
  have hnorm : ∀ a : Completed f, ‖q a‖ = ‖a‖ := by
    intro a
    refine Completion.induction_on a
      (isClosed_eq (continuous_norm.comp (ClosedIdealQuotient.qCLM I).continuous)
        continuous_norm) ?_
    intro z
    let coe (x : DirectLimit A f) : Completed f := ((show Carrier f from x) : Completed f)
    refine DirectLimit.induction f (C := fun x => ‖q (coe x)‖ = ‖coe x‖) ?_ z
    intro i x
    obtain ⟨j, hij, hm⟩ := hmix i
    let fᵢ := q.comp (completedEmbedding f i)
    let fⱼ := q.comp (completedEmbedding f j)
    have hf : Function.Injective fᵢ := by
      have hEq (x : A i) : fⱼ (f i j hij x) = fᵢ x :=
        congrArg q (completedEmbedding_map f hij x)
      intro x y hxy
      exact hm _ fⱼ.toAlgHom ((hEq x).trans (hxy.trans (hEq y).symm))
    change ‖fᵢ x‖ = ‖completedEmbedding f i x‖
    rw [completedEmbedding_norm]
    apply le_antisymm _ (norm_le_starAlgHom_of_finiteDimensional fᵢ hf x)
    calc
      ‖fᵢ x‖ ≤ ‖completedEmbedding f i x‖ :=
        Submodule.Quotient.norm_mk_le (ClosedIdealQuotient.submodule I) _
      _ = ‖x‖ := completedEmbedding_norm f i x
  left
  apply le_antisymm _ bot_le
  intro a ha
  change a = 0
  apply norm_eq_zero.mp
  rw [← hnorm a]
  change ‖ClosedIdealQuotient.q I a‖ = 0
  rw [(ClosedIdealQuotient.q_eq_zero I a).mpr ha, norm_zero]

end NonCalkinAlgebra.NormedStarDirectLimit
