import NonCalkinAlgebra.ClosedIdealQuotient
import NonCalkinAlgebra.FiniteCStarEmbedding
import Mathlib.RingTheory.SimpleRing.Basic

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe u
variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

/-- A unital C*-algebra with a dense union of algebraically simple
finite-dimensional unital *-subalgebras is topologically simple.
This is the simplicity step for approximately matricial algebras. -/
theorem topologically_simple_of_dense_simple_finiteDimensional_starSubalgebras
    (S : Set (StarSubalgebra ℂ A))
    (hfinite : ∀ B ∈ S, FiniteDimensional ℂ B)
    (hsimple : ∀ B ∈ S, IsSimpleRing B)
    (hdense : Dense (⋃ B ∈ S, (B : Set A))) : IsTopologicallySimple A := by
  intro I hI
  by_cases htop : I = ⊤
  · exact Or.inr htop
  letI : IsClosed (I : Set A) := hI
  letI : Nontrivial (ClosedIdealQuotient.Space I) :=
    ClosedIdealQuotient.quotient_nontrivial I htop
  have hnorm : ∀ a : A, ‖ClosedIdealQuotient.q I a‖ = ‖a‖ := by
    have hc : IsClosed {a : A | ‖ClosedIdealQuotient.q I a‖ = ‖a‖} :=
      isClosed_eq (continuous_norm.comp (ClosedIdealQuotient.qCLM I).continuous) continuous_norm
    have hsub : (⋃ B ∈ S, (B : Set A)) ⊆
        {a : A | ‖ClosedIdealQuotient.q I a‖ = ‖a‖} := by
      intro a ha
      obtain ⟨B, ha⟩ := Set.mem_iUnion.mp ha
      obtain ⟨hB, ha⟩ := Set.mem_iUnion.mp ha
      letI : FiniteDimensional ℂ B := hfinite B hB
      letI : IsSimpleRing B := hsimple B hB
      letI : IsClosed (B : Set A) := by
        have hc := (LinearMap.isClosedEmbedding_of_injective
          (f := B.subtype.toAlgHom.toLinearMap)
          (LinearMap.ker_eq_bot.mpr Subtype.val_injective)).isClosed_range
        change IsClosed (Set.range ((↑) : B → A)) at hc
        simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq] using hc
      let f : B →⋆ₐ[ℂ] ClosedIdealQuotient.Space I :=
        (ClosedIdealQuotient.qStarAlgHom I).comp B.subtype
      have hf : Function.Injective f := f.toRingHom.injective
      exact le_antisymm (Submodule.Quotient.norm_mk_le (ClosedIdealQuotient.submodule I) a)
        (norm_le_starAlgHom_of_finiteDimensional f hf (⟨a, ha⟩ : B))
    have hcl := closure_minimal hsub hc
    rw [hdense.closure_eq] at hcl
    exact fun a => hcl (Set.mem_univ a)
  left
  apply le_antisymm _ bot_le
  intro a ha
  change a = 0
  apply norm_eq_zero.mp
  rw [← hnorm a, (ClosedIdealQuotient.q_eq_zero I a).mpr ha, norm_zero]

end NonCalkinAlgebra
