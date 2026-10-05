import PFP.OrdinalMatrixHeadSpan
import JLMS.OrdinalCountableTails

/-! A map from a smaller ordinal function space has its whole image constant
on one common tail. The domain-size bound is on the actual ordinal cardinal. -/
noncomputable section
namespace Posets.UniverseRegularMatrix
universe ordU
open Posets.UniverseRegularInitial
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096

theorem exists_smallFamily_ordinal_tail {κ σ : Ordinal.{ordU}}
    (hκ : Cardinal.aleph0 < κ.cof) (hσ : σ.card < κ.cof)
    (f : ∀ γ < σ, OrdinalC 𝕜 κ) :
    ∃ β < κ, ∀ γ (hγ : γ < σ), f γ hγ ∈ ordinalTailSpace κ β := by
  have h (γ : Ordinal.{ordU}) (hγ : γ < σ) := exists_constant_ordinalC_tail hκ (f γ hγ)
  choose b hb hf using h
  refine ⟨Ordinal.bsup σ b, Ordinal.bsup_lt_ord hσ hb, ?_⟩
  intro γ hγ x hx
  exact hf γ hγ x ((Ordinal.le_bsup b γ hγ).trans_lt hx)

theorem exists_smallDomain_operator_tail {κ σ : Ordinal.{ordU}}
    (hκ : Cardinal.aleph0 < κ.cof) (hσ : σ.card < κ.cof)
    (T : OrdinalC 𝕜 σ →L[𝕜] OrdinalC 𝕜 κ) :
    ∃ β < κ, ∀ f, T f ∈ ordinalTailSpace κ β := by
  have hs : (Order.succ σ).card < κ.cof := by
    rw [Ordinal.card_succ]
    exact Cardinal.add_lt_of_lt hκ.le hσ (Cardinal.one_lt_aleph0.trans hκ)
  obtain ⟨β, hβ, hf⟩ := exists_smallFamily_ordinal_tail hκ hs
    (fun γ _ => T (ordinalHeadIndicator σ γ))
  let S : Submodule 𝕜 (OrdinalC 𝕜 σ) :=
    (ordinalTailSpace κ β).comap T.toLinearMap
  have hSclosed : IsClosed (S : Set (OrdinalC 𝕜 σ)) :=
    (ordinalTailSpace_isClosed κ β).preimage T.continuous
  have hspan : Submodule.span 𝕜 (Set.range (fun γ : OrdinalInterval σ =>
      ordinalHeadIndicator (𝕜 := 𝕜) σ γ.val)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro f ⟨γ, rfl⟩
    exact hf γ.val (Order.lt_succ_iff.mpr γ.property.2)
  have htop : (⊤ : Submodule 𝕜 (OrdinalC 𝕜 σ)) ≤ S := by
    rw [← ordinalHeadIndicators_dense σ]
    exact Submodule.topologicalClosure_minimal _ hspan hSclosed
  exact ⟨β, hβ, fun f => htop (Submodule.mem_top)⟩

end Posets.UniverseRegularMatrix


