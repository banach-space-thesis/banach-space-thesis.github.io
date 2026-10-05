import ThesisCommon.Analysis.FiniteCoefficientTransfer
import ThesisCommon.Analysis.SequenceSpaces

/-! Finite ordinal coefficient spaces are actual nonzero finite-dimensional
continuous-function spaces. Their infinite sums are covered by the genuine
finite-coefficient absorption maps, without any coefficient PFP assumption. -/
noncomputable section
open Set
namespace ThesisCommon
universe u

theorem ordinalInterval_finite {α : Ordinal.{u}}
    (hα : α < Ordinal.omega0) : Finite (OrdinalInterval α) := by
  have hIio : Finite (Set.Iio α) := by
    apply Cardinal.lt_aleph0_iff_finite.mp
    rw [Ordinal.mk_Iio_ordinal, Cardinal.lift_lt_aleph0]
    exact Ordinal.card_lt_aleph0.mpr hα
  have hIcc : (Set.Icc 0 α).Finite :=
    ((Set.toFinite (Set.Iio α)).union (Set.finite_singleton α)).subset (by
      intro β hβ
      rcases lt_or_eq_of_le hβ.2 with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq)
  exact hIcc.to_subtype

theorem ordinalContinuous_nontrivial (𝕜 : Type*) [RCLike 𝕜] (α : Ordinal.{u}) :
    Nontrivial (OrdinalContinuous 𝕜 α) := by
  refine ⟨⟨ContinuousMap.const _ 0, ContinuousMap.const _ 1, ?_⟩⟩
  intro h
  have hh := congrArg (fun f : OrdinalContinuous 𝕜 α =>
    f ⟨0, le_rfl, Ordinal.zero_le α⟩) h
  exact zero_ne_one hh

theorem ordinalContinuous_finiteDimensional (𝕜 : Type*) [RCLike 𝕜]
    {α : Ordinal.{u}} (hα : α < Ordinal.omega0) :
    FiniteDimensional 𝕜 (OrdinalContinuous 𝕜 α) := by
  letI := ordinalInterval_finite hα
  letI := Fintype.ofFinite (OrdinalInterval α)
  exact FiniteDimensional.of_injective (ContinuousMap.coeFnLinearMap 𝕜)
    DFunLike.coe_injective

end ThesisCommon
