import BanachIsometric.ExactSectionBundleConstruction

/-! A continuous section of the constructed Mathlib bundle is an actual
continuous operator section in the original topology. -/

namespace BanachIsometric

noncomputable section

open Set

namespace ExactSectionAtlas

variable {P E F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    (Z : ExactSectionAtlas S K H)

theorem exists_continuous_operator_section_of_bundle_section
    (σ : P → Z.fiberBundleCore.TotalSpace) (hσ : Continuous σ)
    (hbase : ∀ a, (σ a).proj = a) :
    ∃ A : C(P, E →L[ℝ] F), ∀ a,
      Function.Injective (A a) ∧ LinearMap.range (A a).toLinearMap = H a ∧
        A a '' S = K ∩ (H a : Set F) := by
  let t := fun a => Z.actualHomeomorph (σ a)
  have ht : Continuous t := Z.actualHomeomorph.continuous.comp hσ
  let A : C(P, E →L[ℝ] F) :=
    ⟨fun a => (t a).val.2, continuous_snd.comp (continuous_subtype_val.comp ht)⟩
  refine ⟨A, ?_⟩
  intro a
  have ha : (t a).val.1 = a := hbase a
  simpa only [ha] using (t a).property

end ExactSectionAtlas

end
end BanachIsometric
