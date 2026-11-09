import BanachIsometric.ConnectedReductionMap

/-! The constructed connected reduction respects the actual right subgroup
action on principal coordinates. -/

noncomputable section

namespace BanachIsometric.ExactSectionAtlas

open Set Bundle

variable {P E F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    (Z : BanachIsometric.ExactSectionAtlas S K H)
    (s : C(P, Z.componentCore.TotalSpace)) (hs : ∀ a, Z.componentCore.proj (s a) = a)
    (hopen : IsOpen (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) :
      Set (bodyAutomorphismGroup S)))

theorem connectedReductionToPrincipal_right
    (t : (Z.connectedReductionCore s hs hopen).TotalSpace)
    (g : Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) :
    Z.connectedReductionToPrincipal s hs hopen
        ⟨t.1, (show Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) from t.2) * g⟩ =
      ⟨t.1, (show bodyAutomorphismGroup S from
        (Z.connectedReductionToPrincipal s hs hopen t).2) * (g : bodyAutomorphismGroup S)⟩ := by
  apply Bundle.TotalSpace.ext
  · rfl
  apply heq_of_eq
  change Z.componentRepresentative s t.1 *
      (((show Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) from t.2) :
        bodyAutomorphismGroup S) * (g : bodyAutomorphismGroup S)) = _
  exact (mul_assoc _ _ _).symm

end BanachIsometric.ExactSectionAtlas
