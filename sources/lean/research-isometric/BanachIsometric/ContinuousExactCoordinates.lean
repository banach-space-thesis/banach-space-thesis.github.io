import BanachIsometric.ExactSectionBundleConstruction

/-! The genuine torsor coordinate between continuous exact operator families
is continuous. The proof reads both families in the already constructed actual
principal atlas, rather than assuming continuity of chosen linear inverses. -/

noncomputable section

namespace BanachIsometric.ExactSectionAtlas

open Set Filter
open scoped Topology

variable {P E F Q : Type*} [PseudoMetricSpace P] [TopologicalSpace Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    (Z : BanachIsometric.ExactSectionAtlas S K H)
    (f : C(Q, P)) (A B : C(Q, E →L[ℝ] F))
    (hA : ∀ x, Function.Injective (A x) ∧ LinearMap.range (A x).toLinearMap = H (f x) ∧
      A x '' S = K ∩ (H (f x) : Set F))
    (hB : ∀ x, Function.Injective (B x) ∧ LinearMap.range (B x).toLinearMap = H (f x) ∧
      B x '' S = K ∩ (H (f x) : Set F))

def exactCoordinateFamily (x : Q) : bodyAutomorphismGroup S :=
  exactBodyMapCoordinate (⟨A x, hA x⟩ : ExactBodyMap S K (H (f x))) ⟨B x, hB x⟩

def exactOperatorFamily : C(Q, ExactSectionSpace S K H) :=
  ⟨fun x => ⟨(f x, A x), hA x⟩, (f.continuous.prodMk A.continuous).subtype_mk _⟩

theorem exactCoordinateFamily_right (x : Q) :
    exactSectionRight (exactOperatorFamily f A hA x) (exactCoordinateFamily f A B hA hB x) =
      exactOperatorFamily f B hB x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  exact congrArg Subtype.val (exactBodyMapRight_coordinate
    (⟨A x, hA x⟩ : ExactBodyMap S K (H (f x))) ⟨B x, hB x⟩)

theorem exactCoordinateFamily_chart_formula (i : P) (x : Q) (hi : f x ∈ Z.baseSet i) :
    exactCoordinateFamily f A B hA hB x =
      (Z.actualTrivialization i (exactOperatorFamily f A hA x)).2⁻¹ *
        (Z.actualTrivialization i (exactOperatorFamily f B hB x)).2 := by
  have he := congrArg (fun t => (Z.actualTrivialization i t).2)
    (exactCoordinateFamily_right f A B hA hB x)
  change (Z.actualTrivialization i (exactSectionRight
    (exactOperatorFamily f A hA x) (exactCoordinateFamily f A B hA hB x))).2 =
      (Z.actualTrivialization i (exactOperatorFamily f B hB x)).2 at he
  rw [Z.actualTrivialization_right_equivariant i _ hi] at he
  calc
    exactCoordinateFamily f A B hA hB x =
        (Z.actualTrivialization i (exactOperatorFamily f A hA x)).2⁻¹ *
          ((Z.actualTrivialization i (exactOperatorFamily f A hA x)).2 *
            exactCoordinateFamily f A B hA hB x) := (inv_mul_cancel_left _ _).symm
    _ = _ := congrArg (fun g => (Z.actualTrivialization i (exactOperatorFamily f A hA x)).2⁻¹ * g) he

include Z in
theorem continuous_exactCoordinateFamily : Continuous (exactCoordinateFamily f A B hA hB) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let i := f x
  have hi : f x ∈ Z.baseSet i := Z.mem_baseSet (f x)
  have hAm : exactOperatorFamily f A hA x ∈ (Z.actualTrivialization i).source :=
    (Z.actualTrivialization i).mem_source.mpr hi
  have hBm : exactOperatorFamily f B hB x ∈ (Z.actualTrivialization i).source :=
    (Z.actualTrivialization i).mem_source.mpr hi
  have hAc : ContinuousAt (fun y => (Z.actualTrivialization i (exactOperatorFamily f A hA y)).2) x :=
    continuous_snd.continuousAt.comp (((Z.actualTrivialization i).continuousAt hAm).comp
      (exactOperatorFamily f A hA).continuous.continuousAt)
  have hBc : ContinuousAt (fun y => (Z.actualTrivialization i (exactOperatorFamily f B hB y)).2) x :=
    continuous_snd.continuousAt.comp (((Z.actualTrivialization i).continuousAt hBm).comp
      (exactOperatorFamily f B hB).continuous.continuousAt)
  apply (hAc.inv.mul hBc).congr_of_eventuallyEq
  filter_upwards [((Z.isOpen_baseSet i).preimage f.continuous).mem_nhds hi] with y hy
  exact Z.exactCoordinateFamily_chart_formula f A B hA hB i y hy

end BanachIsometric.ExactSectionAtlas
