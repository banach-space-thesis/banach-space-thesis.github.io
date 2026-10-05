import ThesisCommon.Analysis.MeasureAlgebraL1

/-! The identity measure-algebra isomorphism and its actual L1 lift. -/
noncomputable section
open MeasureTheory

namespace ThesisCommon.MeasureAlgebraIso
variable {X : Type*} [MeasurableSpace X]

def refl (μ : Measure X) : MeasureAlgebraIso μ μ where
  toEquiv := Equiv.refl _
  map_compl := fun _ => rfl
  map_iUnion := fun _ _ _ => rfl
  measure_eq := fun _ => rfl

theorem refl_lOneEquiv_apply (μ : Measure X) [IsFiniteMeasure μ] (f : Lp ℝ 1 μ) :
    (refl μ).lOneEquiv f = f := by
  have h : (refl μ).lOneMap = ContinuousLinearMap.id ℝ (Lp ℝ 1 μ) := by
    apply lOne_continuousLinearMap_ext_indicators
    intro s hs
    exact (refl μ).lOneEquiv_indicator_of_mk_eq s hs s hs rfl
  exact DFunLike.congr_fun h f

theorem refl_lOneEquiv (μ : Measure X) [IsFiniteMeasure μ] :
    (refl μ).lOneEquiv = LinearIsometryEquiv.refl ℝ (Lp ℝ 1 μ) := by
  apply LinearIsometryEquiv.ext
  intro f
  exact refl_lOneEquiv_apply μ f

end ThesisCommon.MeasureAlgebraIso
