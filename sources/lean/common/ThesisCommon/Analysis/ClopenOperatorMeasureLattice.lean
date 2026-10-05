import ThesisCommon.Analysis.ClopenOperatorMeasureOrder
import ThesisCommon.Analysis.OperatorOfProductMeasure
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-! The positive-operator product measure preserves lattice infima.
The reverse inequality is obtained by constructing an actual L1 operator
from each dominated product measure, rather than assuming a representation. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SigmaFinite ν]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [BorelSpace X] [BorelSpace Y]

theorem clopenOperatorMeasure_operatorOfProductMeasure
    (ρ : Measure (X × Y)) [IsFiniteMeasure ρ] (C : ℝ) (hC : 0 ≤ C)
    (hfst : ρ.fst ≤ ENNReal.ofReal C • μ) (hsnd : ρ.snd ≪ ν) :
    clopenOperatorMeasure (operatorOfProductMeasure μ ν ρ C hC hfst hsnd)
      (fun _ hf => operatorOfProductMeasure_nonneg μ ν ρ C hC hfst hsnd hf) = ρ := by
  apply clopenOperatorMeasure_unique
  intro a b ha hb
  exact (operatorOfProductMeasure_rectangle_ofReal μ ν ρ C hC hfst hsnd a ha b hb).symm

/-- Every measure below a positive operator measure is itself the measure
of a positive bounded operator below the original operator. -/
theorem exists_operator_of_le_clopenOperatorMeasure
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (τ : Measure (X × Y)) (hτ : τ ≤ clopenOperatorMeasure S hS) :
    ∃ (U : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hU : 0 ≤ U),
      U ≤ S ∧ clopenOperatorMeasure U hU = τ := by
  letI : IsFiniteMeasure τ := isFiniteMeasure_of_le (clopenOperatorMeasure S hS) hτ
  have hfst : τ.fst ≤ ENNReal.ofReal ‖S‖ • μ :=
    (Measure.fst_mono hτ).trans (clopenOperatorMeasure_fst_le S hS)
  have hsnd : τ.snd ≪ ν :=
    (Measure.absolutelyContinuous_of_le (Measure.snd_mono hτ)).trans
      (clopenOperatorMeasure_snd_absolutelyContinuous S hS)
  let U := operatorOfProductMeasure μ ν τ ‖S‖ (norm_nonneg S) hfst hsnd
  have hU : 0 ≤ U := fun _ hf =>
    operatorOfProductMeasure_nonneg μ ν τ ‖S‖ (norm_nonneg S) hfst hsnd hf
  have hrepr : clopenOperatorMeasure U hU = τ :=
    clopenOperatorMeasure_operatorOfProductMeasure τ ‖S‖ (norm_nonneg S) hfst hsnd
  refine ⟨U, hU, ?_, hrepr⟩
  exact (clopenOperatorMeasure_le_iff U S hU hS).mp (by rw [hrepr]; exact hτ)

theorem clopenOperatorMeasure_inf
    (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    clopenOperatorMeasure (S ⊓ T) (le_inf hS hT) =
      clopenOperatorMeasure S hS ⊓ clopenOperatorMeasure T hT := by
  apply le_antisymm
  · exact le_inf (clopenOperatorMeasure_mono _ _ (le_inf hS hT) hS inf_le_left)
      (clopenOperatorMeasure_mono _ _ (le_inf hS hT) hT inf_le_right)
  · obtain ⟨U, hU, hUS, hrepr⟩ := exists_operator_of_le_clopenOperatorMeasure S hS
      (clopenOperatorMeasure S hS ⊓ clopenOperatorMeasure T hT) inf_le_left
    have hUT : U ≤ T := (clopenOperatorMeasure_le_iff U T hU hT).mp
      (by rw [hrepr]; exact inf_le_right)
    rw [← hrepr]
    exact clopenOperatorMeasure_mono U (S ⊓ T) hU (le_inf hS hT) (le_inf hUS hUT)

theorem clopenOperatorMeasure_mutuallySingular_iff
    (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    clopenOperatorMeasure S hS ⟂ₘ clopenOperatorMeasure T hT ↔ S ⊓ T = 0 := by
  rw [Measure.mutuallySingular_iff_disjoint, disjoint_iff]
  change clopenOperatorMeasure S hS ⊓ clopenOperatorMeasure T hT = 0 ↔ _
  rw [← clopenOperatorMeasure_inf S T hS hT, clopenOperatorMeasure_eq_zero_iff]

end ThesisCommon
