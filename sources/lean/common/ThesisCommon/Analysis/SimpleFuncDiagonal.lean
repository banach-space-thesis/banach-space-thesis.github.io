import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic

/-! Finite measurable selection preserves simultaneous almost-everywhere
statements and integrability. This is the finite-pattern null-set argument
used to turn L1 operator values into a content on product sets. -/
noncomputable section
open MeasureTheory Set Filter
local infixr:25 " →ₛ " => MeasureTheory.SimpleFunc
namespace ThesisCommon
variable {Y I : Type*} [MeasurableSpace Y] {ν : Measure Y}

theorem simpleFunc_ae_bind (q : Y →ₛ I) {p : I → Y → Prop}
    (hp : ∀ i, ∀ᵐ y ∂ν, p i y) : ∀ᵐ y ∂ν, p (q y) y := by
  classical
  have h : ∀ i : q.range, ∀ᵐ y ∂ν, p i.val y := fun i => hp i.val
  filter_upwards [ae_all_iff.mpr h] with y hy
  exact hy ⟨q y, q.mem_range_self y⟩

theorem simpleFunc_integrable_bind (q : Y →ₛ I) (g : I → Y → ℝ)
    (hgm : ∀ i, Measurable (g i)) (hgi : ∀ i, Integrable (g i) ν) :
    Integrable (fun y => g (q y) y) ν := by
  classical
  have hsum : Integrable (fun y => ∑ i ∈ q.range, ‖g i y‖) ν :=
    integrable_finset_sum _ (fun i _ => (hgi i).norm)
  apply hsum.mono' (q.measurable_bind g hgm).aestronglyMeasurable
  exact Eventually.of_forall fun y =>
    Finset.single_le_sum (fun i _ => norm_nonneg (g i y)) (q.mem_range_self y)

end ThesisCommon
