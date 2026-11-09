import Mathlib.Topology.MetricSpace.Basic
import Mathlib.SetTheory.Cardinal.Continuum

/-! Cardinal bounds for the actual separable metric ranges of compact operators. -/

noncomputable section
set_option autoImplicit false
open TopologicalSpace

namespace SurveyStatements.P2
universe v
variable (Y : Type v) [MetricSpace Y] [SecondCountableTopology Y]

/-- A point is determined by membership in the countable topological basis. -/
def pointBasisCode (x : Y) : Set (countableBasis Y) := {b | x ∈ b.val}

theorem pointBasisCode_injective : Function.Injective (pointBasisCode Y) := by
  intro x y hcode
  by_contra hxy
  have hd : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨b, hb, hxb, hbball⟩ :=
    (isBasis_countableBasis Y).isOpen_iff.mp Metric.isOpen_ball x
      (Metric.mem_ball_self hd)
  have hyb : y ∈ b := by
    have hxcode : (⟨b, hb⟩ : countableBasis Y) ∈ pointBasisCode Y x := hxb
    rw [hcode] at hxcode
    exact hxcode
  have hyball := hbball hyb
  have hlt : dist y x < dist x y := hyball
  rw [dist_comm] at hlt
  exact lt_irrefl _ hlt

theorem mk_le_continuum_of_secondCountable_metric :
    Cardinal.mk Y ≤ Cardinal.continuum := by
  calc
    Cardinal.mk Y ≤ Cardinal.mk (Set (countableBasis Y)) :=
      Cardinal.mk_le_of_injective (pointBasisCode_injective Y)
    _ = 2 ^ Cardinal.mk (countableBasis Y) := Cardinal.mk_set
    _ ≤ 2 ^ Cardinal.aleph0 := Cardinal.power_le_power_left (by simp) Cardinal.mk_le_aleph0
    _ = Cardinal.continuum := rfl

theorem mk_le_continuum_of_separable_metric (Z : Type v) [MetricSpace Z] [SeparableSpace Z] :
    Cardinal.mk Z ≤ Cardinal.continuum :=
  mk_le_continuum_of_secondCountable_metric Z

theorem not_separableSpace_of_continuum_lt_mk (Z : Type v) [MetricSpace Z]
    (hZ : Cardinal.continuum < Cardinal.mk Z) : ¬ SeparableSpace Z := by
  intro hs
  letI := hs
  exact not_le_of_gt hZ (mk_le_continuum_of_separable_metric Z)

end SurveyStatements.P2
