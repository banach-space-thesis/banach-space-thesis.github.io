import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Gluing almost-everywhere local constants on a preconnected region

Positive measure of nonempty open intersections gives uniqueness of the local
values. Preconnectedness glues those values, and second countability glues the
local null exceptional sets.
-/

namespace BanachIsometric

open MeasureTheory Set Filter Metric
open scoped Topology

theorem exists_ae_eq_const_on_of_ae_locally_constant
    {X Y : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [Nonempty Y] (μ : Measure X) [Measure.IsOpenPosMeasure μ]
    {f : X → Y} {U : Set X} (hU : IsPreconnected U)
    (hlocal : ∀ x ∈ U, ∃ r > 0, ∃ D : Y, ∀ᵐ y ∂μ, y ∈ ball x r → f y = D) :
    ∃ D : Y, ∀ᵐ y ∂μ, y ∈ U → f y = D := by
  classical
  by_cases hnonempty : U.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hnonempty
    have hloc : ∀ x : U, ∃ r > 0, ∃ D : Y,
        ∀ᵐ y ∂μ, y ∈ ball (x : X) r → f y = D := fun x => hlocal x x.property
    choose r hr D hD using hloc
    have huniq (x z : U) (hz : (z : X) ∈ ball (x : X) (r x)) : D z = D x := by
      let V : Set X := ball (x : X) (r x) ∩ ball (z : X) (r z)
      have hV : μ V ≠ 0 :=
        (isOpen_ball.inter isOpen_ball).measure_ne_zero μ
          ⟨(z : X), hz, mem_ball_self (hr z)⟩
      have hae : ∀ᵐ y ∂μ, y ∈ V → D z = D x := by
        filter_upwards [hD x, hD z] with y hyx hyz
        intro hy
        exact (hyz hy.2).symm.trans (hyx hy.1)
      obtain ⟨y, hy, heq⟩ :=
        Measure.exists_mem_of_measure_ne_zero_of_ae hV (ae_restrict_of_ae hae)
      exact heq hy
    have hDlocal : IsLocallyConstant D := by
      apply (IsLocallyConstant.iff_eventually_eq D).mpr
      intro x
      have hball : ∀ᶠ z : U in 𝓝 x, (z : X) ∈ ball (x : X) (r x) :=
        (continuous_subtype_val.tendsto x).eventually (ball_mem_nhds (x : X) (hr x))
      exact hball.mono (fun z hz => huniq x z hz)
    letI : PreconnectedSpace U := Subtype.preconnectedSpace hU
    let base : Y := D ⟨x₀, hx₀⟩
    have hDconst (x : U) : D x = base := hDlocal.apply_eq_of_preconnectedSpace x ⟨x₀, hx₀⟩
    refine ⟨base, ?_⟩
    apply ae_iff.mpr
    change μ {y | ¬ (y ∈ U → f y = base)} = 0
    simp only [_root_.not_imp]
    let bad : Set X := {y | y ∈ U ∧ f y ≠ base}
    change μ bad = 0
    apply measure_null_of_locally_null bad
    intro x hx
    let p : U := ⟨x, hx.1⟩
    have hae : ∀ᵐ y ∂μ, y ∈ ball x (r p) → f y = base := by
      simpa only [hDconst p] using hD p
    have hzero : μ {y | y ∈ ball x (r p) ∧ f y ≠ base} = 0 := by
      simpa only [ae_iff, _root_.not_imp] using hae
    refine ⟨bad ∩ ball x (r p),
      inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr p))), ?_⟩
    apply measure_mono_null _ hzero
    intro y hy
    exact ⟨hy.2, hy.1.2⟩
  · refine ⟨Classical.arbitrary Y, ae_of_all _ ?_⟩
    intro y hy
    exact (hnonempty ⟨y, hy⟩).elim

end BanachIsometric
