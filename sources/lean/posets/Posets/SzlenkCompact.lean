import Posets.SzlenkOperator
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Compact operators have Szlenk bound one. Finite nets in the primal
compact image directly give small weak-star neighborhoods in the adjoint image. -/

noncomputable section
universe v
open Set Topology
namespace Posets
variable {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem szlenkDeriv_adjointUnitBall_compact {T : E →L[𝕜] F}
    (hT : IsCompactOperator T) {ε : ℝ} (hε : 0 < ε) :
    szlenkDeriv ε (adjointUnitBall T) = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨φ₀, hφ₀, rfl⟩ := hx.1
  have hn₀ : ‖WeakDual.toStrongDual φ₀‖ ≤ 1 := by
    simpa only [weakStarUnitBall, mem_preimage, Metric.mem_closedBall, dist_zero_right] using hφ₀
  obtain ⟨s, hs, hfin, hcover⟩ := exists_finite_cover_balls_of_isCompact_closure
    (hT.isCompact_closure_image_closedBall 1) (show 0 < ε / 8 by positivity)
  letI : Fintype s := hfin.fintype
  choose z hzmem hz using fun v : s => hs v.property
  let U : Set (WeakDual 𝕜 E) := ⋂ v : s,
    {ψ | ‖ψ (z v) - weakStarAdjoint T φ₀ (z v)‖ < ε / 8}
  have hU : IsOpen U := isOpen_iInter_of_finite (fun v =>
    isOpen_lt ((WeakDual.eval_continuous (z v)).sub continuous_const).norm continuous_const)
  have hxU : weakStarAdjoint T φ₀ ∈ U := by
    apply mem_iInter.mpr
    intro v
    simp only [mem_setOf_eq, sub_self, norm_zero]
    positivity
  have hnear : ∀ ψ ∈ adjointUnitBall T ∩ U,
      ‖WeakDual.toStrongDual ψ - WeakDual.toStrongDual (weakStarAdjoint T φ₀)‖ ≤ ε / 2 := by
    rintro ψ ⟨⟨φ, hφ, rfl⟩, hφU⟩
    have hn : ‖WeakDual.toStrongDual φ‖ ≤ 1 := by
      simpa only [weakStarUnitBall, mem_preimage, Metric.mem_closedBall, dist_zero_right] using hφ
    let θ : StrongDual 𝕜 F := WeakDual.toStrongDual φ - WeakDual.toStrongDual φ₀
    have hnθ : ‖θ‖ ≤ 2 := by
      exact (norm_sub_le _ _).trans (by linarith only [hn, hn₀])
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro w hw
    have hwmem : w ∈ Metric.closedBall (0 : E) 1 := by
      simp only [Metric.mem_closedBall, dist_zero_right, hw, le_refl]
    obtain ⟨v, hv, hvclose⟩ := mem_iUnion₂.mp (hcover ⟨w, hwmem, rfl⟩)
    let v' : s := ⟨v, hv⟩
    have hcenter := mem_iInter.mp hφU v'
    change ‖φ (T (z v')) - φ₀ (T (z v'))‖ < ε / 8 at hcenter
    have hzeq : T (z v') = v := hz v'
    rw [hzeq] at hcenter
    have hdiff : ‖T w - v‖ < ε / 8 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hvclose
    have hval : ‖θ (T w)‖ ≤ ‖θ (T w - v)‖ + ‖θ v‖ := by
      rw [map_sub]
      exact norm_le_norm_sub_add _ _
    have hsmall : ‖θ (T w - v)‖ ≤ 2 * (ε / 8) :=
      (θ.le_opNorm _).trans (mul_le_mul hnθ hdiff.le (norm_nonneg _) (by norm_num))
    change ‖θ (T w)‖ ≤ ε / 2
    have hcenter' : ‖θ v‖ < ε / 8 := hcenter
    linarith only [hval, hsmall, hcenter', hε]
  obtain ⟨a, ha, b, hb, hab⟩ := hx.2 U hU hxU
  have han := hnear a ha
  have hbn := hnear b hb
  have htri := norm_sub_le_norm_sub_add_norm_sub (WeakDual.toStrongDual a)
    (WeakDual.toStrongDual (weakStarAdjoint T φ₀)) (WeakDual.toStrongDual b)
  rw [norm_sub_rev (WeakDual.toStrongDual (weakStarAdjoint T φ₀)) (WeakDual.toStrongDual b)] at htri
  linarith only [han, hbn, htri, hab]

theorem operatorSzlenkBound_of_compact {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    OperatorSzlenkBound T (1 : Ordinal) := by
  intro ε hε
  rw [← Ordinal.succ_zero, szlenkIterate_succ, szlenkIterate_zero]
  exact szlenkDeriv_adjointUnitBall_compact hT hε

theorem compact_subset_szlenk_one :
    {T : E →L[𝕜] F | IsCompactOperator T} ⊆ SzlenkOperatorClass (1 : Ordinal.{v}) := by
  intro T hT
  change OperatorSzlenkBound T (Ordinal.omega0 ^ (1 : Ordinal.{v}))
  rw [Ordinal.opow_one]
  exact (operatorSzlenkBound_of_compact hT).mono Ordinal.one_lt_omega0.le

end Posets
