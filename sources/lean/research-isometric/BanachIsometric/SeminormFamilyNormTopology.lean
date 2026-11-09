import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.UniformSpace.Equiv
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.Equiv

/-! A family of seminorms which collapses to an actual anchor norm generates
exactly that norm's uniformity. This generic helper uses only additive-group
uniformities, so it preserves arbitrary original scalar actions, including Hopp. -/

namespace BanachIsometric

open Set Filter
open scoped Topology

noncomputable section

variable {ι X M : Type*} [AddCommGroup X] [Module ℝ X] [UniformSpace X] [IsUniformAddGroup X]
    [NormedAddCommGroup M]

theorem uniformContinuous_normModel_of_anchor
    (p : ι → Seminorm ℝ X) (hp : WithSeminorms p) (i₀ : ι)
    (e : X ≃+ M) (hnorm : ∀ x, ‖e x‖ = p i₀ x) : UniformContinuous e := by
  apply uniformContinuous_of_continuousAt_zero e
  rw [ContinuousAt, e.map_zero]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht : Tendsto (p i₀) (𝓝 (0 : X)) (𝓝 (0 : ℝ)) := by
    simpa only [map_zero] using (hp.continuous_seminorm i₀).tendsto 0
  have h := ht.eventually (Iio_mem_nhds hε)
  simpa only [dist_zero_right, hnorm] using h

theorem uniformContinuous_from_normModel_of_family_collapse
    (p : ι → Seminorm ℝ X) (hp : WithSeminorms p) (i₀ : ι)
    (e : X ≃+ M) (hnorm : ∀ x, ‖e x‖ = p i₀ x)
    (hscale : ∀ i, (∀ x, p i x = 0) ∨ ∃ c : ℝ, 0 < c ∧ ∀ x, p i x = c * p i₀ x) :
    UniformContinuous e.symm := by
  apply uniformContinuous_of_continuousAt_zero e.symm
  rw [ContinuousAt, e.symm.map_zero]
  apply (hp.tendsto_nhds e.symm 0).mpr
  intro i ε hε
  rcases hscale i with hzero | ⟨c, _hc, hprop⟩
  · filter_upwards [] with y
    change p i (e.symm y - 0) < ε
    rw [sub_zero, hzero]
    exact hε
  · have ht : Tendsto (fun y : M => c * ‖y‖) (𝓝 (0 : M)) (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero, mul_zero] using (continuous_const.mul continuous_norm).tendsto (0 : M)
    filter_upwards [ht.eventually (Iio_mem_nhds hε)] with y hy
    change p i (e.symm y - 0) < ε
    rw [sub_zero, hprop, ← hnorm, e.apply_symm_apply]
    exact hy

def seminormFamilyNormUniformEquiv
    (p : ι → Seminorm ℝ X) (hp : WithSeminorms p) (i₀ : ι)
    (e : X ≃+ M) (hnorm : ∀ x, ‖e x‖ = p i₀ x)
    (hscale : ∀ i, (∀ x, p i x = 0) ∨ ∃ c : ℝ, 0 < c ∧ ∀ x, p i x = c * p i₀ x) :
    X ≃ᵤ M :=
  { e.toEquiv with
    uniformContinuous_toFun := uniformContinuous_normModel_of_anchor p hp i₀ e hnorm
    uniformContinuous_invFun := uniformContinuous_from_normModel_of_family_collapse p hp i₀ e hnorm hscale }

section Scalars

variable {R : Type*} [Semiring R] [Module R X] [Module R M]

def seminormFamilyNormContinuousLinearEquiv
    (p : ι → Seminorm ℝ X) (hp : WithSeminorms p) (i₀ : ι)
    (e : X ≃ₗ[R] M) (hnorm : ∀ x, ‖e x‖ = p i₀ x)
    (hscale : ∀ i, (∀ x, p i x = 0) ∨ ∃ c : ℝ, 0 < c ∧ ∀ x, p i x = c * p i₀ x) :
    X ≃L[R] M :=
  { e with
    continuous_toFun := (seminormFamilyNormUniformEquiv p hp i₀ e.toAddEquiv hnorm hscale).uniformContinuous.continuous
    continuous_invFun := (seminormFamilyNormUniformEquiv p hp i₀ e.toAddEquiv hnorm hscale).symm.uniformContinuous.continuous }

theorem completeSpace_normModel_of_seminorm_family_collapse [CompleteSpace X]
    (p : ι → Seminorm ℝ X) (hp : WithSeminorms p) (i₀ : ι)
    (e : X ≃ₗ[R] M) (hnorm : ∀ x, ‖e x‖ = p i₀ x)
    (hscale : ∀ i, (∀ x, p i x = 0) ∨ ∃ c : ℝ, 0 < c ∧ ∀ x, p i x = c * p i₀ x) :
    CompleteSpace M :=
  (seminormFamilyNormUniformEquiv p hp i₀ e.toAddEquiv hnorm hscale).completeSpace_iff.mp inferInstance

end Scalars

end
end BanachIsometric
