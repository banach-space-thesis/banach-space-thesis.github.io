import SurveyStatements.P1WeakCauchyNorming
import SurveyStatements.P1BasicSelection

/-! Finite families from an actual norming kernel. Unlike an unrestricted
Hahn--Banach family, every chosen functional belongs to the specified kernel,
so its evaluations on the weak-Cauchy sequence tend to zero. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem finite_kernel_norming_family
    (ξ : StrongDual ℂ (StrongDual ℂ X)) {q d : ℝ}
    (hq : ∀ x : X, ∃ f : StrongDual ℂ X,
      ‖f‖ ≤ 1 ∧ ξ f = 0 ∧ q * ‖x‖ ≤ ‖f x‖)
    (hd : d < q) (M : Submodule ℂ X) [FiniteDimensional ℂ M] :
    ∃ F : Finset (StrongDual ℂ X),
      (∀ f ∈ F, ‖f‖ ≤ 1 ∧ ξ f = 0) ∧
      ∀ x ∈ M, x ≠ 0 → ∃ f ∈ F, d * ‖x‖ < ‖f x‖ := by
  classical
  let D := {f : StrongDual ℂ X // ‖f‖ ≤ 1 ∧ ξ f = 0}
  let U : D → Set M := fun f => {x | d < ‖f.1 x‖}
  have hU : ∀ f, IsOpen (U f) := by
    intro f
    exact isOpen_lt continuous_const
      (f.1.continuous.comp continuous_subtype_val).norm
  have hcover : Metric.sphere (0 : M) 1 ⊆ ⋃ f, U f := by
    intro x hx
    have hxnorm : ‖(x : X)‖ = 1 := by simpa using hx
    obtain ⟨f, hfnorm, hfker, hfx⟩ := hq (x : X)
    refine Set.mem_iUnion.mpr ⟨⟨f, hfnorm, hfker⟩, ?_⟩
    change d < ‖f (x : X)‖
    exact hd.trans_le (by simpa only [hxnorm, mul_one] using hfx)
  obtain ⟨A, hA⟩ := (isCompact_sphere (0 : M) 1).elim_finite_subcover U hU hcover
  refine ⟨A.image Subtype.val, ?_, ?_⟩
  · intro f hf
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hf
    exact g.2
  · intro x hx hx0
    let y : M := ⟨unitNormalize x, M.smul_mem _ hx⟩
    have hy : y ∈ Metric.sphere (0 : M) 1 := by
      simpa [y] using norm_unitNormalize hx0
    obtain ⟨f, hfA, hyf⟩ := Set.mem_iUnion₂.mp (hA hy)
    refine ⟨f.1, Finset.mem_image.mpr ⟨f, hfA, rfl⟩, ?_⟩
    have hynorm : d < ‖f.1 (unitNormalize x)‖ := hyf
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hscale := mul_lt_mul_of_pos_right hynorm hxpos
    have heq : ‖f.1 (unitNormalize x)‖ * ‖x‖ = ‖f.1 x‖ := by
      calc
        ‖f.1 (unitNormalize x)‖ * ‖x‖ =
            ‖f.1 ((‖x‖ : ℂ) • unitNormalize x)‖ := by
              simp [norm_smul, mul_comm]
        _ = ‖f.1 x‖ := by rw [norm_smul_unitNormalize]
    rwa [heq] at hscale

theorem weakCauchy_kernel_evaluations_tendsto_zero
    (s : ℕ → X) (hs : IsWeakCauchySequence s)
    (f : StrongDual ℂ X) (hf : weakCauchyLimitBidual s hs f = 0) :
    Tendsto (fun n => f (s n)) atTop (𝓝 0) := by
  simpa only [hf] using weakCauchyLimitBidual_tendsto s hs f

end SurveyStatements.P1
