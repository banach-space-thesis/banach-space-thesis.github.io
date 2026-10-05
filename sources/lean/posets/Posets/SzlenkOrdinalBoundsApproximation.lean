import Posets.SzlenkOrdinalBoundsSplit
import Posets.SzlenkOrdinalBoundsIteration

/-! A strongly convergent family of supremum-norm projections with Szlenk
bound κ gives a bound κω for the identity. -/
noncomputable section
open Set Topology Filter
namespace Posets
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem OperatorSzlenkBound.image_dualBall {T : E →L[𝕜] F} {κ : Ordinal}
    (h : OperatorSzlenkBound T κ) (R : ℝ) :
    HasSzlenkBound (weakStarAdjoint T '' szlenkDualBall R) κ := by
  let c : 𝕜 := ((|R| + 1 : ℝ) : 𝕜)
  have hcpos : 0 < |R| + 1 := by positivity
  have hcnorm : ‖c‖ = |R| + 1 := by
    change ‖((|R| + 1 : ℝ) : 𝕜)‖ = _
    rw [RCLike.norm_ofReal, abs_of_pos hcpos]
  have hcne : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hcnorm]; exact hcpos.ne')
  apply (h.smul c).subset
  rintro _ ⟨φ, hφ, rfl⟩
  refine ⟨c⁻¹ • φ, ?_, ?_⟩
  · change ‖c⁻¹ • WeakDual.toStrongDual φ - 0‖ ≤ 1
    rw [sub_zero, norm_smul, norm_inv, hcnorm]
    apply (inv_mul_le_iff₀ hcpos).mpr
    have hb : ‖WeakDual.toStrongDual φ‖ ≤ R := hφ
    have hr := le_abs_self R
    linarith
  · apply DFunLike.ext
    intro x
    change c⁻¹ • φ (c • T x) = φ (T x)
    rw [map_smul, smul_smul, inv_mul_cancel₀ hcne, one_smul]

theorem operatorSzlenkBound_of_sup_projections {I : Type*} {l : Filter I} [NeBot l]
    (P : I → E →L[𝕜] E) (hP : ∀ x, Tendsto (fun i => P i x) l (𝓝 x))
    (hmax : ∀ i x y, ‖P i x + (ContinuousLinearMap.id 𝕜 E - P i) y‖ ≤ max ‖x‖ ‖y‖)
    {κ : Ordinal} (hbound : ∀ i, OperatorSzlenkBound (P i) κ) :
    OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 E) (κ * Ordinal.omega0) := by
  apply operatorSzlenkBound_of_ball_shrink
  intro ε hε
  refine ⟨ε / 8, by positivity, ?_⟩
  intro R
  apply szlenkIterate_ball_shrink_of_projections (F := E) hε R
  intro x r hr
  obtain ⟨i, hi⟩ := strongDual_projection_mass_approx P hP (WeakDual.toStrongDual x) hr
  refine ⟨weakStarAdjoint (P i), weakStarAdjoint_continuous _, hi,
    (hbound i).image_dualBall R, ?_⟩
  intro a b
  exact strongDual_norm_sub_split (P i) (ContinuousLinearMap.id 𝕜 E - P i)
    (add_sub_cancel _ _) (hmax i) (WeakDual.toStrongDual a) (WeakDual.toStrongDual b)

end Posets
