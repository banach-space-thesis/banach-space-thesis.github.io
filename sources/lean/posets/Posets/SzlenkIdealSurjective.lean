import Posets.SzlenkIdealEmbedding
import Mathlib.Analysis.Normed.Operator.Banach

/-! Surjective Banach operators have the same Szlenk bound as their
codomain identity. Open mapping supplies the adjoint's lower norm bound. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

theorem weakStarAdjoint_exists_norm_sub_lower_bound (T : E →L[𝕜] F)
    (hT : Function.Surjective T) :
    ∃ c : ℝ, 0 < c ∧ ∀ a b : WeakDual 𝕜 F,
      c * ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤
        ‖WeakDual.toStrongDual (weakStarAdjoint T a) -
          WeakDual.toStrongDual (weakStarAdjoint T b)‖ := by
  obtain ⟨C, hC, hpre⟩ := T.exists_preimage_norm_le hT
  have hnorm : ∀ φ : StrongDual 𝕜 F, ‖φ‖ ≤ C * ‖φ.comp T‖ := by
    intro φ
    apply φ.opNorm_le_bound (mul_nonneg hC.le (norm_nonneg _))
    intro y
    obtain ⟨x, hx, hxn⟩ := hpre y
    calc
      ‖φ y‖ = ‖(φ.comp T) x‖ := by rw [ContinuousLinearMap.comp_apply, hx]
      _ ≤ ‖φ.comp T‖ * ‖x‖ := (φ.comp T).le_opNorm x
      _ ≤ ‖φ.comp T‖ * (C * ‖y‖) := mul_le_mul_of_nonneg_left hxn (norm_nonneg _)
      _ = (C * ‖φ.comp T‖) * ‖y‖ := by ring
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro a b
  change C⁻¹ * ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤
    ‖(WeakDual.toStrongDual a).comp T - (WeakDual.toStrongDual b).comp T‖
  rw [← ContinuousLinearMap.sub_comp]
  exact (inv_mul_le_iff₀ hC).mpr (hnorm _)

theorem OperatorSzlenkBound.id_codomain_of_surjective
    {T : E →L[𝕜] F} {α : Ordinal} (h : OperatorSzlenkBound T α)
    (hT : Function.Surjective T) :
    OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 F) α := by
  obtain ⟨c, hc, hTc⟩ := weakStarAdjoint_exists_norm_sub_lower_bound T hT
  rw [OperatorSzlenkBound, adjointUnitBall_id]
  exact HasSzlenkBound.of_image (weakStarAdjoint T) (weakStarAdjoint_continuous T) hc hTc h

theorem operatorSzlenkBound_surjective_iff (T : E →L[𝕜] F)
    (hT : Function.Surjective T) (α : Ordinal) :
    OperatorSzlenkBound T α ↔ OperatorSzlenkBound (ContinuousLinearMap.id 𝕜 F) α := by
  constructor
  · exact fun h => h.id_codomain_of_surjective hT
  · intro h
    simpa only [ContinuousLinearMap.id_comp] using h.precomp T

end Posets
