import ThesisCommon.Analysis.GowersMaureyCompletedPairing
import ThesisCommon.Analysis.GowersMaureyFiniteNorming

/-! Finite interval restriction of a genuine bounded functional. Its
dual-unit bound is exact, and its error on a completed vector is controlled
by an actual finite approximation supported in that interval. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def finiteFunctionalRestriction (D : ConstructionData 𝕜) (E : Interval)
    (φ : ShiftSpace D →L[𝕜] 𝕜) : C00 𝕜 :=
  finiteDualCoefficients D E (φ.comp (denseEmbedding D).toContinuousLinearMap)

theorem finiteFunctionalRestriction_support (D : ConstructionData 𝕜) (E : Interval)
    (φ : ShiftSpace D →L[𝕜] 𝕜) : (finiteFunctionalRestriction D E φ).support ⊆ E.set :=
  finiteDualCoefficients_support D E _

theorem finiteFunctionalRestriction_pairing (D : ConstructionData 𝕜) (E : Interval)
    (φ : ShiftSpace D →L[𝕜] 𝕜) {x : C00 𝕜} (hx : x.support ⊆ E.set) :
    pairing (finiteFunctionalRestriction D E φ) x = φ (denseEmbedding D x) := by
  rw [finiteFunctionalRestriction, pairing_finiteDualCoefficients, restrict_eq_self_of_support_subset hx]
  rfl

theorem finiteFunctionalRestriction_dualUnit (D : ConstructionData 𝕜) (E : Interval)
    (φ : ShiftSpace D →L[𝕜] 𝕜) (hφ : ‖φ‖ ≤ 1) :
    DualUnit (implicitNorm D) (finiteFunctionalRestriction D E φ) := by
  apply finiteDualCoefficients_dualUnit
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖φ (denseEmbedding D x)‖ ≤ 1*‖x‖
  calc
    _ ≤ ‖φ‖ * ‖denseEmbedding D x‖ := φ.le_opNorm _
    _ ≤ _ := by rw [denseEmbedding_norm]; exact mul_le_mul_of_nonneg_right hφ (norm_nonneg x)

theorem finiteFunctionalRestriction_error (D : ConstructionData 𝕜) (E : Interval)
    (φ : ShiftSpace D →L[𝕜] 𝕜) (hφ : ‖φ‖ ≤ 1)
    (z : ShiftSpace D) {y : C00 𝕜} (hy : y.support ⊆ E.set) :
    ‖completedPairing D (finiteFunctionalRestriction D E φ) z - φ z‖ ≤
      2 * ‖z-denseEmbedding D y‖ := by
  have hmatch : completedPairing D (finiteFunctionalRestriction D E φ) (denseEmbedding D y) =
      φ (denseEmbedding D y) := by
    rw [completedPairing_denseEmbedding]
    exact finiteFunctionalRestriction_pairing D E φ hy
  have he : completedPairing D (finiteFunctionalRestriction D E φ) z - φ z =
      completedPairing D (finiteFunctionalRestriction D E φ) (z-denseEmbedding D y) -
      φ (z-denseEmbedding D y) := by
    simp only [map_sub, hmatch]
    abel
  rw [he]
  calc
    _ ≤ ‖completedPairing D (finiteFunctionalRestriction D E φ) (z-denseEmbedding D y)‖ +
        ‖φ (z-denseEmbedding D y)‖ := norm_sub_le _ _
    _ ≤ ‖z-denseEmbedding D y‖ + ‖z-denseEmbedding D y‖ := add_le_add
      (completedPairing_norm_bound (finiteFunctionalRestriction_dualUnit D E φ hφ) _)
      ((φ.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hφ))
    _ = _ := by ring

end ThesisCommon.GowersMaurey
