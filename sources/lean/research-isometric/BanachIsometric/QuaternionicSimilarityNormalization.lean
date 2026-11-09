import BanachIsometric.QuaternionicHermitianRealGeometry
import BanachIsometric.HermitianSimilarityNormalization
import BanachIsometric.HermitianDeletionHyperplanes

/-!
# The actual quaternionic simultaneous maps supply real normalized isometries

The input map is linear for the original right quaternionic action. Restriction
to real scalars and division by the first positive similarity factor produce
the real isometry used for Rayleigh and trace. No real map replaces the input
similarity hypothesis.
-/

namespace BanachIsometric.Quaternionic

open scoped Quaternion

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module Hᵐᵒᵖ E] [IsScalarTower ℝ Hᵐᵒᵖ E]

theorem exists_real_isometry_of_quaternionic_simultaneous_similarity
    (Q : HermitianForm E) (S J : Submodule Hᵐᵒᵖ E) (T : S ≃ₗ[Hᵐᵒᵖ] J)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hfirst : ∀ x, ‖T x‖ = c₁ * ‖x‖)
    (hsecond : ∀ x, (Q.form (T x : E) (T x : E)).re = c₂ ^ 2 * (Q.form (x : E) (x : E)).re) :
    ∃ U : S.restrictScalars ℝ ≃ₗᵢ[ℝ] J.restrictScalars ℝ, ∃ c : ℝ, 0 < c ∧
      ∀ x, (Q.form (U x : E) (U x : E)).re = c * (Q.form (x : E) (x : E)).re := by
  let Tr : S.restrictScalars ℝ ≃ₗ[ℝ] J.restrictScalars ℝ := T.restrictScalars ℝ
  exact exists_normalized_simultaneous_hermitian_similarity
    (restrictSesqForm Q.realBilinear (S.restrictScalars ℝ))
    (restrictSesqForm Q.realBilinear (J.restrictScalars ℝ)) Tr c₁ c₂ hc₁ hc₂ hfirst hsecond

end

end BanachIsometric.Quaternionic
