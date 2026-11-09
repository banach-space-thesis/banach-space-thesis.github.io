import CKEUPFP.Perturbation
import CKEUPFP.DefinitionEquivalences

/-!
# Correcting a compressed factorisation

This proves the last operator-algebra step in Section 4, with the restriction,
extension, multiplier, and local-error inputs explicit. It includes the precise
`4C/3` bound. It is a lemma for assembling the transfer theorem, not a substitute
for the geometric construction of these inputs.
-/

noncomputable section

namespace CKEUPFP

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

/-- A contractive compression within `η` of an exactly factorable operator
gives an exact factorisation through the original operator. -/
theorem factorsThroughWith_of_compression
    (T : X →L[𝕜] X) (Q : X →L[𝕜] Y) (J : Y →L[𝕜] X)
    (L A R : Y →L[𝕜] Y) {C η : ℝ}
    (hQ : ‖Q‖ ≤ 1) (hJ : ‖J‖ ≤ 1)
    (hfactor : (L.comp A).comp R = ContinuousLinearMap.id 𝕜 Y)
    (hLR : ‖L‖ * ‖R‖ ≤ C) (hη : 0 ≤ η)
    (herror : ‖(Q.comp T).comp J - A‖ ≤ η) (hquarter : C * η ≤ (1 / 4 : ℝ)) :
    FactorsThroughWith (ContinuousLinearMap.id 𝕜 Y) T ((4 / 3 : ℝ) * C) := by
  let S := (Q.comp T).comp J
  have happrox : ‖(L.comp S).comp R - ContinuousLinearMap.id 𝕜 Y‖ ≤ (1 / 4 : ℝ) := by
    calc
      ‖(L.comp S).comp R - ContinuousLinearMap.id 𝕜 Y‖ ≤
          ‖L‖ * ‖S - A‖ * ‖R‖ := sandwiched_error_le L R S A hfactor
      _ ≤ ‖L‖ * η * ‖R‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left herror (norm_nonneg L)) (norm_nonneg R)
      _ = (‖L‖ * ‖R‖) * η := by ring
      _ ≤ C * η := mul_le_mul_of_nonneg_right hLR hη
      _ ≤ (1 / 4 : ℝ) := hquarter
  have happrox' : ‖((L.comp Q).comp T).comp (J.comp R) -
      ContinuousLinearMap.id 𝕜 Y‖ ≤ (1 / 4 : ℝ) := by
    simpa only [S, ContinuousLinearMap.comp_assoc] using happrox
  have hcost : ‖L.comp Q‖ * ‖J.comp R‖ ≤ C := by
    have hLQ : ‖L.comp Q‖ ≤ ‖L‖ := by
      calc
        ‖L.comp Q‖ ≤ ‖L‖ * ‖Q‖ := L.opNorm_comp_le Q
        _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left hQ (norm_nonneg L)
        _ = ‖L‖ := mul_one _
    have hJR : ‖J.comp R‖ ≤ ‖R‖ := by
      calc
        ‖J.comp R‖ ≤ ‖J‖ * ‖R‖ := J.opNorm_comp_le R
        _ ≤ 1 * ‖R‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg R)
        _ = ‖R‖ := one_mul _
    exact (mul_le_mul hLQ hJR (norm_nonneg _) (norm_nonneg L)).trans hLR
  exact (factorsThroughWith_id_of_approximate T (L.comp Q) (J.comp R) happrox').mono
    (mul_le_mul_of_nonneg_left hcost (by norm_num))

omit [CompleteSpace Y] in
/-- Restriction after extension preserves the complementary compression. -/
theorem compression_complement (T : X →L[𝕜] X) (Q : X →L[𝕜] Y)
    (J : Y →L[𝕜] X) (hQJ : Q.comp J = ContinuousLinearMap.id 𝕜 Y) :
    (Q.comp (ContinuousLinearMap.id 𝕜 X - T)).comp J =
      ContinuousLinearMap.id 𝕜 Y - (Q.comp T).comp J := by
  ext y
  have hy := congrArg (fun F : Y →L[𝕜] Y => F y) hQJ
  simpa using hy

omit [CompleteSpace Y] in
/-- The two complementary compressions have exactly the same error norm. -/
theorem compression_complement_error (T : X →L[𝕜] X) (Q : X →L[𝕜] Y)
    (J : Y →L[𝕜] X) (A : Y →L[𝕜] Y)
    (hQJ : Q.comp J = ContinuousLinearMap.id 𝕜 Y) :
    ‖(Q.comp (ContinuousLinearMap.id 𝕜 X - T)).comp J -
      (ContinuousLinearMap.id 𝕜 Y - A)‖ = ‖(Q.comp T).comp J - A‖ := by
  rw [compression_complement T Q J hQJ]
  have h : ContinuousLinearMap.id 𝕜 Y - (Q.comp T).comp J -
      (ContinuousLinearMap.id 𝕜 Y - A) = -((Q.comp T).comp J - A) := by abel
  rw [h, norm_neg]

end CKEUPFP
