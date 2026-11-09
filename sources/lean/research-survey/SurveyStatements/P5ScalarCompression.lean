import SurveyStatements.P5Factorization

/-!
The quantitative part of Problem 5's final argument: scalar compression gives
uniform primary factorization; complementary compressions transfer through
bounded retractions. These are proved implications, not assumptions that the
mixed-norm space already has scalar compression.
-/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P5

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem scalar_multiple_factorsIdentityWith {c : 𝕜}
    (hc : (1 / 2 : ℝ) ≤ ‖c‖) :
    FactorsIdentityWith (c • ContinuousLinearMap.id 𝕜 X) X 2 := by
  have hne : c ≠ 0 := norm_pos_iff.mp (by linarith)
  have hinv : ‖c⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    exact (inv_le_comm₀ (norm_pos_iff.mpr hne) (by norm_num : (0 : ℝ) < 2)).mpr
      (by simpa using hc)
  refine ⟨c⁻¹ • ContinuousLinearMap.id 𝕜 X, ContinuousLinearMap.id 𝕜 X, ?_, ?_⟩
  · ext x
    simp [smul_smul, hne]
  · have hU : ‖c⁻¹ • ContinuousLinearMap.id 𝕜 X‖ ≤ 2 := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans
        (by simpa using hinv)
    calc
      _ ≤ 2 * 1 :=
        mul_le_mul hU ContinuousLinearMap.norm_id_le (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num

theorem scalar_multiple_dichotomy (c : 𝕜) :
    FactorsIdentityWith (c • ContinuousLinearMap.id 𝕜 X) X 2 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - c • ContinuousLinearMap.id 𝕜 X) X 2 := by
  by_cases hc : (1 / 2 : ℝ) ≤ ‖c‖
  · exact Or.inl (scalar_multiple_factorsIdentityWith hc)
  · have hsum := norm_add_le c (1 - c)
    have he : c + (1 - c) = (1 : 𝕜) := by ring
    rw [he, norm_one] at hsum
    have hcomp : ContinuousLinearMap.id 𝕜 X - c • ContinuousLinearMap.id 𝕜 X =
        (1 - c) • ContinuousLinearMap.id 𝕜 X := by
      ext x
      simp [sub_smul]
    rw [hcomp]
    exact Or.inr (scalar_multiple_factorsIdentityWith (by linarith))

/-- The scalar-compression property proved for `X₀₀` in the paper. This is
a fully specified mathematical property, not an axiom or a proof certificate. -/
def HasScalarCompression (𝕜 : Type*) [RCLike 𝕜] (X : Type*)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∀ T : X →L[𝕜] X, ∀ ε : ℝ, 0 < ε →
    ∃ A B : X →L[𝕜] X, ∃ c : 𝕜,
      A.comp B = ContinuousLinearMap.id 𝕜 X ∧
      ‖A‖ * ‖B‖ ≤ 1 + ε ∧
      ‖(A.comp T).comp B - c • ContinuousLinearMap.id 𝕜 X‖ < ε

/-- Accuracy `1/8` and factor bound `9/8` give the exact bound three. -/
theorem scalarCompression_factor_dichotomy [CompleteSpace X]
    (h : HasScalarCompression 𝕜 X) (T : X →L[𝕜] X) :
    FactorsIdentityWith T X 3 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - T) X 3 := by
  obtain ⟨A, B, c, hAB, hnorm, hsmall⟩ := h T (1 / 8) (by norm_num)
  have hpert := factorization_dichotomy_perturb (scalar_multiple_dichotomy (X := X) c)
    (by linarith : 2 * ‖(A.comp T).comp B - c • ContinuousLinearMap.id 𝕜 X‖ < 1 / 4)
  rcases hpert with hT | hT
  · exact Or.inl ((hT.of_compression A B).mono (by nlinarith))
  · rw [← compression_complement T A B hAB] at hT
    exact Or.inr ((hT.of_compression A B).mono (by nlinarith))

theorem HasScalarCompression.hasUniformPrimaryFactorization [CompleteSpace X]
    (h : HasScalarCompression 𝕜 X) : HasUniformPrimaryFactorization 𝕜 X := by
  refine ⟨3, by norm_num, fun T => ?_⟩
  rcases scalarCompression_factor_dichotomy h T with hT | hT
  · obtain ⟨A, B, heq, hnorm⟩ := hT
    exact ⟨A, B, hnorm, Or.inl heq⟩
  · obtain ⟨A, B, heq, hnorm⟩ := hT
    exact ⟨A, B, hnorm, Or.inr heq⟩

/-- Transport a factorization through a complemented copy of its factor space. -/
theorem FactorsIdentityWith.through_retract {T : X →L[𝕜] X} {C : ℝ}
    (h : FactorsIdentityWith T Y C) (U : X →L[𝕜] Y) (V : Y →L[𝕜] X)
    (hVU : V.comp U = ContinuousLinearMap.id 𝕜 X) :
    FactorsIdentityWith T X (C * (‖V‖ * ‖U‖)) := by
  obtain ⟨A, B, heq, hnorm⟩ := h
  refine ⟨V.comp A, B.comp U, ?_, ?_⟩
  · ext x
    have heqx := congrArg (fun F : Y →L[𝕜] Y => F (U x)) heq
    have hvux := congrArg (fun F : X →L[𝕜] X => F x) hVU
    change V (A (T (B (U x)))) = x
    change A (T (B (U x))) = U x at heqx
    change V (U x) = x at hvux
    rw [heqx, hvux]
  · calc
      ‖V.comp A‖ * ‖B.comp U‖ ≤ (‖V‖ * ‖A‖) * (‖B‖ * ‖U‖) :=
        mul_le_mul (V.opNorm_comp_le A) (B.opNorm_comp_le U)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖A‖ * ‖B‖) * (‖V‖ * ‖U‖) := by ring
      _ ≤ C * (‖V‖ * ‖U‖) :=
        mul_le_mul_of_nonneg_right hnorm (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The exact final quantitative assembly in the paper. The hypotheses describe
the cancellative projection and complemented copy; their existence on `Lp(L1)`
must still be proved independently of this theorem. -/
theorem uniformPrimaryFactorization_of_cancellative_compression [CompleteSpace Y]
    (h : HasScalarCompression 𝕜 Y)
    (P : X →L[𝕜] Y) (ι : Y →L[𝕜] X)
    (hPι : P.comp ι = ContinuousLinearMap.id 𝕜 Y)
    (U : X →L[𝕜] Y) (V : Y →L[𝕜] X)
    (hVU : V.comp U = ContinuousLinearMap.id 𝕜 X)
    (hP : ‖P‖ ≤ 4) (hι : ‖ι‖ ≤ 1) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) :
    ∀ T : X →L[𝕜] X, FactorsIdentityWith T X 12 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 X - T) X 12 := by
  intro T
  have lift (S : X →L[𝕜] X)
      (hS : FactorsIdentityWith ((P.comp S).comp ι) Y 3) :
      FactorsIdentityWith S X 12 := by
    apply ((hS.of_compression P ι).through_retract U V hVU).mono
    have hPιn : ‖P‖ * ‖ι‖ ≤ 4 := by
      calc
        ‖P‖ * ‖ι‖ ≤ 4 * 1 :=
          mul_le_mul hP hι (norm_nonneg _) (by norm_num)
        _ = 4 := by norm_num
    have hVUn : ‖V‖ * ‖U‖ ≤ 1 := by
      calc
        ‖V‖ * ‖U‖ ≤ 1 * 1 :=
          mul_le_mul hV hU (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    calc
      (3 * (‖P‖ * ‖ι‖)) * (‖V‖ * ‖U‖) ≤ (3 * 4) * 1 := by gcongr
      _ = 12 := by norm_num
  rcases scalarCompression_factor_dichotomy h ((P.comp T).comp ι) with hT | hT
  · exact Or.inl (lift T hT)
  · apply Or.inr
    apply lift (ContinuousLinearMap.id 𝕜 X - T)
    rwa [compression_complement T P ι hPι]

end SurveyStatements.P5
