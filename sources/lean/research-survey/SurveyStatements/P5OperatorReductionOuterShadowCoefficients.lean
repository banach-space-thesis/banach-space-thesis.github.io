import SurveyStatements.P5OperatorReductionOuterShadows
import SurveyStatements.P5OperatorReductionShadowExpansion
import SurveyStatements.P5TensorBilinearity

/-! Exact scalar coefficients of the actual inner-averaged outer operator.
Only finite sign averaging and naturality of actual Bochner integration
are used; there is no exchange of an infinite limit and an operator. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem outerShadowParentMass_eq_real_measure (n : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    outerShadowParentMass n S = (volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent n S) :=
  (lpHaarBlockParent_real_measure n S).symm

theorem outerHaarPacketShadow_weightedReader (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val) η hη hb
      (outerHaarPacketShadow p T n S f) =
      ((outerShadowParentMass n S)⁻¹ : 𝕜) •
        ∑ k ∈ S, scalarHaarPacketReader (𝕜 := 𝕜) n k
          (weightedOuterReader (𝕜 := 𝕜) (E := Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) (p := p.val)
            η hη hb (T (tensorWith (p := p.val)
              (lpHaarDyadic 𝕜 outerShadowL1Exponent n k) f))) := by
  let Q : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[𝕜] Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (weightedOuterReader (𝕜 := 𝕜) (E := Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) (p := p.val) η hη hb).comp
      (T.comp (tensorInnerMap f))
  have hQ (g : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
      Q g = weightedOuterReader (𝕜 := 𝕜) (E := Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) (p := p.val)
        η hη hb (T (tensorWith (p := p.val) g f)) := rfl
  rw [outerHaarPacketShadow_apply, map_smul, outerShadowFiniteMean_map]
  apply congrArg (fun z : 𝕜 => ((outerShadowParentMass n S)⁻¹ : 𝕜) • z)
  calc
    _ = outerShadowFiniteMean (𝕜 := 𝕜) (fun θ =>
        outerShadowInnerReader 𝕜 n S θ
          (Q (outerShadowInnerPacket 𝕜 n S θ))) := by
      apply congrArg (outerShadowFiniteMean (𝕜 := 𝕜))
      funext θ
      rw [hQ]
      exact weightedOuterReader_natural
        (E := Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) (F := 𝕜) (p := p.val)
        η hη hb (outerShadowInnerReader 𝕜 n S θ) _
    _ = _ := by
      have h := rawL1HaarPacket_reader_input_eq_diagonal_sum n S Q
      simpa only [outerShadowFiniteMean, vectorMean, outerShadowInnerReader,
        outerShadowInnerWeight, outerShadowInnerPacket, outerShadowL1Exponent,
        hQ] using h

theorem outerHaarPacketShadow_haarReader (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (n r : ℕ) (S : Finset (Fin (2 ^ n))) (j : Fin (2 ^ r))
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val)
      (haarPacketWeight (𝕜 := 𝕜) r j)
      (haarPacketWeight_stronglyMeasurable r j) (haarPacketWeight_norm_le r j)
      (outerHaarPacketShadow p T n S f) =
      ((outerShadowParentMass n S)⁻¹ : 𝕜) •
        ∑ k ∈ S, scalarHaarPacketReader (𝕜 := 𝕜) n k
          (haarPacketReader (𝕜 := 𝕜) p r j
            (T (tensorWith (p := p.val)
              (lpHaarDyadic 𝕜 outerShadowL1Exponent n k) f))) :=
  outerHaarPacketShadow_weightedReader p T n S
    (haarPacketWeight r j) (haarPacketWeight_stronglyMeasurable r j)
    (haarPacketWeight_norm_le r j) f

/-- With the genuine parent-mass normalization, the raw integral diagonal
sum is precisely the equal-cardinality average of the usual Haar diagonals. -/
theorem outerHaarPacketShadow_weightedReader_coefficient (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := p.val) η hη hb
      (outerHaarPacketShadow p T n S f) =
      (S.card : 𝕜)⁻¹ *
        ∑ k ∈ S, lpHaarDyadicCoefficient 𝕜 outerShadowL1Exponent n k
          (weightedOuterReader (𝕜 := 𝕜) (E := Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) (p := p.val)
            η hη hb (T (tensorWith (p := p.val)
              (lpHaarDyadic 𝕜 outerShadowL1Exponent n k) f))) := by
  rw [outerHaarPacketShadow_weightedReader]
  simp_rw [scalarHaarPacketReader_eq_radius_coefficient]
  rw [← Finset.mul_sum, smul_eq_mul]
  have hmass : (outerShadowParentMass n S : 𝕜) =
      (S.card : 𝕜) * (intervalLpDyadicRadius n : 𝕜) := by
    simp only [outerShadowParentMass, RCLike.ofReal_mul, RCLike.ofReal_natCast]
  have hr : (intervalLpDyadicRadius n : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (intervalLpDyadicRadius_pos n).ne'
  rw [hmass, mul_inv_rev]
  calc
    _ = (S.card : 𝕜)⁻¹ *
        ((intervalLpDyadicRadius n : 𝕜)⁻¹ * (intervalLpDyadicRadius n : 𝕜)) *
        ∑ k ∈ S, lpHaarDyadicCoefficient 𝕜 outerShadowL1Exponent n k
          (weightedOuterReader (𝕜 := 𝕜) (E := Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) (p := p.val)
            η hη hb (T (tensorWith (p := p.val)
              (lpHaarDyadic 𝕜 outerShadowL1Exponent n k) f))) := by
      simp only [outerShadowL1Exponent]
      ring
    _ = _ := by rw [inv_mul_cancel₀ hr, mul_one]

end SurveyStatements.P5OperatorReduction
