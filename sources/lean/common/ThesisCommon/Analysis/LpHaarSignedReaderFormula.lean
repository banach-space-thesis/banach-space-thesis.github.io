import ThesisCommon.Analysis.LpHaarBlockReaders
import ThesisCommon.Analysis.LpHaarDyadicRefinement
import ThesisCommon.Analysis.LpHaarCoefficientFormula

/-! The genuine Haar coefficient of a signed block's two children is
exactly the finite block reader. This identifies the geometric reading
maps with the readers used in the interference estimates. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

theorem lpHaarSignedPart_setIntegral (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) (f : IntervalLp 𝕜 p) :
    (∫ x in lpHaarSignedPart n S θ, f x ∂(volume.restrict (Icc (0 : ℝ) 1))) =
      ∑ k ∈ S, ∫ x in lpHaarSignedChild n k (θ k), f x
        ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
  apply integral_biUnion_finset S
    (fun k _ => lpHaarSignedChild_measurable n k (θ k))
  · intro i _ j _ hij
    exact lpHaarSignedChild_disjoint_other n (fun h => hij (Fin.ext h)) (θ i) (θ j)
  · intro k _
    exact ((Lp.memLp f).integrable Fact.out).integrableOn

theorem lpHaarSignedBlockReader_eq_coefficient (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) :
    lpHaarSignedBlockReader 𝕜 p n S θ =
      lpHaarCoefficient (lpHaarSignedPart n S θ) (lpHaarSignedPart n S (fun k => !(θ k)))
        (lpHaarSignedPart_measurable n S θ)
        (lpHaarSignedPart_measurable n S (fun k => !(θ k)))
        (lpHaarSignedPart_disjoint n S θ) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [lpHaarSignedBlockReader_apply, lpHaarCoefficient_apply_integrals,
    lpHaarSignedPart_union, lpHaarBlockParent_real_measure,
    lpHaarSignedPart_setIntegral, lpHaarSignedPart_setIntegral, ← Finset.sum_sub_distrib]
  have ht (k : Fin (2 ^ n)) :
      signedValue (θ k) (lpHaarDyadicCoefficient 𝕜 p n k f) =
        (intervalLpDyadicRadius n : 𝕜)⁻¹ *
          ((∫ x in lpHaarSignedChild n k (θ k), f x ∂(volume.restrict (Icc (0 : ℝ) 1))) -
            ∫ x in lpHaarSignedChild n k (!(θ k)), f x ∂(volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [lpHaarDyadicCoefficient_apply_integrals 𝕜 p n k k.isLt f]
    cases hθ : θ k <;> simp [signedValue, lpHaarSignedChild, hθ]
    <;> ring
  simp_rw [ht]
  rw [← Finset.mul_sum]
  push_cast
  rw [mul_inv_rev]
  ring

end ThesisCommon
