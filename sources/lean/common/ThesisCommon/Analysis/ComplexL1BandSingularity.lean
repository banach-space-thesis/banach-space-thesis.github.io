import ThesisCommon.Analysis.ComplexL1BandDecomposition

/-! The paper's signed-modulus singularity criterion for a genuine complex
band projection. The quantifier over every band element is retained. -/
noncomputable section
open MeasureTheory
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable {I : Submodule ℝ (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)}

theorem complexL1OperatorModulus_neg (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorModulus (-T) = complexL1OperatorModulus T := by
  have hle (U : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
      complexL1OperatorModulus (-U) ≤ complexL1OperatorModulus U := by
    apply complexL1OperatorModulus_least
    intro f hf
    have hn (g : Lp ℂ 1 ν) : complexL1Modulus (-g) = complexL1Modulus g := by
      simpa only [neg_one_smul,norm_neg,norm_one,one_smul] using complexL1Modulus_smul (-1) g
    change complexL1Modulus (-U (complexL1OfReal μ f)) ≤ _
    rw [hn]
    exact complexOperatorModulus_dominates_nonneg (complexL1OperatorRealRestriction U) f hf
  exact le_antisymm (hle T) (by simpa only [neg_neg] using hle (-T))

theorem complexL1BandProjection_modulus_add (hI : IsOrderClosedIdeal I)
    {S K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν}
    (hS : complexL1BandProjection hI S = 0) (hK : complexL1BandProjection hI K = K) :
    complexL1OperatorModulus (S+K) = complexL1OperatorModulus S + complexL1OperatorModulus K := by
  have h := complexL1BandProjection_modulus_decomposition hI (S+K)
  simpa only [map_add,hS,hK,zero_add,add_sub_cancel_right] using h

theorem complexL1BandProjection_modulus_sub (hI : IsOrderClosedIdeal I)
    {S K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν}
    (hS : complexL1BandProjection hI S = 0) (hK : complexL1BandProjection hI K = K) :
    complexL1OperatorModulus (S-K) = complexL1OperatorModulus S + complexL1OperatorModulus K := by
  simpa only [sub_eq_add_neg,complexL1OperatorModulus_neg] using
    complexL1BandProjection_modulus_add hI hS
      (show complexL1BandProjection hI (-K) = -K by rw [map_neg,hK])

theorem complexL1BandProjection_eq_zero_iff_signed_modulus (hI : IsOrderClosedIdeal I)
    (S : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1BandProjection hI S = 0 ↔
      ∀ K, complexL1BandProjection hI K = K →
        complexL1OperatorModulus (S-K) = complexL1OperatorModulus (S+K) := by
  constructor
  · intro hS K hK
    rw [complexL1BandProjection_modulus_sub hI hS hK,complexL1BandProjection_modulus_add hI hS hK]
  · intro h
    let K := complexL1BandProjection hI S
    have hid : complexL1BandProjection hI K = K := complexL1BandProjection_idempotent hI S
    have he := congrArg (bandProjection hI) (h K hid)
    rw [← complexL1BandProjection_modulus,← complexL1BandProjection_modulus,map_sub,map_add,hid] at he
    change complexL1OperatorModulus (K-K) = complexL1OperatorModulus (K+K) at he
    rw [sub_self,complexL1OperatorModulus_zero] at he
    have hn : ‖K+K‖ = 0 := by rw [← norm_complexL1OperatorModulus,← he,norm_zero]
    have htw : 2*‖K‖ = 0 := by
      simpa only [← two_smul ℝ K,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)] using hn
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg K])

end ThesisCommon
