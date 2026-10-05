import ThesisCommon.Analysis.ComplexL1ModulusRealDomain
import ThesisCommon.Analysis.ComplexL1Domination

/-! Every bounded complex L1 operator has a genuinely constructed positive
modulus, with sharp norm equality. This holds for arbitrary measures. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

def complexL1OperatorRealRestriction (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    Lp ℝ 1 μ →L[ℝ] Lp ℂ 1 ν := (T.restrictScalars ℝ).comp (complexL1OfReal μ)

theorem norm_complexL1OperatorRealRestriction_le (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    ‖complexL1OperatorRealRestriction T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro f
  change ‖T (complexL1OfReal μ f)‖ ≤ ‖T‖*‖f‖
  simpa only [norm_complexL1OfReal] using T.le_opNorm (complexL1OfReal μ f)

/-- The actual real positive modulus of a complex-to-complex L1 operator. -/
def complexL1OperatorModulus (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν := complexOperatorModulus (complexL1OperatorRealRestriction T)

theorem complexL1OperatorModulus_nonneg (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    (f : Lp ℝ 1 μ) (hf : 0 ≤ f) : 0 ≤ complexL1OperatorModulus T f :=
  complexOperatorModulus_nonneg _ f hf

theorem complexL1OperatorModulus_dominates (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    (f : Lp ℂ 1 μ) : complexL1Modulus (T f) ≤ complexL1OperatorModulus T (complexL1Modulus f) := by
  apply complexL1_domination_of_nonneg T (complexL1OperatorModulus T) ?_ f
  intro g hg
  exact complexOperatorModulus_dominates_nonneg (complexL1OperatorRealRestriction T) g hg

theorem complexL1OperatorModulus_least (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    (R : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hR : ∀ f, 0 ≤ f → complexL1Modulus (T (complexL1OfReal μ f)) ≤ R f)
    (f : Lp ℝ 1 μ) (hf : 0 ≤ f) : complexL1OperatorModulus T f ≤ R f :=
  complexOperatorModulus_least (complexL1OperatorRealRestriction T) R hR f hf

/-- Exact equality with the original complex operator norm. -/
theorem norm_complexL1OperatorModulus (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    ‖complexL1OperatorModulus T‖ = ‖T‖ := by
  apply le_antisymm
  · exact (norm_complexOperatorModulus_le _).trans (norm_complexL1OperatorRealRestriction_le T)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    calc
      ‖T f‖ = ‖complexL1Modulus (T f)‖ := (norm_complexL1Modulus _).symm
      _ ≤ ‖complexL1OperatorModulus T (complexL1Modulus f)‖ := norm_le_norm_of_abs_le_abs (by
        rw [abs_of_nonneg (complexL1Modulus_nonneg _),
          abs_of_nonneg (complexL1OperatorModulus_nonneg _ _ (complexL1Modulus_nonneg _))]
        exact complexL1OperatorModulus_dominates T f)
      _ ≤ ‖complexL1OperatorModulus T‖ * ‖complexL1Modulus f‖ :=
        (complexL1OperatorModulus T).le_opNorm _
      _ = ‖complexL1OperatorModulus T‖ * ‖f‖ := by rw [norm_complexL1Modulus]

/-- The positive modulus also gives an actual complex-linear operator. -/
def complexL1OperatorAbsolute (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν := complexL1Extension (complexL1OperatorModulus T)

theorem complexL1OperatorAbsolute_ofReal (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (f : Lp ℝ 1 μ) :
    complexL1OperatorAbsolute T (complexL1OfReal μ f) =
      complexL1OfReal ν (complexL1OperatorModulus T f) := complexL1Extension_ofReal _ f

theorem norm_complexL1OperatorAbsolute (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    ‖complexL1OperatorAbsolute T‖ = ‖T‖ := by
  rw [complexL1OperatorAbsolute,
    norm_complexL1Extension_of_positive _ (complexL1OperatorModulus_nonneg T),
    norm_complexL1OperatorModulus]

end ThesisCommon
