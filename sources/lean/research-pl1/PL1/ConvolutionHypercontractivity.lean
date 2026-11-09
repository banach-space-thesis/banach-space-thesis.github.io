import PL1.LpInclusions
import PL1.ConvolutionL1

/-! # Transfer a real convolution Lp-L2 bound to either scalar field

Positivity of the actual convolution kernel gives the same constant; no
complex tensorization premise is required.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PL1.Walsh

variable (K : Type*) [RCLike K] (p : ℝ≥0∞) [Fact (1 ≤ p)]

def normLp (f : Lp K p haar) : Lp ℝ p haar :=
  lipschitzWith_one_norm.compLp norm_zero f

omit [Fact (1 ≤ p)] in
theorem coeFn_normLp (f : Lp K p haar) : normLp K p f =ᵐ[haar] fun x => ‖f x‖ :=
  lipschitzWith_one_norm.coeFn_compLp norm_zero f

omit [Fact (1 ≤ p)] in
theorem norm_normLp_le (f : Lp K p haar) : ‖normLp K p f‖ ≤ ‖f‖ := by
  simpa only [normLp, one_mul, NNReal.coe_one] using lipschitzWith_one_norm.norm_compLp_le norm_zero f

variable (ν : Measure Group) [IsProbabilityMeasure ν]
  (H : Lp ℝ p haar →L[ℝ] Lp ℝ 2 haar)
  (hH : ∀ f, l2ToL1 (H f) = convolutionL1 ν
    (ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p) f))

include hH

theorem norm_convolution_inclusion_le_real (f : Lp K p haar) :
    ∀ᵐ x ∂haar, ‖convolutionL1 ν
      (ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p) f) x‖ ≤
        ‖H (normLp K p f) x‖ := by
  let g := ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p) f
  let h := ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p) (normLp K p f)
  have hnorm : h =ᵐ[haar] fun x => ‖g x‖ := by
    filter_upwards [ProbabilityLp.coeFn_inclusion haar 1 p (Fact.out : 1 ≤ p) f,
      ProbabilityLp.coeFn_inclusion haar 1 p (Fact.out : 1 ≤ p) (normLp K p f),
      coeFn_normLp K p f] with x hg hh hn
    exact hh.trans (hn.trans (congrArg norm hg).symm)
  have hconv := convolutionL1_ae_eq_integral_of_ae_eq ν hnorm
  have hHae : H (normLp K p f) =ᵐ[haar] convolutionL1 ν h := by
    exact (ProbabilityLp.coeFn_inclusion haar 1 2 (by norm_num) _).symm.trans
      (by rw [hH])
  filter_upwards [coeFn_convolutionL1 ν g, hconv, hHae] with x hx hh hHx
  rw [hx, hHx, hh]
  exact (norm_integral_le_integral_norm _).trans (le_abs_self _)

theorem memLp_convolution_inclusion_two (f : Lp K p haar) :
    MemLp (convolutionL1 ν (ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p) f)) 2 haar :=
  (Lp.memLp (H (normLp K p f))).mono
    (Lp.aestronglyMeasurable _) (norm_convolution_inclusion_le_real K p ν H hH f)

def scalarLiftFun (f : Lp K p haar) : Lp K 2 haar :=
  (memLp_convolution_inclusion_two K p ν H hH f).toLp
    (convolutionL1 ν (ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p) f))

theorem coeFn_scalarLiftFun (f : Lp K p haar) :
    scalarLiftFun K p ν H hH f =ᵐ[haar]
      convolutionL1 ν (ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p) f) :=
  MemLp.coeFn_toLp _

theorem scalarLiftFun_add (f g : Lp K p haar) :
    scalarLiftFun K p ν H hH (f + g) =
      scalarLiftFun K p ν H hH f + scalarLiftFun K p ν H hH g := by
  let V := (convolutionL1 (𝕜 := K) ν).comp
    (ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p))
  apply Lp.ext
  filter_upwards [coeFn_scalarLiftFun K p ν H hH (f + g),
    coeFn_scalarLiftFun K p ν H hH f, coeFn_scalarLiftFun K p ν H hH g,
    Lp.coeFn_add (V f) (V g),
    Lp.coeFn_add (scalarLiftFun K p ν H hH f) (scalarLiftFun K p ν H hH g)]
      with x hfg hf hg hv hl
  change scalarLiftFun K p ν H hH (f + g) x = _
  change scalarLiftFun K p ν H hH (f + g) x = V (f + g) x at hfg
  rw [hfg, map_add, hv, hl]
  simp only [Pi.add_apply, hf, hg]
  rfl

theorem scalarLiftFun_smul (c : K) (f : Lp K p haar) :
    scalarLiftFun K p ν H hH (c • f) = c • scalarLiftFun K p ν H hH f := by
  let V := (convolutionL1 (𝕜 := K) ν).comp
    (ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p))
  apply Lp.ext
  filter_upwards [coeFn_scalarLiftFun K p ν H hH (c • f),
    coeFn_scalarLiftFun K p ν H hH f, Lp.coeFn_smul c (V f),
    Lp.coeFn_smul c (scalarLiftFun K p ν H hH f)] with x hcf hf hv hl
  change scalarLiftFun K p ν H hH (c • f) x = V (c • f) x at hcf
  rw [hcf, map_smul, hv, hl]
  simp only [Pi.smul_apply, hf]
  rfl

theorem norm_scalarLiftFun_le (f : Lp K p haar) :
    ‖scalarLiftFun K p ν H hH f‖ ≤ ‖H‖ * ‖f‖ := by
  calc
    _ ≤ ‖H (normLp K p f)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [coeFn_scalarLiftFun K p ν H hH f,
        norm_convolution_inclusion_le_real K p ν H hH f] with x hx hb
      simpa only [hx] using hb
    _ ≤ ‖H‖ * ‖normLp K p f‖ := H.le_opNorm _
    _ ≤ ‖H‖ * ‖f‖ := mul_le_mul_of_nonneg_left (norm_normLp_le K p f) (norm_nonneg _)

/-- The complex (or real) convolution lift with the same bound as the real
lift, constructed on genuine equivalence classes. -/
def scalarLift : Lp K p haar →L[K] Lp K 2 haar :=
  LinearMap.mkContinuous
    { toFun := scalarLiftFun K p ν H hH
      map_add' := scalarLiftFun_add K p ν H hH
      map_smul' := scalarLiftFun_smul K p ν H hH }
    ‖H‖ (norm_scalarLiftFun_le K p ν H hH)

theorem norm_scalarLift_le : ‖scalarLift K p ν H hH‖ ≤ ‖H‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_scalarLiftFun_le K p ν H hH)

theorem scalarLift_overlap (f : Lp K p haar) :
    l2ToL1 (scalarLift K p ν H hH f) =
      convolutionL1 ν (ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p) f) := by
  apply Lp.ext
  exact (ProbabilityLp.coeFn_inclusion haar 1 2 (by norm_num) _).trans
    (coeFn_scalarLiftFun K p ν H hH f)

end PL1.Walsh
