import PL1.IntrinsicNonBoundedComplete
import PL1.ScalarRealification
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The explicit cylinder-resolvent sequence

The normalized finite cylinder indicators are defined through their finite
Walsh expansions and are identified with the exact indicator functions.
Applying the zeroth reconstruction column gives the manuscript's concrete
bounded coherent sequence in the actual intrinsic Banach space.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PL1.ExplicitMartingale

open Walsh WalshExpectations Noise IntrinsicGraph ScalarRealification

/-- The cylinder through `s` determined by the first `m` coordinates. -/
def cylinder (m : ℕ) (s : Walsh.Group) : Set Walsh.Group :=
  {x | ∀ j : ℕ, j < m → x j = s j}

/-- The real normalized cylinder kernel, as an actual continuous polynomial. -/
def kernelContinuous (m : ℕ) (s : Walsh.Group) : C(Walsh.Group, ℝ) :=
  ∑ F ∈ (Finset.range m).powerset, character F s • characterContinuous F

theorem kernelContinuous_apply (m : ℕ) (s x : Walsh.Group) :
    kernelContinuous m s x = ∑ F ∈ (Finset.range m).powerset, character F (s * x) := by
  simp only [kernelContinuous, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, characterContinuous, ContinuousMap.coe_mk, character_mul]

theorem kernelContinuous_eq_prod (m : ℕ) (s x : Walsh.Group) :
    kernelContinuous m s x = ∏ j ∈ Finset.range m, (1 + signValue (s j * x j)) := by
  rw [kernelContinuous_apply, Finset.prod_one_add]
  rfl

theorem one_add_sign_mul (a b : Sign) :
    (1 + signValue (a * b) : ℝ) = if b = a then 2 else 0 := by
  classical
  rw [signValue_mul]
  rcases signValue_eq_one_or_neg_one a with ha | ha <;>
    rcases signValue_eq_one_or_neg_one b with hb | hb
  · have hab : b = a := signValue_injective (hb.trans ha.symm)
    norm_num [ha, hab]
  · have hab : b ≠ a := by intro h; subst b; linarith
    norm_num [ha, hb, hab]
  · have hab : b ≠ a := by intro h; subst b; linarith
    norm_num [ha, hb, hab]
  · have hab : b = a := signValue_injective (hb.trans ha.symm)
    norm_num [ha, hab]

/-- The finite Walsh polynomial is exactly `2^m` on its cylinder and zero
off that cylinder, at every point rather than only almost everywhere. -/
theorem kernelContinuous_eq_indicator (m : ℕ) (s x : Walsh.Group) :
    kernelContinuous m s x = (cylinder m s).indicator (fun _ => (2 : ℝ) ^ m) x := by
  classical
  rw [kernelContinuous_eq_prod]
  simp_rw [one_add_sign_mul]
  by_cases hx : x ∈ cylinder m s
  · rw [Set.indicator_of_mem hx]
    have h : ∀ j ∈ Finset.range m, x j = s j := fun j hj => hx j (Finset.mem_range.mp hj)
    simp only [Finset.prod_congr rfl (fun j hj => ite_eq_left (h j hj)), Finset.prod_const,
      Finset.card_range]
  · rw [Set.indicator_of_notMem hx]
    have h : ∃ j ∈ Finset.range m, x j ≠ s j := by
      simpa only [cylinder, Set.mem_ofPred_eq, not_forall, exists_prop, Finset.mem_range] using hx
    obtain ⟨j, hj, hneq⟩ := h
    exact Finset.prod_eq_zero hj (ite_eq_right hneq)

theorem kernelContinuous_nonneg (m : ℕ) (s x : Walsh.Group) :
    0 ≤ kernelContinuous m s x := by
  rw [kernelContinuous_eq_indicator]
  exact Set.indicator_nonneg (fun _ _ => by positivity) _

theorem integral_kernelContinuous (m : ℕ) (s : Walsh.Group) :
    ∫ x, kernelContinuous m s x ∂haar = 1 := by
  simp only [kernelContinuous, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    characterContinuous, ContinuousMap.coe_mk, smul_eq_mul]
  rw [integral_finsetSum _ (fun F _ => (integrable_character F).const_mul _)]
  simp_rw [integral_const_mul, Walsh.integral_character]
  simp

/-- The actual real `L1` normalized cylinder class. -/
def kernelRealL1 (m : ℕ) (s : Walsh.Group) : Lp ℝ 1 haar :=
  ContinuousMap.toLp 1 haar ℝ (kernelContinuous m s)

theorem kernelRealL1_eq_sum (m : ℕ) (s : Walsh.Group) :
    kernelRealL1 m s = ∑ F ∈ (Finset.range m).powerset, character F s • characterLp 1 F := by
  simp only [kernelRealL1, kernelContinuous, map_sum, map_smul, toLp_characterContinuous]

theorem coeFn_kernelRealL1 (m : ℕ) (s : Walsh.Group) :
    kernelRealL1 m s =ᵐ[haar] kernelContinuous m s :=
  ContinuousMap.coeFn_toLp haar (kernelContinuous m s)

theorem norm_kernelRealL1 (m : ℕ) (s : Walsh.Group) : ‖kernelRealL1 m s‖ = 1 := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ x, kernelContinuous m s x ∂haar := by
      apply integral_congr_ae
      filter_upwards [coeFn_kernelRealL1 m s] with x hx
      rw [hx, Real.norm_of_nonneg (kernelContinuous_nonneg m s x)]
    _ = 1 := integral_kernelContinuous m s

variable (K : Type*) [RCLike K]

/-- Scalar-valued normalized cylinder class, with the same real indicator. -/
def kernelL1 (m : ℕ) (s : Walsh.Group) : Lp K 1 haar := ofRealL1 K (kernelRealL1 m s)

theorem kernelL1_eq_sum (m : ℕ) (s : Walsh.Group) :
    kernelL1 K m s = ∑ F ∈ (Finset.range m).powerset,
      (character F s : K) • scalarCharacterLp K 1 F := by
  rw [kernelL1, kernelRealL1_eq_sum]
  simp only [map_sum, map_smul, ofRealL1_character]
  apply Finset.sum_congr rfl
  intro F hF
  exact (IsScalarTower.algebraMap_smul K (character F s) (scalarCharacterLp K 1 F)).symm

theorem coeFn_kernelL1 (m : ℕ) (s : Walsh.Group) :
    kernelL1 K m s =ᵐ[haar] fun x => ((kernelContinuous m s x : ℝ) : K) :=
  (coeFn_ofRealL1 K (kernelRealL1 m s)).trans ((coeFn_kernelRealL1 m s).fun_comp _)

theorem norm_kernelL1 (m : ℕ) (s : Walsh.Group) : ‖kernelL1 K m s‖ = 1 := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ x, kernelContinuous m s x ∂haar := by
      apply integral_congr_ae
      filter_upwards [coeFn_kernelL1 K m s] with x hx
      rw [hx, RCLike.norm_ofReal, abs_of_nonneg (kernelContinuous_nonneg m s x)]
    _ = 1 := integral_kernelContinuous m s

theorem expectation_kernelL1 (k m : ℕ) (s : Walsh.Group) :
    expectationL1 K k (kernelL1 K m s) = kernelL1 K (min k m) s := by
  classical
  have hfilter : ((Finset.range m).powerset.filter (fun F => F ⊆ Finset.range k)) =
      (Finset.range (min k m)).powerset := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, Finset.mem_range]
    constructor
    · rintro ⟨hm, hk⟩ j hj
      exact lt_min (hk hj) (hm hj)
    · intro h
      exact ⟨fun j hj => (lt_min_iff.mp (h hj)).2, fun j hj => (lt_min_iff.mp (h hj)).1⟩
  rw [kernelL1_eq_sum, map_sum]
  simp_rw [map_smul, expectationL1_character, smul_ite, smul_zero]
  rw [← Finset.sum_filter, hfilter, kernelL1_eq_sum]

/-- Walsh moments of the actual normalized cylinder class. -/
theorem fourier_kernelRealL1 (F : Finset ℕ) (m : ℕ) (s : Walsh.Group) :
    SingularConvolution.fourierFunctional F (kernelRealL1 m s) =
      if F ⊆ Finset.range m then character F s else 0 := by
  classical
  rw [kernelRealL1_eq_sum, map_sum]
  simp_rw [map_smul, smul_eq_mul, SingularConvolution.fourierFunctional_character]
  simp [Finset.mem_powerset, mul_ite]

/-- The actual intrinsic-space-valued cylinder-resolvent functions. -/
def beta (rates : ℕ → ℝ≥0) (m : ℕ) (s : Walsh.Group) :
    (dyadicSystem K rates).IntrinsicSpace :=
  (dyadicSystem K rates).column 0 (kernelL1 K m s)

/-- The fixed sequence from the manuscript is the trajectory through the
group identity: `R₁(2^m 1_{H_m})`. -/
def sequence (rates : ℕ → ℝ≥0) (m : ℕ) : (dyadicSystem K rates).IntrinsicSpace :=
  beta K rates m 1

theorem evalZero_beta (rates : ℕ → ℝ≥0) (m : ℕ) (s : Walsh.Group) :
    evalZero (dyadicSystem K rates).analysis (beta K rates m s) =
      resolventL1 K rates (dyadicTime 0) (kernelL1 K m s) := by
  rw [beta, DyadicSystem.evalZero_column]
  rfl

theorem norm_beta_le (rates : ℕ → ℝ≥0) (m : ℕ) (s : Walsh.Group) :
    ‖beta K rates m s‖ ≤ projectionBound := by
  have h := ((dyadicSystem K rates).column 0).le_opNorm (kernelL1 K m s)
  rw [norm_kernelL1, mul_one] at h
  exact h.trans ((dyadicSystem K rates).norm_column_le 0)

theorem norm_sequence_le (rates : ℕ → ℝ≥0) (m : ℕ) :
    ‖sequence K rates m‖ ≤ projectionBound := norm_beta_le K rates m 1

/-- Coherence holds for all two indices, with the exact minimum formula. -/
theorem intrinsicExpectation_beta (rates : ℕ → ℝ≥0) (k m : ℕ) (s : Walsh.Group) :
    intrinsicExpectation K rates k (beta K rates m s) = beta K rates (min k m) s := by
  apply evalZero_injective (dyadicSystem K rates).analysis
  rw [evalZero_intrinsicExpectation, evalZero_beta, evalZero_beta]
  have h := DFunLike.congr_fun
    (expectationL1_resolvent_commute K k rates (dyadicTime 0)) (kernelL1 K m s)
  change expectationL1 K k (resolventL1 K rates (dyadicTime 0) (kernelL1 K m s)) =
    resolventL1 K rates (dyadicTime 0) (expectationL1 K k (kernelL1 K m s)) at h
  rw [h, expectation_kernelL1]

theorem intrinsicExpectation_sequence (rates : ℕ → ℝ≥0) (k m : ℕ) :
    intrinsicExpectation K rates k (sequence K rates m) = sequence K rates (min k m) :=
  intrinsicExpectation_beta K rates k m 1

omit K in
/-- Singular convolution of these actual cylinder kernels is not Cauchy
in Haar `L1`, for any cylinder trajectory. -/
theorem not_cauchySeq_convolution_kernelRealL1
    (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (N : Set Walsh.Group) (hmN : haar N = 0) (hνN : ν N ≠ 0)
    (s : Walsh.Group) :
    ¬ CauchySeq (fun m => convolutionL1 (𝕜 := ℝ) ν (kernelRealL1 m s)) := by
  intro hc
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hc
  have hMom (F : Finset ℕ) : SingularConvolution.fourierFunctional F g =
      coefficient ν F * character F s := by
    have ht := ((SingularConvolution.fourierFunctional F).continuous.tendsto g).comp hg
    have he : Tendsto (fun m => SingularConvolution.fourierFunctional F
        (convolutionL1 ν (kernelRealL1 m s))) atTop
          (𝓝 (coefficient ν F * character F s)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (F.sup id + 1)] with m hm
      have hF : F ⊆ Finset.range m := by
        intro j hj
        exact Finset.mem_range.mpr ((Finset.le_sup (f := id) hj).trans_lt (by omega))
      rw [SingularConvolution.fourierFunctional_convolution_apply, fourier_kernelRealL1,
        ite_eq_left hF]
    exact tendsto_nhds_unique ht he
  let g' := convolutionL1 (𝕜 := ℝ) (Measure.dirac s) g
  apply SingularConvolution.no_integrable_density_of_null_carrier ν N hmN hνN
  refine ⟨g', L1.integrable_coeFn g', ?_⟩
  intro F
  rw [← SingularConvolution.fourierFunctional_apply]
  change SingularConvolution.fourierFunctional F
    (convolutionL1 (𝕜 := ℝ) (Measure.dirac s) g) = coefficient ν F
  rw [SingularConvolution.fourierFunctional_convolution_apply, hMom]
  have hdir : coefficient (Measure.dirac s) F = character F s := by
    simp [coefficient]
  rw [hdir]
  calc
    character F s * (coefficient ν F * character F s) =
        coefficient ν F * (character F s * character F s) := by ring
    _ = coefficient ν F := by rw [character_mul_self, mul_one]

theorem re_evalZero_beta (rates : ℕ → ℝ≥0) (m : ℕ) (s : Walsh.Group) :
    reL1 K (evalZero (dyadicSystem K rates).analysis (beta K rates m s)) =
      resolventL1 ℝ rates (dyadicTime 0) (kernelRealL1 m s) := by
  let := isProbabilityMeasure_resolventMeasure rates (dyadicTime 0).property
  rw [evalZero_beta]
  exact DFunLike.congr_fun (reL1_convolution_ofRealL1 K
    (resolventMeasure rates (dyadicTime 0))) (kernelRealL1 m s)

/-- Every trajectory of the explicitly defined intrinsic-space function
fails to be norm Cauchy whenever the actual zeroth resolvent is singular. -/
theorem not_cauchySeq_beta_of_null_carrier (rates : ℕ → ℝ≥0)
    (N : Set Walsh.Group) (hmN : haar N = 0)
    (hνN : resolventMeasure rates (dyadicTime 0) N ≠ 0) (s : Walsh.Group) :
    ¬ CauchySeq (fun m => beta K rates m s) := by
  let := isProbabilityMeasure_resolventMeasure rates (dyadicTime 0).property
  intro hc
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  have hzero := ((evalZero (dyadicSystem K rates).analysis).continuous.tendsto a).comp ha
  have hre := ((reL1 K).continuous.tendsto _).comp hzero
  have ht : Tendsto (fun m => convolutionL1 (𝕜 := ℝ)
      (resolventMeasure rates (dyadicTime 0)) (kernelRealL1 m s)) atTop
      (𝓝 (reL1 K (evalZero (dyadicSystem K rates).analysis a))) := by
    convert hre using 1
    funext m
    exact (re_evalZero_beta K rates m s).symm
  exact not_cauchySeq_convolution_kernelRealL1 (resolventMeasure rates (dyadicTime 0))
    N hmN hνN s ht.cauchySeq

theorem schur_beta_not_cauchy (s : Walsh.Group) :
    ¬ CauchySeq (fun m => beta K schurRates m s) :=
  not_cauchySeq_beta_of_null_carrier K schurRates (Carrier.commonSet 0)
    (Carrier.haar_commonSet_eq_zero 0) (by rw [schur_resolvent_commonSet]; exact one_ne_zero) s

theorem constant_beta_not_cauchy (s : Walsh.Group) :
    ¬ CauchySeq (fun m => beta K constantRates m s) :=
  not_cauchySeq_beta_of_null_carrier K constantRates (Carrier.commonSet 0)
    (Carrier.haar_commonSet_eq_zero 0) (by rw [constant_resolvent_commonSet]; exact one_ne_zero) s

theorem schur_sequence_not_cauchy : ¬ CauchySeq (sequence K schurRates) :=
  schur_beta_not_cauchy K 1

theorem constant_sequence_not_cauchy : ¬ CauchySeq (sequence K constantRates) :=
  constant_beta_not_cauchy K 1

end PL1.ExplicitMartingale
