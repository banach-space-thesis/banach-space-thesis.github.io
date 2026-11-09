import PL1.ConstantTailSpikes
import PL1.IntrinsicWalshBlocks
import PL1.L1Multiplication
import PL1.HeadTail
import PL1.IntrinsicSpikeFamilies

/-! # Exact tail expectations and norms in the original intrinsic space -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PL1.IntrinsicTailNorm
open Walsh WalshExpectations Noise IntrinsicGraph L1Multiplication

variable (K : Type*) [RCLike K]

theorem norm_constantL1 : ‖scalarCharacterLp K 1 ∅‖ = 1 := by
  rw [L1.norm_eq_integral_norm]
  have h : (fun x => ‖scalarCharacterLp K 1 ∅ x‖) =ᵐ[haar] fun _ => (1 : ℝ) := by
    filter_upwards [coeFn_scalarCharacterLp K 1 ∅] with x hx
    simp only [hx, scalarCharacter, character_empty, RCLike.ofReal_one, norm_one]
  rw [integral_congr_ae h]
  simp

theorem coord_constant (rates : ℕ → ℝ≥0) (n : ℕ) :
    coord (dyadicSystem K rates).analysis n (intrinsicCharacter K rates ∅) =
      if n = 0 then scalarCharacterLp K 1 ∅ else 0 := by
  rw [coord_eq, evalZero_intrinsicCharacter]
  cases n with
  | zero => rfl
  | succ n =>
    change (((ResolventEstimates.dyadicRatio ^ (n + 1))⁻¹ : ℝ) : K) •
        (scalarCharacterLp K 1 ∅ - resolventL1 K rates (dyadicTime (n + 1))
          (scalarCharacterLp K 1 ∅)) = 0
    rw [resolventL1_scalarCharacter]
    simp [rateSum]

theorem norm_intrinsicConstant (rates : ℕ → ℝ≥0) :
    ‖intrinsicCharacter K rates ∅‖ = 1 := by
  rw [norm_eq_tsum]
  simp only [coord_constant, apply_ite norm, norm_zero]
  rw [tsum_ite_eq]
  exact norm_constantL1 K

theorem intrinsicConstant_mem_range (rates : ℕ → ℝ≥0) (m : ℕ) :
    intrinsicCharacter K rates ∅ ∈ (intrinsicExpectation K rates m).range := by
  refine ⟨intrinsicCharacter K rates ∅, ?_⟩
  change intrinsicExpectation K rates m (intrinsicCharacter K rates ∅) = _
  simp only [intrinsicExpectation_character, Finset.empty_subset, ite_true]

theorem multiplier_constant_ae (q : C(Walsh.Group, ℝ)) :
    multiplier K q (scalarCharacterLp K 1 ∅) =ᵐ[haar] fun x => (q x : K) := by
  filter_upwards [coeFn_multiplier K q (scalarCharacterLp K 1 ∅),
    coeFn_scalarCharacterLp K 1 ∅] with x hx hy
  rw [hx, hy]
  simp only [scalarCharacter, character_empty, RCLike.ofReal_one, RCLike.real_smul_eq_coe_mul, mul_one]

/-- Averaging a finite tail density of integral one over the genuine tail
Haar subgroup gives the constant one, for every initial head length. -/
theorem expectation_multiplier_constant (m : ℕ) {S : Finset ℕ}
    (hS : Disjoint S (Finset.range m)) (q : C(Walsh.Group, ℝ))
    (hq : HeadTail.DependsOn S q) (hq1 : ∫ x, q x ∂haar = 1) :
    expectationL1 K m (multiplier K q (scalarCharacterLp K 1 ∅)) =
      scalarCharacterLp K 1 ∅ := by
  have hi (x : Walsh.Group) : (∫ y, (q (x * y) : K) ∂tailMeasure m) = 1 := by
    rw [tailMeasure, integral_map (continuous_tailProjection m).measurable.aemeasurable
      (RCLike.continuous_ofReal.comp
        (q.continuous.comp (continuous_const.mul continuous_id))).aestronglyMeasurable]
    have ht (y : Walsh.Group) : q (x * tailProjection m y) = q (x * y) := by
      apply hq
      intro j hj
      have hjm : ¬ j < m := by
        intro h
        exact Finset.disjoint_left.mp hS hj (Finset.mem_range.mpr h)
      simp only [Pi.mul_apply, tailProjection, hjm, ite_false]
    simp_rw [ht]
    rw [integral_mul_left_eq_self (fun y => (q y : K)) x]
    have he : (fun y => (q y : K)) = fun y => q y • (1 : K) := by
      funext y
      simp only [RCLike.real_smul_eq_coe_mul, mul_one]
    rw [he, integral_smul_const, hq1, one_smul]
  apply Lp.ext
  filter_upwards [convolutionL1_ae_eq_integral_of_ae_eq (tailMeasure m)
      (multiplier_constant_ae K q), coeFn_scalarCharacterLp K 1 ∅] with x hx hy
  change (convolutionL1 (tailMeasure m) (multiplier K q (scalarCharacterLp K 1 ∅))) x = _
  rw [hx, hi, hy]
  simp only [scalarCharacter, character_empty, RCLike.ofReal_one]

theorem intrinsicExpectation_tailProduct (rates : ℕ → ℝ≥0) (m : ℕ)
    {S : Finset ℕ} (hS : Disjoint S (Finset.range m)) (q : C(Walsh.Group, ℝ))
    (hq : HeadTail.DependsOn S q) (hq1 : ∫ x, q x ∂haar = 1)
    (g : (dyadicSystem K rates).IntrinsicSpace)
    (hg : evalZero (dyadicSystem K rates).analysis g =
      multiplier K q (scalarCharacterLp K 1 ∅)) :
    intrinsicExpectation K rates m g = intrinsicCharacter K rates ∅ := by
  apply evalZero_injective (dyadicSystem K rates).analysis
  rw [evalZero_intrinsicExpectation, hg, expectation_multiplier_constant K m hS q hq hq1,
    evalZero_intrinsicCharacter]

theorem norm_id_sub_intrinsicExpectation_le (rates : ℕ → ℝ≥0) (m : ℕ) :
    ‖ContinuousLinearMap.id K (dyadicSystem K rates).IntrinsicSpace -
      intrinsicExpectation K rates m‖ ≤ 2 := by
  have h := norm_sub_le (ContinuousLinearMap.id K (dyadicSystem K rates).IntrinsicSpace)
    (intrinsicExpectation K rates m)
  have hid := ContinuousLinearMap.norm_id_le (𝕜 := K)
    (E := (dyadicSystem K rates).IntrinsicSpace)
  linarith [norm_intrinsicExpectation_le K rates m]

/-- Actual tail densities give the exact norm two of every complementary
coordinate projection. This proof uses the explicit spikes directly. -/
theorem norm_id_sub_intrinsicExpectation_eq_two_of_families (rates : ℕ → ℝ≥0)
    (hQ : ∀ (d : ℕ) (T : PositiveTime) (δ : ℝ), 0 < δ →
      Nonempty (TailSpikes.RateFamily rates d T δ)) (m : ℕ) :
    ‖ContinuousLinearMap.id K (dyadicSystem K rates).IntrinsicSpace -
      intrinsicExpectation K rates m‖ = 2 := by
  let P := ContinuousLinearMap.id K (dyadicSystem K rates).IntrinsicSpace -
    intrinsicExpectation K rates m
  have hup : ‖P‖ ≤ 2 := norm_id_sub_intrinsicExpectation_le K rates m
  have hlow (ε : ℝ) (hε : 0 < ε) : 2 - ε < ‖P‖ := by
    obtain ⟨T, hT⟩ := IntrinsicSpikes.exists_eta_lt (div_pos hε (by norm_num : (0:ℝ)<16))
    obtain ⟨Q⟩ := hQ m T (ε / 16) (by positivity)
    let c := intrinsicCharacter K rates ∅
    have hc : ‖c‖ = 1 := norm_intrinsicConstant K rates
    have hce : ‖evalZero (dyadicSystem K rates).analysis c‖ = 1 := by
      rw [evalZero_intrinsicCharacter, norm_constantL1]
    have hcV : c ∈ (intrinsicExpectation K rates m).range := intrinsicConstant_mem_range K rates m
    obtain ⟨g, hge, _havg, hgn, hgs⟩ := IntrinsicSpikeFamilies.exists_products Q (-c) c
      ((intrinsicExpectation K rates m).range.neg_mem hcV) hcV
    let a : FiniteCoordinateKernels.Assignments Q.coordinates := fun _ => 1
    have hgm : intrinsicExpectation K rates m (g a) = c := by
      apply intrinsicExpectation_tailProduct K rates m Q.beyond_prefix (Q.q a)
        (Q.q_depends a) (Q.integral_one a)
      simpa only [c, evalZero_intrinsicCharacter] using hge a
    have hgNorm : ‖g a‖ ≤ 1 + IntrinsicSpikes.eta T := by
      have hn := (abs_le.mp (hgn a)).2
      rw [hc, hce, mul_one] at hn
      linarith
    have hs : 2 - 4 * (ε / 16) - IntrinsicSpikes.eta T ≤ ‖P (g a)‖ := by
      have h := hgs a
      rw [norm_neg, hc, hce, mul_one] at h
      have hp : P (g a) = -c + g a := by
        simp only [P, sub_apply, ContinuousLinearMap.id_apply, hgm]
        abel
      rw [hp]
      nlinarith
    have hop := P.le_opNorm (g a)
    have hmul := mul_le_mul_of_nonneg_left hgNorm (norm_nonneg P)
    have herr := mul_le_mul_of_nonneg_right hup (IntrinsicSpikes.eta_pos T).le
    nlinarith
  apply le_antisymm hup
  by_contra h
  have he : 0 < (2 - ‖P‖) / 2 := by linarith
  have := hlow ((2 - ‖P‖) / 2) he
  linarith

theorem schur_norm_id_sub_intrinsicExpectation_eq_two (m : ℕ) :
    ‖ContinuousLinearMap.id K (dyadicSystem K schurRates).IntrinsicSpace -
      intrinsicExpectation K schurRates m‖ = 2 :=
  norm_id_sub_intrinsicExpectation_eq_two_of_families K schurRates
    (fun d T _δ hδ => TailSpikes.exists_family d T hδ) m

theorem constant_norm_id_sub_intrinsicExpectation_eq_two (m : ℕ) :
    ‖ContinuousLinearMap.id K (dyadicSystem K constantRates).IntrinsicSpace -
      intrinsicExpectation K constantRates m‖ = 2 :=
  norm_id_sub_intrinsicExpectation_eq_two_of_families K constantRates
    (fun d T _δ hδ => TailSpikes.exists_constant_family d T hδ) m

end PL1.IntrinsicTailNorm
