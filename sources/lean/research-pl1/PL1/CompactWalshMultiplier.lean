import PL1.WalshModel
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PL1.ConcreteResolvents
import PL1.LpInclusions

/-!
# Compact diagonal Walsh multipliers

This file proves compactness by finite-rank approximation in operator norm.
The coefficient condition is convergence to zero along the cofinite filter.
The final rate lemmas establish this condition for resolvent coefficients.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal BigOperators

namespace PL1
namespace WalshMultiplier

variable {ι : Type*} (𝕜 : Type*) [RCLike 𝕜]

abbrev Coefficients (ι : Type*) (𝕜 : Type*) [RCLike 𝕜] := lp (fun _ : ι => 𝕜) ∞
abbrev SquareSummable (ι : Type*) (𝕜 : Type*) [RCLike 𝕜] := lp (fun _ : ι => 𝕜) 2

/-- Bounded coordinatewise multiplication on square-summable scalar families. -/
def diagonalL : Coefficients ι 𝕜 →L[𝕜] SquareSummable ι 𝕜 →L[𝕜] SquareSummable ι 𝕜 :=
  lp.holderL (p := ∞) (q := 2) 2 (fun _ : ι => ContinuousLinearMap.mul 𝕜 𝕜)
    (K := 1) (fun _ => ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜)

@[simp] theorem diagonalL_apply (a : Coefficients ι 𝕜) (x : SquareSummable ι 𝕜) (i : ι) :
    diagonalL 𝕜 a x i = a i * x i := rfl

theorem norm_diagonalL_le : ‖(diagonalL 𝕜 : Coefficients ι 𝕜 →L[𝕜] _)‖ ≤ 1 :=
  lp.norm_holderL_le (p := ∞) (q := 2) 2 (fun _ : ι => ContinuousLinearMap.mul 𝕜 𝕜)
    (K := 1) (fun _ => ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜)

theorem diagonalL_single [DecidableEq ι] (j : ι) (c : 𝕜) :
    diagonalL 𝕜 (lp.single ∞ j c) =
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ι => 𝕜) 2 j).comp
        ((ContinuousLinearMap.mul 𝕜 𝕜 c).comp (lp.evalCLM 𝕜 (fun _ : ι => 𝕜) 2 j)) := by
  ext x i
  change lp.single (E := fun _ : ι => 𝕜) ∞ j c i * x i =
    lp.single (E := fun _ : ι => 𝕜) 2 j (c * x j) i
  by_cases hi : i = j <;> simp [lp.single_apply, hi]

theorem compact_diagonalL_single [DecidableEq ι] (j : ι) (c : 𝕜) :
    IsCompactOperator (diagonalL 𝕜 (lp.single ∞ j c)) := by
  rw [diagonalL_single]
  exact (isCompactOperator_of_locallyCompactSpace_dom
    ((ContinuousLinearMap.mul 𝕜 𝕜 c).comp (lp.evalCLM 𝕜 (fun _ : ι => 𝕜) 2 j))).clm_comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ι => 𝕜) 2 j)

theorem compact_diagonalL_sum [DecidableEq ι] (s : Finset ι) (a : ι → 𝕜) :
    IsCompactOperator (diagonalL 𝕜 (∑ i ∈ s, lp.single ∞ i (a i))) := by
  induction s using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero (M₁ := SquareSummable ι 𝕜)
      (M₂ := SquareSummable ι 𝕜))
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj, map_add]
      exact (compact_diagonalL_single 𝕜 j (a j)).add ih

/-- A null family has finite truncations converging in the supremum norm. -/
theorem tendsto_truncations [DecidableEq ι] (a : Coefficients ι 𝕜)
    (ha : Tendsto (fun i => a i) cofinite (𝓝 0)) :
    Tendsto (fun s : Finset ι => ∑ i ∈ s, lp.single ∞ i (a i)) atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he : ∀ᶠ i in cofinite, ‖a i‖ < ε / 2 := by
    have hn : Tendsto (fun i => ‖a i‖) cofinite (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero] using ha.norm
    exact hn.eventually (gt_mem_nhds (half_pos hε))
  have hfinite := eventually_cofinite.mp he
  refine ⟨hfinite.toFinset, fun s hs => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (b := ε / 2) _ (half_lt_self hε)
  apply lp.norm_le_of_forall_le (half_pos hε).le
  intro i
  have hval : (∑ j ∈ s, lp.single ∞ j (a j)) i = if i ∈ s then a i else 0 := by
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  change ‖(∑ j ∈ s, lp.single ∞ j (a j)) i - a i‖ ≤ ε / 2
  rw [hval]
  by_cases hi : i ∈ s
  · simp [hi, (half_pos hε).le]
  · have hai : ‖a i‖ < ε / 2 := by
      by_contra h
      exact hi (hs (hfinite.mem_toFinset.mpr h))
    simpa [hi] using hai.le

/-- A bounded diagonal operator with coefficients vanishing at infinity is compact. -/
theorem compact_diagonalL [DecidableEq ι] (a : Coefficients ι 𝕜)
    (ha : Tendsto (fun i => a i) cofinite (𝓝 0)) :
    IsCompactOperator (diagonalL 𝕜 a) := by
  apply isCompactOperator_of_tendsto ((diagonalL 𝕜).continuous.tendsto a |>.comp
    (tendsto_truncations 𝕜 a ha))
  exact Eventually.of_forall (fun s => compact_diagonalL_sum 𝕜 s (fun i => a i))

/-- Turn an arbitrary null scalar family into its bounded coefficient vector. -/
def nullCoefficients (a : ι → 𝕜) (ha : Tendsto a cofinite (𝓝 0)) : Coefficients ι 𝕜 :=
  ⟨a, memℓp_infty ha.norm.bddAbove_range_of_cofinite⟩

section HilbertSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Transfer a coordinate multiplier to any Hilbert space with a specified basis. -/
def hilbertDiagonal (b : HilbertBasis ι 𝕜 E) (a : Coefficients ι 𝕜) : E →L[𝕜] E :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((diagonalL 𝕜 a).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem norm_hilbertDiagonal_le (b : HilbertBasis ι 𝕜 E) (a : Coefficients ι 𝕜) :
    ‖hilbertDiagonal 𝕜 b a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro x
  change ‖b.repr.symm (diagonalL 𝕜 a (b.repr x))‖ ≤ ‖a‖ * ‖x‖
  rw [b.repr.symm.norm_map]
  have hD : ‖diagonalL 𝕜 a‖ ≤ ‖a‖ := by
    simpa only [one_mul] using (diagonalL 𝕜).le_of_opNorm_le (norm_diagonalL_le 𝕜) a
  simpa only [b.repr.norm_map] using (diagonalL 𝕜 a).le_of_opNorm_le hD (b.repr x)

theorem compact_hilbertDiagonal [DecidableEq ι] (b : HilbertBasis ι 𝕜 E)
    (a : Coefficients ι 𝕜) (ha : Tendsto (fun i => a i) cofinite (𝓝 0)) :
    IsCompactOperator (hilbertDiagonal 𝕜 b a) :=
  ((compact_diagonalL 𝕜 a ha).comp_clm b.repr.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
    b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem hilbertDiagonal_apply_basis [DecidableEq ι] (b : HilbertBasis ι 𝕜 E)
    (a : Coefficients ι 𝕜) (i : ι) : hilbertDiagonal 𝕜 b a (b i) = a i • b i := by
  apply b.repr.injective
  change b.repr (b.repr.symm (diagonalL 𝕜 a (b.repr (b i)))) = b.repr (a i • b i)
  rw [b.repr.apply_symm_apply, map_smul, b.repr_self]
  apply lp.ext
  funext j
  by_cases hj : j = i <;> simp [diagonalL_apply, lp.coeFn_smul, lp.single_apply, hj]

/-- Any bounded operator diagonal on a Hilbert basis, with null eigenvalues, is compact. -/
theorem compact_of_diagonal [DecidableEq ι] (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] E)
    (a : ι → 𝕜) (ha : Tendsto a cofinite (𝓝 0))
    (hT : ∀ i, T (b i) = a i • b i) : IsCompactOperator T := by
  have hEq : T = hilbertDiagonal 𝕜 b (nullCoefficients 𝕜 a ha) := by
    apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
    rintro x ⟨i, rfl⟩
    rw [hT, hilbertDiagonal_apply_basis]
    rfl
  rw [hEq]
  exact compact_hilbertDiagonal 𝕜 b (nullCoefficients 𝕜 a ha) ha

end HilbertSpace

section Rates

variable (rates : ι → ℝ)

/-- Only finitely many finite supports can have a bounded total rate. -/
theorem finite_rate_sublevels (hRate : ∀ i, 0 ≤ rates i)
    (hRateTop : Tendsto rates cofinite atTop) (L : ℝ) :
    Set.Finite {F : Finset ι | ∑ i ∈ F, rates i ≤ L} := by
  classical
  have he : ∀ᶠ i in cofinite, L < rates i := hRateTop.eventually (eventually_gt_atTop L)
  have hfinite : Set.Finite {i | rates i ≤ L} := by
    simpa only [not_lt] using eventually_cofinite.mp he
  apply hfinite.toFinset.powerset.finite_toSet.subset
  intro F hF
  apply Finset.mem_powerset.mpr
  intro i hi
  apply hfinite.mem_toFinset.mpr
  exact (Finset.single_le_sum (fun j _ => hRate j) hi).trans hF

theorem tendsto_rateSum (hRate : ∀ i, 0 ≤ rates i) (hRateTop : Tendsto rates cofinite atTop) :
    Tendsto (fun F : Finset ι => ∑ i ∈ F, rates i) cofinite atTop := by
  apply tendsto_atTop.mpr
  intro L
  apply eventually_cofinite.mpr
  exact (finite_rate_sublevels rates hRate hRateTop L).subset (fun F hF => (not_le.mp hF).le)

theorem tendsto_resolvent_coefficients (hRate : ∀ i, 0 ≤ rates i)
    (hRateTop : Tendsto rates cofinite atTop) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun F : Finset ι => (1 + t * ∑ i ∈ F, rates i)⁻¹) cofinite (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  exact tendsto_const_nhds.add_atTop ((tendsto_rateSum rates hRate hRateTop).const_mul_atTop ht)

end Rates

/-- Growth of the actual rate sequence used for the Schur example. -/
theorem tendsto_schurRates :
    Tendsto (fun j : ℕ => Real.sqrt (Real.log (j + 2))) cofinite atTop := by
  rw [Nat.cofinite_eq_atTop]
  apply Real.tendsto_sqrt_atTop.comp
  apply Real.tendsto_log_atTop.comp
  exact (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop).atTop_add
    (tendsto_const_nhds (x := (2 : ℝ)))

/-- A direct compactness criterion for a resolvent acting on the actual Haar L2. -/
theorem compact_walsh_resolvent_of_diagonal (rates : ℕ → ℝ)
    (hRate : ∀ j, 0 ≤ rates j) (hRateTop : Tendsto rates cofinite atTop)
    {t : ℝ} (ht : 0 < t) (T : Lp 𝕜 2 Walsh.haar →L[𝕜] Lp 𝕜 2 Walsh.haar)
    (hT : ∀ F : Finset ℕ, T (Walsh.scalarCharacterLp 𝕜 2 F) =
      (((1 + t * ∑ j ∈ F, rates j)⁻¹ : ℝ) : 𝕜) • Walsh.scalarCharacterLp 𝕜 2 F) :
    IsCompactOperator T := by
  apply compact_of_diagonal 𝕜 (Walsh.scalarHilbertBasis 𝕜) T
    (fun F => (((1 + t * ∑ j ∈ F, rates j)⁻¹ : ℝ) : 𝕜))
  · simpa only [RCLike.ofReal_zero, Function.comp_def, RCLike.ofReal_inv] using
      RCLike.continuous_ofReal.tendsto 0 |>.comp (tendsto_resolvent_coefficients rates hRate hRateTop ht)
  · intro F
    simpa only [Walsh.scalarHilbertBasis_apply] using hT F

theorem compact_schur_resolvent_of_diagonal {t : ℝ} (ht : 0 < t)
    (T : Lp 𝕜 2 Walsh.haar →L[𝕜] Lp 𝕜 2 Walsh.haar)
    (hT : ∀ F : Finset ℕ, T (Walsh.scalarCharacterLp 𝕜 2 F) =
      (((1 + t * ∑ j ∈ F, Real.sqrt (Real.log (j + 2)))⁻¹ : ℝ) : 𝕜) •
        Walsh.scalarCharacterLp 𝕜 2 F) : IsCompactOperator T :=
  compact_walsh_resolvent_of_diagonal 𝕜 _ (fun _ => Real.sqrt_nonneg _) tendsto_schurRates ht T hT

section ConstructedResolvent

variable (rates : ℕ → ℝ) (hRate : ∀ j, 0 ≤ rates j) (t : ℝ) (ht : 0 ≤ t)
include hRate ht

theorem norm_resolvent_coefficient_le_one (F : Finset ℕ) :
    ‖(((1 + t * ∑ j ∈ F, rates j)⁻¹ : ℝ) : 𝕜)‖ ≤ 1 := by
  have hs : 0 ≤ ∑ j ∈ F, rates j := Finset.sum_nonneg (fun j _ => hRate j)
  have hd : 0 < 1 + t * ∑ j ∈ F, rates j := by positivity
  rw [RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr hd.le)]
  exact (inv_le_one₀ hd).mpr (by nlinarith)

/-- The bounded family of all resolvent eigenvalues; growth of the rates is not required. -/
def resolventCoefficients : Coefficients (Finset ℕ) 𝕜 :=
  ⟨fun F => (((1 + t * ∑ j ∈ F, rates j)⁻¹ : ℝ) : 𝕜), memℓp_infty
    ⟨1, by rintro r ⟨F, rfl⟩; exact norm_resolvent_coefficient_le_one 𝕜 rates hRate t ht F⟩⟩

theorem norm_resolventCoefficients_le_one : ‖resolventCoefficients 𝕜 rates hRate t ht‖ ≤ 1 := by
  apply lp.norm_le_of_forall_le zero_le_one
  exact norm_resolvent_coefficient_le_one 𝕜 rates hRate t ht

/-- A genuine bounded resolvent multiplier on Haar L2, for any nonnegative rates and time. -/
def resolventL2 : Lp 𝕜 2 Walsh.haar →L[𝕜] Lp 𝕜 2 Walsh.haar :=
  hilbertDiagonal 𝕜 (Walsh.scalarHilbertBasis 𝕜) (resolventCoefficients 𝕜 rates hRate t ht)

theorem norm_resolventL2_le_one : ‖resolventL2 𝕜 rates hRate t ht‖ ≤ 1 :=
  (norm_hilbertDiagonal_le 𝕜 _ _).trans (norm_resolventCoefficients_le_one 𝕜 rates hRate t ht)

theorem resolventL2_apply_character (F : Finset ℕ) :
    resolventL2 𝕜 rates hRate t ht (Walsh.scalarCharacterLp 𝕜 2 F) =
      (((1 + t * ∑ j ∈ F, rates j)⁻¹ : ℝ) : 𝕜) • Walsh.scalarCharacterLp 𝕜 2 F := by
  simpa only [Walsh.scalarHilbertBasis_apply, resolventL2, resolventCoefficients] using
    hilbertDiagonal_apply_basis 𝕜 (Walsh.scalarHilbertBasis 𝕜)
      (resolventCoefficients 𝕜 rates hRate t ht) F

theorem compact_resolventL2 (hRateTop : Tendsto rates cofinite atTop) (htpos : 0 < t) :
    IsCompactOperator (resolventL2 𝕜 rates hRate t ht) :=
  compact_walsh_resolvent_of_diagonal 𝕜 rates hRate hRateTop htpos _
    (resolventL2_apply_character 𝕜 rates hRate t ht)

end ConstructedResolvent

section ActualResolvent

variable (rates : ℕ → ℝ≥0) (t : Noise.PositiveTime)

/-- The L2 extension of the manuscript's concrete convolution resolvent. -/
def actualResolventL2 : Lp 𝕜 2 Walsh.haar →L[𝕜] Lp 𝕜 2 Walsh.haar :=
  resolventL2 𝕜 (fun j => (rates j : ℝ)) (fun j => (rates j).coe_nonneg) t t.property.le

theorem norm_actualResolventL2_le_one : ‖actualResolventL2 𝕜 rates t‖ ≤ 1 :=
  norm_resolventL2_le_one 𝕜 _ _ _ _

theorem actualResolventL2_apply_character (F : Finset ℕ) :
    actualResolventL2 𝕜 rates t (Walsh.scalarCharacterLp 𝕜 2 F) =
      (((1 + (t : ℝ) * Noise.rateSum rates F)⁻¹ : ℝ) : 𝕜) •
        Walsh.scalarCharacterLp 𝕜 2 F :=
  resolventL2_apply_character 𝕜 _ _ _ _ F

/-- The constructed L2 multiplier agrees with the actual convolution on their common domain. -/
theorem actualResolventL2_l2ToL1 :
    (Walsh.l2ToL1 (𝕜 := 𝕜)).comp (actualResolventL2 𝕜 rates t) =
      (Noise.resolventL1 𝕜 rates t).comp Walsh.l2ToL1 := by
  apply ContinuousLinearMap.ext_on (Walsh.dense_span_scalarCharacterLp 𝕜 2 (by norm_num))
  rintro f ⟨F, rfl⟩
  simp only [ContinuousLinearMap.comp_apply, actualResolventL2_apply_character,
    map_smul, Walsh.l2ToL1_scalarCharacter, Noise.resolventL1_scalarCharacter]

theorem compact_actualResolventL2
    (hRateTop : Tendsto (fun j => (rates j : ℝ)) cofinite atTop) :
    IsCompactOperator (actualResolventL2 𝕜 rates t) :=
  compact_resolventL2 𝕜 _ _ _ _ hRateTop t.property

theorem compact_schur_actualResolventL2 :
    IsCompactOperator (actualResolventL2 𝕜 Noise.schurRates t) :=
  compact_actualResolventL2 𝕜 Noise.schurRates t tendsto_schurRates

theorem compact_resolventL1_on_L2
    (hRateTop : Tendsto (fun j => (rates j : ℝ)) cofinite atTop) :
    IsCompactOperator ((Noise.resolventL1 𝕜 rates t).comp Walsh.l2ToL1) := by
  rw [← actualResolventL2_l2ToL1]
  exact (compact_actualResolventL2 𝕜 rates t hRateTop).clm_comp Walsh.l2ToL1

/-- The concrete resolvent has compact restriction from bounded functions to Haar L1. -/
theorem compact_resolventL1_on_Linfty
    (hRateTop : Tendsto (fun j => (rates j : ℝ)) cofinite atTop) :
    IsCompactOperator ((Noise.resolventL1 𝕜 rates t).comp
      ((Walsh.l2ToL1 (𝕜 := 𝕜)).comp Walsh.linftyToL2)) := by
  rw [← ContinuousLinearMap.comp_assoc]
  exact (compact_resolventL1_on_L2 𝕜 rates t hRateTop).comp_clm Walsh.linftyToL2

theorem compact_schur_resolventL1_on_Linfty :
    IsCompactOperator ((Noise.resolventL1 𝕜 Noise.schurRates t).comp
      ((Walsh.l2ToL1 (𝕜 := 𝕜)).comp Walsh.linftyToL2)) :=
  compact_resolventL1_on_Linfty 𝕜 Noise.schurRates t tendsto_schurRates

/-- Compactness stated using the direct canonical inclusion from L-infinity to L1. -/
theorem compact_resolventL1_restriction
    (hRateTop : Tendsto (fun j => (rates j : ℝ)) cofinite atTop) :
    IsCompactOperator ((Noise.resolventL1 𝕜 rates t).comp
      (ProbabilityLp.inclusion Walsh.haar 1 ∞ le_top)) := by
  simpa only [Walsh.l2ToL1, Walsh.linftyToL2, ProbabilityLp.inclusion_comp] using
    compact_resolventL1_on_Linfty 𝕜 rates t hRateTop

theorem compact_schur_resolventL1_restriction :
    IsCompactOperator ((Noise.resolventL1 𝕜 Noise.schurRates t).comp
      (ProbabilityLp.inclusion Walsh.haar 1 ∞ le_top)) :=
  compact_resolventL1_restriction 𝕜 Noise.schurRates t tendsto_schurRates

end ActualResolvent

end WalshMultiplier
end PL1
