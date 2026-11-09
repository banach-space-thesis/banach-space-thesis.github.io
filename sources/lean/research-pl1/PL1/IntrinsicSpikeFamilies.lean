import PL1.IntrinsicHeadRepresentatives
import PL1.IntrinsicSpikeAverages
import PL1.IntrinsicSpikes
import PL1.TailSpikeMultiplication
import PL1.DaugavetAveraging

/-!
# Actual finite spike families in the intrinsic space

Finite head representatives, genuine tail families, Haar independence and the
proved resolvent commutator discharge every input to the intrinsic coordinate
estimates. The resulting family lives in the original dyadic intrinsic graph.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace PL1.IntrinsicSpikeFamilies
open Noise Walsh IntrinsicGraph IntrinsicHeadRepresentatives
open FiniteCoordinateKernels L1Multiplication

variable {K : Type*} [RCLike K]

theorem coordinate_norm_preserved {rates : ℕ → ℝ≥0} {d : ℕ}
    {T : PositiveTime} {δ : ℝ} (Q : TailSpikes.RateFamily rates d T δ)
    (a : Assignments Q.coordinates) {f : (dyadicSystem K rates).IntrinsicSpace}
    (hf : f ∈ (intrinsicExpectation K rates d).range) (n : ℕ) :
    ‖multiplier K (Q.q a) (coord (dyadicSystem K rates).analysis n f)‖ =
      ‖coord (dyadicSystem K rates).analysis n f‖ := by
  obtain ⟨F, hF, hFeq⟩ := continuousRepresentative_coord_of_range rates d n hf
  rw [← hFeq]
  exact HeadTail.norm_multiplier_toLp_of_density Q.beyond_prefix.symm F (Q.q a)
    hF (Q.q_depends a) (ae_of_all _ (Q.nonnegative a)) (Q.integral_one a)

theorem coordinate_separation {rates : ℕ → ℝ≥0} {d : ℕ}
    {T : PositiveTime} {δ : ℝ} (Q : TailSpikes.RateFamily rates d T δ)
    (a : Assignments Q.coordinates) {h f : (dyadicSystem K rates).IntrinsicSpace}
    (hh : h ∈ (intrinsicExpectation K rates d).range)
    (hf : f ∈ (intrinsicExpectation K rates d).range) (n : ℕ) :
    (1 - 2 * δ) * (‖coord (dyadicSystem K rates).analysis n h‖ +
        ‖coord (dyadicSystem K rates).analysis n f‖) ≤
      ‖coord (dyadicSystem K rates).analysis n h +
        multiplier K (Q.q a) (coord (dyadicSystem K rates).analysis n f)‖ := by
  obtain ⟨H, hH, hHeq⟩ := continuousRepresentative_coord_of_range rates d n hh
  obtain ⟨F, hF, hFeq⟩ := continuousRepresentative_coord_of_range rates d n hf
  rw [← hHeq, ← hFeq]
  exact HeadTail.concentration_multiplier_toLp Q.beyond_prefix.symm H F (Q.q a)
    hH hF (Q.q_depends a) (ae_of_all _ (Q.nonnegative a)) (Q.integral_one a)
    (Q.B a) (Q.measurable a) δ (Q.small a).le (Q.concentrated a).le

theorem coordinate_commutator {rates : ℕ → ℝ≥0} {d : ℕ}
    {T : PositiveTime} {δ : ℝ} (Q : TailSpikes.RateFamily rates d T δ)
    (a : Assignments Q.coordinates) {f : (dyadicSystem K rates).IntrinsicSpace}
    (hf : f ∈ (intrinsicExpectation K rates d).range) :
    ∀ n, ‖(dyadicSystem K rates).analysis n
          (multiplier K (Q.q a) (evalZero (dyadicSystem K rates).analysis f)) -
        multiplier K (Q.q a) (coord (dyadicSystem K rates).analysis n f)‖ ≤
      IntrinsicSpikes.error T ‖evalZero (dyadicSystem K rates).analysis f‖ n := by
  apply IntrinsicSpikes.coordinate_commutator_le rates (multiplier K (Q.q a)) f T
  obtain ⟨F, hF, hFeq⟩ := continuousRepresentative_evalZero_of_range rates d hf
  intro t
  rw [← hFeq]
  exact Q.norm_id_sub_resolvent_commutator_le a F hF t

/-- The actual products have exact finite average, the manuscript's norm bound,
and its separation estimate, without residual analytic assumptions. -/
theorem exists_products {rates : ℕ → ℝ≥0} {d : ℕ}
    {T : PositiveTime} {δ : ℝ} (Q : TailSpikes.RateFamily rates d T δ)
    (h f : (dyadicSystem K rates).IntrinsicSpace)
    (hh : h ∈ (intrinsicExpectation K rates d).range)
    (hf : f ∈ (intrinsicExpectation K rates d).range) :
    ∃ g : Assignments Q.coordinates → (dyadicSystem K rates).IntrinsicSpace,
      (∀ a, evalZero (dyadicSystem K rates).analysis (g a) =
        multiplier K (Q.q a) (evalZero (dyadicSystem K rates).analysis f)) ∧
      (Fintype.card (Assignments Q.coordinates) : K)⁻¹ • (∑ a, g a) = f ∧
      (∀ a, |‖g a‖ - ‖f‖| ≤
        IntrinsicSpikes.eta T * ‖evalZero (dyadicSystem K rates).analysis f‖) ∧
      (∀ a, (1 - 2 * δ) * (‖h‖ + ‖f‖) -
        IntrinsicSpikes.eta T * ‖evalZero (dyadicSystem K rates).analysis f‖ ≤ ‖h + g a‖) := by
  have hex (a : Assignments Q.coordinates) := IntrinsicSpikes.exists_product rates
    (multiplier K (Q.q a)) f T (coordinate_norm_preserved Q a hf)
    (coordinate_commutator Q a hf)
  choose g hge hgn using hex
  refine ⟨g, hge, ?_, hgn, ?_⟩
  · have havg := IntrinsicSpikeAverages.average_products K Q (dyadicSystem K rates).analysis f g hge
    have hsmul : (Fintype.card (Assignments Q.coordinates) : ℝ)⁻¹ • (∑ a, g a) =
        (((Fintype.card (Assignments Q.coordinates) : ℝ)⁻¹ : ℝ) : K) • (∑ a, g a) := by
      apply Subtype.ext
      change (Fintype.card (Assignments Q.coordinates) : ℝ)⁻¹ •
          ((∑ a, g a : (dyadicSystem K rates).IntrinsicSpace) : Ambient (Y := Lp K 1 haar)) =
        (((Fintype.card (Assignments Q.coordinates) : ℝ)⁻¹ : ℝ) : K) •
          ((∑ a, g a : (dyadicSystem K rates).IntrinsicSpace) : Ambient (Y := Lp K 1 haar))
      exact RCLike.real_smul_eq_coe_smul (K := K) _ _
    rw [hsmul] at havg
    simpa only [RCLike.ofReal_inv, RCLike.ofReal_natCast] using havg
  · intro a
    exact IntrinsicSpikes.separation rates (multiplier K (Q.q a)) h f (g a) (hge a) T δ
      (coordinate_separation Q a hh hf) (coordinate_commutator Q a hf)

/-- Existence of genuine tail families supplies exactly the finite-family
criterion on the original finite-coordinate intrinsic ranges. -/
theorem finiteSpikeFamilies (rates : ℕ → ℝ≥0)
    (hQ : ∀ (d : ℕ) (T : PositiveTime) (δ : ℝ), 0 < δ →
      Nonempty (TailSpikes.RateFamily rates d T δ)) :
    Daugavet.FiniteSpikeFamilies K (dyadicSystem K rates).IntrinsicSpace
      (fun n => (intrinsicExpectation K rates n).range) := by
  classical
  intro d h hh f hf δ hδ η hη
  obtain ⟨T, hT⟩ := IntrinsicSpikes.exists_eta_lt hη
  obtain ⟨Q⟩ := hQ d T δ hδ
  obtain ⟨g, hge, havg, hgn, hgs⟩ := exists_products Q h f hh hf
  let e := Fintype.equivFin (Assignments Q.coordinates)
  refine ⟨Fintype.card (Assignments Q.coordinates), Fintype.card_pos, fun i => g (e.symm i),
    ?_, ?_, ?_⟩
  · rw [e.symm.sum_comp]
    exact havg
  · intro a
    have he : IntrinsicSpikes.eta T * ‖evalZero (dyadicSystem K rates).analysis f‖ ≤
        η * ‖f‖ := mul_le_mul hT.le (norm_evalZero_le _ _) (norm_nonneg _) hη.le
    have hn := (abs_le.mp (hgn (e.symm a))).2
    nlinarith
  · intro a
    have he : IntrinsicSpikes.eta T * ‖evalZero (dyadicSystem K rates).analysis f‖ ≤
        η * ‖f‖ := mul_le_mul hT.le (norm_evalZero_le _ _) (norm_nonneg _) hη.le
    linarith [hgs (e.symm a)]

end PL1.IntrinsicSpikeFamilies
