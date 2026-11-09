import SurveyStatements.P5OperatorReductionShadowExpansion
import SurveyStatements.P5OperatorReductionDisjointMoments
import SurveyStatements.P5Support.LpHaarContinuousApproximation

/-! Uniformly small second moments of actual signed Haar integral readers
on every L1 family with uniformly small restrictions. Packet subsets retain
the entire sign cube, and the estimates are uniform over all family members. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
open SurveyStatements.P5Support.Grothendieck
variable {𝕜 ι : Type*} [RCLike 𝕜]

def signedHaarPacketReader (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) (y : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) : 𝕜 :=
  ∑ k ∈ S, signedValue (θ k) (scalarHaarPacketReader (𝕜 := 𝕜) n k y)

theorem uniform_signedHaarPacketReader_second_moment_small
    (y : ι → Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) (hy : UniformSmallRestrictions y)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ i, ‖y i‖ ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin (2 ^ n)), ∀ i,
        mean (fun θ : Fin (2 ^ n) → Bool =>
          ‖signedHaarPacketReader n S θ (y i)‖ ^ 2) < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := uniform_restricted_reader_signed_variance_small
    y hy hC hbound ε hε
  obtain ⟨N, hN⟩ := ((tendsto_order.mp lpHaarDyadicRadius_tendsto).2 δ hδ).exists_forall_of_atTop
  refine ⟨N, fun n hn S i => ?_⟩
  let φ (k : Fin (2 ^ n)) : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[𝕜] 𝕜 :=
    if k ∈ S then scalarHaarPacketReader (𝕜 := 𝕜) n k else 0
  have hφ (k : Fin (2 ^ n)) : ‖φ k‖ ≤ 1 := by
    by_cases hk : k ∈ S
    · simpa only [φ, if_pos hk] using norm_scalarHaarPacketReader_le (𝕜 := 𝕜) n k
    · simp only [φ, if_neg hk, norm_zero, zero_le_one]
  have hμ (k : Fin (2 ^ n)) :
      (volume.restrict (Set.Icc (0 : ℝ) 1)) (lpHaarCell n k) ≤ ENNReal.ofReal δ := by
    rw [lpHaarCell_measure n k k.isLt]
    exact ENNReal.ofReal_le_ofReal (hN n hn).le
  have h := hsmall (2 ^ n) (fun k => lpHaarCell n k)
    (fun _ => measurableSet_Ioc)
    (fun k j hkj => lpHaarCell_disjoint_sameLevel n (fun h => hkj (Fin.ext h)))
    hμ φ hφ i
  have hmask (k : Fin (2 ^ n)) :
      restrictedFunctional (lpHaarCell n k) measurableSet_Ioc (φ k) (y i) =
        if k ∈ S then scalarHaarPacketReader (𝕜 := 𝕜) n k (y i) else 0 := by
    by_cases hk : k ∈ S
    · simp only [φ, if_pos hk]
      exact congrArg
        (fun L : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[𝕜] 𝕜 => L (y i))
        (scalarHaarPacketReader_eq_restricted (𝕜 := 𝕜) n k).symm
    · simp only [φ, if_neg hk]
      change (0 : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[𝕜] 𝕜)
        (vectorIndicatorMultiply (𝕜 := 𝕜) (lpHaarCell n k) measurableSet_Ioc (y i)) = 0
      exact ContinuousLinearMap.zero_apply _
  simpa only [hmask, sum_signed_mask_eq, signedHaarPacketReader] using h

theorem limiting_signedHaarPacketReader_second_moment_small
    (y : ℕ → Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) (hy : UniformSmallRestrictions y)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ m, ‖y m‖ ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin (2 ^ n)), ∀ a : (Fin (2 ^ n) → Bool) → 𝕜,
      (∀ θ, Tendsto (fun m => signedHaarPacketReader n S θ (y m)) atTop (𝓝 (a θ))) →
        mean (fun θ : Fin (2 ^ n) → Bool => ‖a θ‖ ^ 2) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := uniform_signedHaarPacketReader_second_moment_small
    y hy hC hbound (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn S a ha => ?_⟩
  have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin (2 ^ n) → Bool))
    (fun θ _ => (ha θ).norm.pow 2)
  have hmean : Tendsto (fun m => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖signedHaarPacketReader n S θ (y m)‖ ^ 2)) atTop
      (𝓝 (mean (fun θ : Fin (2 ^ n) → Bool => ‖a θ‖ ^ 2))) := by
    simpa only [mean] using hsum.const_mul (Fintype.card (Fin (2 ^ n) → Bool) : ℝ)⁻¹
  exact (le_of_tendsto hmean (Eventually.of_forall (fun m => (hN n hn S m).le))).trans_lt
    (half_lt_self hε)

end SurveyStatements.P5OperatorReduction
