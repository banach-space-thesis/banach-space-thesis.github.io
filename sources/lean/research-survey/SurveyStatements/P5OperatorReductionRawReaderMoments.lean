import SurveyStatements.P5OperatorReductionSupportedHaarReaderMoments
import SurveyStatements.P5OperatorReductionBlockReaderWeights

/-! Dual-side moment bounds stated for actual raw weighted readers and
the actual parent-normalized signed block readers. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
open SurveyStatements.P5Support.Grothendieck
variable {𝕜 ι : Type*} [RCLike 𝕜]

def rawScalarPacketReader (n : ℕ) (S : Finset (Fin (2 ^ n)))
    (θ : Fin (2 ^ n) → Bool) :
    Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[𝕜] 𝕜 :=
  weightedOuterReader (𝕜 := 𝕜) (E := 𝕜) (p := 1)
    (operatorReductionRawPacketFunction n S (fun k => scalarSign (θ k)))
    (rawPacketFunction_stronglyMeasurable n S (fun k => scalarSign (θ k)))
    (norm_rawPacketFunction_le_one n S (fun k => scalarSign (θ k))
      (fun k _ => (norm_scalarSign_eq_one (θ k)).le))

theorem rawScalarPacketReader_eq_signedHaarPacketReader (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool)
    (y : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    rawScalarPacketReader (𝕜 := 𝕜) n S θ y = signedHaarPacketReader n S θ y := by
  rw [rawScalarPacketReader, rawL1PacketReader_signed_mask,
    ContinuousLinearMap.sum_apply]
  calc
    _ = ∑ k, signedValue (θ k)
        (if k ∈ S then scalarHaarPacketReader (𝕜 := 𝕜) n k y else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      cases θ k <;> by_cases hk : k ∈ S <;> simp [signedValue, hk]
    _ = _ := sum_signed_mask_eq S (fun k => scalarHaarPacketReader (𝕜 := 𝕜) n k y) θ

theorem uniform_rawScalarPacketReader_second_moment_small
    (y : ι → Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hy : UniformSmallRestrictions y)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ i, ‖y i‖ ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin (2 ^ n)), ∀ i,
        mean (fun θ : Fin (2 ^ n) → Bool =>
          ‖rawScalarPacketReader (𝕜 := 𝕜) n S θ (y i)‖ ^ 2) < ε := by
  simp_rw [rawScalarPacketReader_eq_signedHaarPacketReader]
  exact uniform_signedHaarPacketReader_second_moment_small y hy hC hbound

theorem limiting_rawScalarPacketReader_second_moment_small
    (y : ℕ → Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hy : UniformSmallRestrictions y)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ m, ‖y m‖ ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin (2 ^ n)), ∀ a : (Fin (2 ^ n) → Bool) → 𝕜,
      (∀ θ, Tendsto (fun m => rawScalarPacketReader (𝕜 := 𝕜) n S θ (y m))
        atTop (𝓝 (a θ))) →
        mean (fun θ : Fin (2 ^ n) → Bool => ‖a θ‖ ^ 2) < ε := by
  simp_rw [rawScalarPacketReader_eq_signedHaarPacketReader]
  exact limiting_signedHaarPacketReader_second_moment_small y hy hC hbound

theorem mean_signedBlockReader_sq_eq_mass_scaled (n : ℕ)
    (S : Finset (Fin (2 ^ n)))
    (y : Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖lpHaarSignedBlockReader 𝕜 ⟨1, le_rfl⟩ n S θ y‖ ^ 2) =
    ‖((volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent n S) : 𝕜)⁻¹‖ ^ 2 *
      mean (fun θ : Fin (2 ^ n) → Bool =>
        ‖rawScalarPacketReader (𝕜 := 𝕜) n S θ y‖ ^ 2) := by
  simp only [rawScalarPacketReader]
  simp_rw [lpHaarSignedBlockReader_eq_rawWeightedReader,
    ContinuousLinearMap.smul_apply, norm_smul, mul_pow]
  exact mean_mul_left _ _

theorem uniform_signedBlockReader_second_moment_small
    (y : ι → Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hy : UniformSmallRestrictions y)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ i, ‖y i‖ ≤ C)
    {m : ℝ} (hm : 0 < m) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin (2 ^ n)),
      (volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent n S) = m →
      ∀ i, mean (fun θ : Fin (2 ^ n) → Bool =>
        ‖lpHaarSignedBlockReader 𝕜 ⟨1, le_rfl⟩ n S θ (y i)‖ ^ 2) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := uniform_rawScalarPacketReader_second_moment_small
    y hy hC hbound (ε * m ^ 2) (mul_pos hε (pow_pos hm 2))
  refine ⟨N, fun n hn S hmass i => ?_⟩
  rw [mean_signedBlockReader_sq_eq_mass_scaled, hmass, norm_inv,
    RCLike.norm_ofReal, abs_of_pos hm, inv_pow]
  calc
    _ < (m ^ 2)⁻¹ * (ε * m ^ 2) :=
      mul_lt_mul_of_pos_left (hN n hn S i) (inv_pos.mpr (pow_pos hm 2))
    _ = ε * ((m ^ 2)⁻¹ * m ^ 2) := by ring
    _ = ε := by rw [inv_mul_cancel₀ (ne_of_gt (pow_pos hm 2)), mul_one]

theorem limiting_signedBlockReader_second_moment_small
    (y : ℕ → Lp 𝕜 1 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hy : UniformSmallRestrictions y)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ j, ‖y j‖ ≤ C)
    {m : ℝ} (hm : 0 < m) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset (Fin (2 ^ n)),
      (volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent n S) = m →
      ∀ a : (Fin (2 ^ n) → Bool) → 𝕜,
      (∀ θ, Tendsto (fun j => lpHaarSignedBlockReader 𝕜 ⟨1, le_rfl⟩ n S θ (y j))
        atTop (𝓝 (a θ))) →
        mean (fun θ : Fin (2 ^ n) → Bool => ‖a θ‖ ^ 2) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := uniform_signedBlockReader_second_moment_small
    y hy hC hbound hm (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn S hmass a ha => ?_⟩
  have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin (2 ^ n) → Bool))
    (fun θ _ => (ha θ).norm.pow 2)
  have hmean : Tendsto (fun j => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖lpHaarSignedBlockReader 𝕜 ⟨1, le_rfl⟩ n S θ (y j)‖ ^ 2)) atTop
      (𝓝 (mean (fun θ : Fin (2 ^ n) → Bool => ‖a θ‖ ^ 2))) := by
    simpa only [mean] using hsum.const_mul (Fintype.card (Fin (2 ^ n) → Bool) : ℝ)⁻¹
  exact (le_of_tendsto hmean
    (Eventually.of_forall (fun j => (hN n hn S hmass j).le))).trans_lt (half_lt_self hε)

end SurveyStatements.P5OperatorReduction
