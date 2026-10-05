import Posets.OrdinalBandCompressionEstimates
import Posets.WolfeNearDiagonalFactorizationInverse

/-! Actual band factorisation by a continuous reciprocal multiplier and
the Neumann inverse. Neither separability nor complemented-subcopy machinery
is needed. The estimates may be verified only on a dense set of leaves. -/
noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [TopologicalSpace L] [CompactSpace L]

theorem ordinalBand_inverse_of_multiplier_error
    (A : C(L, 𝕜) →L[𝕜] C(L, 𝕜)) (a : C(L, 𝕜))
    {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (ha : ∀ x, d - ε ≤ ‖a x‖)
    (herr : ‖A - ContinuousLinearMap.mul 𝕜 C(L, 𝕜) a‖ ≤ 2 * ε) :
    ∃ B : C(L, 𝕜) →L[𝕜] C(L, 𝕜),
      B.comp A = ContinuousLinearMap.id 𝕜 C(L, 𝕜) ∧ ‖B‖ ≤ 1 / (d - 3 * ε) := by
  have hγ : 0 < d - ε := by linarith
  have hane (x : L) : a x ≠ 0 := norm_pos_iff.mp (hγ.trans_le (ha x))
  let b : C(L, 𝕜) := ⟨fun x => (a x)⁻¹, a.continuous.inv₀ hane⟩
  let D := ContinuousLinearMap.mul 𝕜 C(L, 𝕜) a
  let Dinv := ContinuousLinearMap.mul 𝕜 C(L, 𝕜) b
  have hb : ‖b‖ ≤ 1 / (d - ε) := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    change ‖(a x)⁻¹‖ ≤ _
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hγ (ha x)
  have hDinv : ‖Dinv‖ ≤ 1 / (d - ε) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    exact (norm_mul_le b f).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg f))
  have hinv : Dinv.comp D = ContinuousLinearMap.id 𝕜 C(L, 𝕜) := by
    ext f x
    change (a x)⁻¹ * (a x * f x) = f x
    rw [← mul_assoc, inv_mul_cancel₀ (hane x), one_mul]
  obtain ⟨B, hB, hn⟩ := wolfe_exists_left_inverse_of_approximation A D Dinv hγ
    (show 0 ≤ 2 * ε by positivity) (show 2 * ε < d - ε by linarith) hDinv hinv herr
  refine ⟨B, hB, ?_⟩
  convert hn using 1 <;> congr 1 <;> ring

theorem ordinalBand_factors_of_multiplier_error
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (J : C(L, 𝕜) →L[𝕜] JLMS.CZero 𝕜 K) (q : C(L, K)) (a : C(L, 𝕜))
    {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (ha : ∀ x, d - ε ≤ ‖a x‖)
    (herr : ‖ordinalBandCompression T J q - ContinuousLinearMap.mul 𝕜 C(L, 𝕜) a‖ ≤ 2 * ε) :
    ∃ R : JLMS.CZero 𝕜 K →L[𝕜] C(L, 𝕜),
      R.comp (T.comp J) = ContinuousLinearMap.id 𝕜 C(L, 𝕜) ∧ ‖R‖ ≤ 1 / (d - 3 * ε) := by
  obtain ⟨B, hB, hn⟩ := ordinalBand_inverse_of_multiplier_error
    (ordinalBandCompression T J q) a hε hgap ha herr
  refine ⟨B.comp (ordinalBandRead q), ?_, ?_⟩
  · simpa only [ordinalBandCompression, ContinuousLinearMap.comp_assoc] using hB
  · exact (B.opNorm_comp_le _).trans ((mul_le_mul hn (ordinalBandRead_norm_le q)
      (ordinalBandRead (𝕜 := 𝕜) q).opNorm_nonneg
      (one_div_pos.mpr (sub_pos.mpr hgap)).le).trans_eq (mul_one _))

theorem ordinalBand_factors_of_dense_estimates
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (J : C(L, 𝕜) →L[𝕜] JLMS.CZero 𝕜 K) (q : C(L, K)) (a : C(L, 𝕜))
    {S : Set L} (hS : Dense S) {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (ha : ∀ x ∈ S, d - ε ≤ ‖a x‖)
    (herr : ∀ f : C(L, 𝕜), ∀ x ∈ S,
      ‖T (J f) (q x) - a x * f x‖ ≤ 2 * ε * ‖f‖) :
    ∃ R : JLMS.CZero 𝕜 K →L[𝕜] C(L, 𝕜),
      R.comp (T.comp J) = ContinuousLinearMap.id 𝕜 C(L, 𝕜) ∧ ‖R‖ ≤ 1 / (d - 3 * ε) :=
  ordinalBand_factors_of_multiplier_error T J q a hε hgap
    (ordinalBand_lower_of_dense_leaves a hS ha)
    (ordinalBand_error_of_dense_leaves _ a hS (by positivity) herr)

theorem ordinalBand_factors_of_leaf_mass
    (M : JLMS.AtomicDualModel 𝕜 K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (J : C(L, 𝕜) →L[𝕜] JLMS.CZero 𝕜 K) (q : C(L, K))
    (H : Set K) (hH : IsClopen H) (hcH : IsCompact H)
    (hJ : ‖J‖ ≤ 1) (hsupp : ∀ f, Function.support (J f) ⊆ H)
    {S : Set L} (hS : Dense S) (V : L → Set K)
    (hVH : ∀ x ∈ S, V x ⊆ H)
    (hconst : ∀ x ∈ S, ∀ f : C(L, 𝕜), ∀ y ∈ V x, J f y = f x)
    {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (ha : ∀ x ∈ S, d - ε ≤ ‖ordinalBandTotal T q H hH hcH x‖)
    (hmass : ∀ x ∈ S, ‖JLMS.atomicRestriction M (H \ V x)
      ((JLMS.evaluation (q x)).comp T)‖ ≤ ε) :
    ∃ R : JLMS.CZero 𝕜 K →L[𝕜] C(L, 𝕜),
      R.comp (T.comp J) = ContinuousLinearMap.id 𝕜 C(L, 𝕜) ∧ ‖R‖ ≤ 1 / (d - 3 * ε) := by
  apply ordinalBand_factors_of_dense_estimates T J q (ordinalBandTotal T q H hH hcH)
    hS hε hgap ha
  intro f x hx
  exact ordinalBand_pointwise_error M T J q H hH hcH hJ hsupp x (V x)
    (hVH x hx) (hconst x hx) hε (hmass x hx) f

end Posets
