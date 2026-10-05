import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

/-! Quantitative Neumann inversion for genuine bounded operators, with the
sharp geometric-series bound, and correction of approximate factorizations. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable [CompleteSpace Z] [Nontrivial Z]

theorem exists_bounded_inverse_near_identity (F : Z →L[𝕜] Z) {r : ℝ}
    (hr : 0 ≤ r) (hrone : r < 1) (hclose : ‖ContinuousLinearMap.id 𝕜 Z - F‖ ≤ r) :
    ∃ G : Z →L[𝕜] Z, G.comp F = ContinuousLinearMap.id 𝕜 Z ∧
      F.comp G = ContinuousLinearMap.id 𝕜 Z ∧ ‖G‖ ≤ (1 - r)⁻¹ := by
  let t : Z →L[𝕜] Z := 1 - F
  have ht : ‖t‖ < 1 := hclose.trans_lt hrone
  let u := Units.oneSub t ht
  let G : Z →L[𝕜] Z := ↑u⁻¹
  have hu : (u : Z →L[𝕜] Z) = F := by
    change 1 - (1 - F) = F
    abel
  refine ⟨G, ?_, ?_, ?_⟩
  · change (↑u⁻¹ : Z →L[𝕜] Z) * F = 1
    rw [← hu]
    exact u.inv_val
  · change F * (↑u⁻¹ : Z →L[𝕜] Z) = 1
    rw [← hu]
    exact u.val_inv
  · have hgeom : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr hrone
    have hpow (n : ℕ) : ‖t ^ n‖ ≤ r ^ n :=
      (norm_pow_le t n).trans (pow_le_pow_left₀ (norm_nonneg t) hclose n)
    have hs := hgeom.of_nonneg_of_le (fun _ => norm_nonneg _) hpow
    change ‖∑' n : ℕ, t ^ n‖ ≤ (1 - r)⁻¹
    calc
      _ ≤ ∑' n, ‖t ^ n‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n : ℕ, r ^ n := hs.tsum_le_tsum hpow hgeom
      _ = (1 - r)⁻¹ := tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr])

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem exists_corrected_factorization_of_close
    (T : E →L[𝕜] F) (U : F →L[𝕜] Z) (V : Z →L[𝕜] E)
    {r : ℝ} (hr : 0 ≤ r) (hrone : r < 1) (hU : ‖U‖ ≤ 1)
    (hclose : ‖U.comp (T.comp V) - ContinuousLinearMap.id 𝕜 Z‖ ≤ r) :
    ∃ U' : F →L[𝕜] Z, U'.comp (T.comp V) = ContinuousLinearMap.id 𝕜 Z ∧
      ‖U'‖ ≤ (1 - r)⁻¹ := by
  obtain ⟨G, hG, _, hnorm⟩ := exists_bounded_inverse_near_identity (U.comp (T.comp V))
    hr hrone (by rwa [norm_sub_rev])
  refine ⟨G.comp U, ?_, ?_⟩
  · rw [ContinuousLinearMap.comp_assoc]
    exact hG
  · exact (ContinuousLinearMap.opNorm_comp_le G U).trans
      ((mul_le_of_le_one_right (norm_nonneg G) hU).trans hnorm)

end ThesisCommon
