import Posets.WolfeNearDiagonalFactorizationEstimates
import JLMS.QuantitativeNeumann
import JLMS.CompactCZeroEquiv

/-! Quantitative correction of the actual near-diagonal operator by a
continuous reciprocal multiplier followed by the Neumann inverse. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]

theorem wolfe_exists_left_inverse_of_approximation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (A D Dinv : E →L[𝕜] E) {γ r : ℝ} (hγ : 0 < γ) (hr : 0 ≤ r) (hrγ : r < γ)
    (hDinv : ‖Dinv‖ ≤ 1 / γ) (hInvD : Dinv.comp D = ContinuousLinearMap.id 𝕜 E)
    (herror : ‖A - D‖ ≤ r) :
    ∃ B : E →L[𝕜] E, B.comp A = ContinuousLinearMap.id 𝕜 E ∧ ‖B‖ ≤ 1 / (γ - r) := by
  classical
  by_cases hE : Nontrivial E
  · letI := hE
    let F := Dinv.comp A
    have he : ContinuousLinearMap.id 𝕜 E - F = Dinv.comp (D - A) := by
      rw [ContinuousLinearMap.comp_sub, hInvD]
    have hn : ‖ContinuousLinearMap.id 𝕜 E - F‖ ≤ r / γ := by
      rw [he]
      have herror' : ‖D - A‖ ≤ r := by simpa only [norm_sub_rev] using herror
      calc
        _ ≤ ‖Dinv‖ * ‖D - A‖ := Dinv.opNorm_comp_le _
        _ ≤ (1 / γ) * r := mul_le_mul hDinv herror' (norm_nonneg _) (by positivity)
        _ = r / γ := by ring
    have hrad : r / γ < 1 := (div_lt_one hγ).mpr hrγ
    obtain ⟨G, hG, hGn⟩ := JLMS.exists_inverse_near_identity F
      (div_nonneg hr hγ.le) hrad hn
    refine ⟨G.comp Dinv, ?_, ?_⟩
    · simpa only [ContinuousLinearMap.comp_assoc] using hG
    · calc
        ‖G.comp Dinv‖ ≤ ‖G‖ * ‖Dinv‖ := G.opNorm_comp_le Dinv
        _ ≤ (1 / (1 - r / γ)) * (1 / γ) :=
          mul_le_mul hGn hDinv (norm_nonneg _) (one_div_pos.mpr (sub_pos.mpr hrad)).le
        _ = 1 / (γ - r) := by field_simp
  · haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    exact ⟨0, Subsingleton.elim _ _, by simpa using (one_div_pos.mpr (sub_pos.mpr hrγ)).le⟩

variable {L : Type*} [TopologicalSpace L] [CompactSpace L]

def wolfeCompactReciprocal (a : JLMS.CZero 𝕜 L) (ha : ∀ x, a x ≠ 0) : JLMS.CZero 𝕜 L :=
  (JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := L))
    ⟨fun x => (a x)⁻¹, a.continuous.inv₀ ha⟩

@[simp] theorem wolfeCompactReciprocal_apply (a : JLMS.CZero 𝕜 L)
    (ha : ∀ x, a x ≠ 0) (x : L) : wolfeCompactReciprocal a ha x = (a x)⁻¹ := rfl

theorem wolfeCompactReciprocal_norm_le (a : JLMS.CZero 𝕜 L)
    {γ : ℝ} (hγ : 0 < γ) (ha : ∀ x, γ ≤ ‖a x‖) :
    ‖wolfeCompactReciprocal a (fun x => norm_pos_iff.mp (hγ.trans_le (ha x)))‖ ≤ 1 / γ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  change ‖(a x)⁻¹‖ ≤ 1 / γ
  rw [norm_inv]
  simpa only [one_div] using (one_div_le_one_div_of_le hγ (ha x))

theorem wolfe_compact_multiplier_norm_le (a : JLMS.CZero 𝕜 L) :
    ‖ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 L) a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro f
  exact norm_mul_le a f

theorem wolfe_nearDiagonal_exists_left_inverse
    (M : JLMS.AtomicDualModel 𝕜 L)
    (A : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 L) {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (hdiag : ∀ x, d ≤ ‖wolfeAtomicCrossRow M A x x‖)
    (hoff : ∀ x, ‖JLMS.atomicRestriction M ({x}ᶜ)
      ((JLMS.evaluation x).comp A)‖ ≤ ε) :
    ∃ B : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 L,
      B.comp A = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L) ∧ ‖B‖ ≤ 1 / (d - 3 * ε) := by
  let a := wolfeNearDiagonalTotal A
  have hγ : 0 < d - ε := by linarith
  have ha := wolfeNearDiagonalTotal_norm_lower M A hε hdiag hoff
  let b := wolfeCompactReciprocal a (fun x => norm_pos_iff.mp (hγ.trans_le (ha x)))
  let D := ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 L) a
  let Dinv := ContinuousLinearMap.mul 𝕜 (JLMS.CZero 𝕜 L) b
  have hDinv : ‖Dinv‖ ≤ 1 / (d - ε) :=
    (wolfe_compact_multiplier_norm_le b).trans (wolfeCompactReciprocal_norm_le a hγ ha)
  have hInvD : Dinv.comp D = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L) := by
    ext f x
    change (a x)⁻¹ * (a x * f x) = f x
    rw [← mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mp (hγ.trans_le (ha x))), one_mul]
  obtain ⟨B, hB, hn⟩ := wolfe_exists_left_inverse_of_approximation A D Dinv hγ
    (show 0 ≤ 2 * ε by positivity) (show 2 * ε < d - ε by linarith)
    hDinv hInvD (wolfe_nearDiagonal_multiplier_error M A hε hoff)
  refine ⟨B, hB, ?_⟩
  convert hn using 1 <;> congr 1 <;> ring

end Posets
