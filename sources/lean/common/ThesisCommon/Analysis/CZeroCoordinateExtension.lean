import ThesisCommon.Analysis.CZeroSingles
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! Genuine Hahn–Banach extensions of the inverse coordinates of a
bounded-below c₀ operator, with the exact reciprocal lower-bound constant. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_cZero_coordinate_extensions (J : CZeroSum 𝕜 →L[𝕜] E)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c*‖x‖ ≤ ‖J x‖) :
    ∃ φ : ℕ → E →L[𝕜] 𝕜, (∀ n, ‖φ n‖ ≤ 1/c) ∧
      ∀ n x, φ n (J x) = x n := by
  classical
  have hinj : Function.Injective J := by
    intro x y hxy
    have h := hlower (x-y)
    simp only [map_sub, hxy, sub_self, norm_zero] at h
    have hz : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  let e := LinearEquiv.ofInjective J.toLinearMap hinj
  have hbound (x : LinearMap.range J) : ‖e.symm x‖ ≤ (1/c)*‖x‖ := by
    have h := hlower (e.symm x)
    have he : J (e.symm x) = (x:E) := congrArg Subtype.val (e.apply_symm_apply x)
    rw [he] at h
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using h)
  let L : LinearMap.range J →L[𝕜] CZeroSum 𝕜 :=
    e.symm.toLinearMap.mkContinuous (1/c) hbound
  have hL (x : CZeroSum 𝕜) : L (e x) = x := e.symm_apply_apply x
  have hcoord (n : ℕ) : ‖(cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n).comp L‖ ≤ 1/c := by
    apply ContinuousLinearMap.opNorm_le_bound _ (one_div_pos.mpr hc).le
    intro x
    exact (BoundedContinuousFunction.norm_coe_le_norm (L x).toBCF n).trans (hbound x)
  have hex (n : ℕ) : ∃ φ : E →L[𝕜] 𝕜, ‖φ‖ ≤ 1/c ∧
      ∀ x : CZeroSum 𝕜, φ (J x) = x n := by
    obtain ⟨φ, hφ, hnφ⟩ := exists_extension_norm_eq (LinearMap.range J)
      ((cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n).comp L)
    refine ⟨φ, hnφ ▸ hcoord n, ?_⟩
    intro x
    have h := hφ (e x)
    change φ (J x) = L (e x) n at h
    simpa only [hL] using h
  choose φ hφ hφx using hex
  exact ⟨φ, hφ, hφx⟩

end ThesisCommon
