import JLMS.CZeroTools
import JLMS.Adjoint

/-!
# Hahn–Banach extensions of c₀ coordinates

If J:c₀→X is bounded below by c>0, its inverse on the range has norm at most
1/c. Composing this inverse with each coordinate and applying Hahn–Banach
gives functionals on X with the same uniform bound and exact coordinate values.
No complementation or sequential compactness is assumed in this step.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Uniformly bounded coordinate extensions for a bounded-below c₀ embedding. -/
theorem exists_cZero_coordinateExtensions (J : cZero 𝕜 →L[𝕜] X)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ a, c * ‖a‖ ≤ ‖J a‖) :
    ∃ f : ℕ → (X →L[𝕜] 𝕜), (∀ n, ‖f n‖ ≤ 1 / c) ∧
      ∀ n a, f n (J a) = a n := by
  classical
  have hinj : Function.Injective J := by
    intro a b hab
    have h := hlower (a - b)
    simp only [map_sub, hab, sub_self, norm_zero] at h
    have hn : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  let e := LinearEquiv.ofInjective J.toLinearMap hinj
  have hbound (x : LinearMap.range J) : ‖e.symm x‖ ≤ (1 / c) * ‖x‖ := by
    have h := hlower (e.symm x)
    have he : J (e.symm x) = (x : X) := congrArg Subtype.val (e.apply_symm_apply x)
    rw [he] at h
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀ hc).mpr (by simpa [mul_comm] using h)
  let L : LinearMap.range J →L[𝕜] cZero 𝕜 :=
    e.symm.toLinearMap.mkContinuous (1 / c) hbound
  have hL (a : cZero 𝕜) : L (e a) = a := e.symm_apply_apply a
  have hcoord (n : ℕ) : ‖(evaluation (𝕜 := 𝕜) n).comp L‖ ≤ 1 / c := by
    apply ContinuousLinearMap.opNorm_le_bound _ (one_div_pos.mpr hc).le
    intro x
    exact (norm_CZero_apply_le (L x) n).trans (hbound x)
  have hex (n : ℕ) : ∃ f : X →L[𝕜] 𝕜,
      ‖f‖ ≤ 1 / c ∧ ∀ a : cZero 𝕜, f (J a) = a n := by
    obtain ⟨f, hf, hnorm⟩ := exists_extension_norm_eq (LinearMap.range J)
      ((evaluation (𝕜 := 𝕜) n).comp L)
    refine ⟨f, hnorm ▸ hcoord n, ?_⟩
    intro a
    have h := hf (e a)
    change f (J a) = evaluation n (L (e a)) at h
    simpa only [hL, evaluation_apply] using h
  choose f hf hfa using hex
  exact ⟨f, hf, hfa⟩

end JLMS
