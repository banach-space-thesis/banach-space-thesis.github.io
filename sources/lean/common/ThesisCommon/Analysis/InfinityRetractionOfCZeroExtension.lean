import ThesisCommon.Analysis.CZeroCoordinateExtension
import ThesisCommon.Analysis.InfinityAnnihilator
import ThesisCommon.Analysis.SupRowOperators
import ThesisCommon.Analysis.SequenceEntryAlgebra

/-! An actual ℓ∞ extension of a bounded-below c₀ map has a complemented
coordinate subcopy with the sharp reciprocal bound. The common annihilator
theorem removes the non-matrix residual exactly on an infinite support. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_infinity_retraction_of_cZero_extension
    (J : CZeroSum 𝕜 →L[𝕜] E) (W : EllInfinitySum 𝕜 →L[𝕜] E)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c*‖x‖ ≤ ‖J x‖)
    (hext : ∀ n, W (lp.single ∞ n 1) = J (cZeroSingle n 1)) :
    ∃ U : E →L[𝕜] EllInfinitySum 𝕜,
      ∃ A : EllInfinitySum 𝕜 →L[𝕜] EllInfinitySum 𝕜,
        U.comp (W.comp A) = ContinuousLinearMap.id 𝕜 (EllInfinitySum 𝕜) ∧
        ‖U‖ ≤ 1/c ∧ ‖A‖ ≤ 1 := by
  classical
  obtain ⟨φ, hφ, hφJ⟩ := exists_cZero_coordinate_extensions J hc hlower
  let R := infinityRows φ (1/c) (one_div_pos.mpr hc).le hφ
  let ψ (n : ℕ) : EllInfinitySum 𝕜 →L[𝕜] 𝕜 :=
    (φ n).comp W - lpCoordinate ∞ n
  have hψ (m n : ℕ) : ψ m (lp.single ∞ n 1) = 0 := by
    change φ m (W (lp.single ∞ n 1)) - (lp.single ∞ n (1 : 𝕜) : EllInfinitySum 𝕜) m = 0
    rw [hext, hφJ]
    simp [cZeroSingle_apply, lp.single_apply, Pi.single_apply]
  obtain ⟨M, _, hM, hz⟩ := infinity_common_annihilator ψ hψ Set.infinite_univ
  let e : ℕ ↪ ℕ := (hM.natEmbedding M).trans (Function.Embedding.subtype M)
  have he (n : ℕ) : e n ∈ M := (hM.natEmbedding M n).property
  let A := lpExtend (𝕜 := 𝕜) (X := 𝕜) ∞ e
  let U := (lpRestrict (𝕜 := 𝕜) (X := 𝕜) ∞ e).comp R
  have hzero (n : ℕ) (x : EllInfinitySum 𝕜) : ψ n (A x) = 0 := by
    apply hz n (A x)
    intro k hk
    exact lpExtend_apply_off_range e x (by rintro ⟨j, rfl⟩; exact hk (he j))
  refine ⟨U, A, ?_, ?_, norm_lpExtend_le e⟩
  · apply ContinuousLinearMap.ext
    intro x
    ext n
    have h := hzero (e n) x
    change φ (e n) (W (A x)) - A x (e n) = 0 at h
    change φ (e n) (W (A x)) = x n
    rw [sub_eq_zero] at h
    exact h.trans (lpExtend_apply_image e x n)
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (norm_lpRestrict_le e) (norm_infinityRows_le ..)
        (norm_nonneg R) zero_le_one).trans_eq (one_mul (1/c)))

end ThesisCommon
