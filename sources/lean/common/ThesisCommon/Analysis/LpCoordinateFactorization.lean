import ThesisCommon.Analysis.WCGEllOneDiagonalSelection
import ThesisCommon.Analysis.FactorNormalization

/-! Coordinate factorisation on actual arbitrary-index finite-exponent ℓp
spaces. Vanishing off-diagonal entries determine the compressed operator on
all vectors by the genuine norm-convergent singleton expansion.
-/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def lpCoordinateEntry (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p) (β α : Γ) : X →L[𝕜] X :=
  ((lpCoordinate p β).comp T).comp (lp.singleContinuousLinearMap 𝕜 (fun _ : Γ => X) p α)

@[simp] theorem lpCoordinateEntry_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p) (β α : Γ) (x : X) :
    lpCoordinateEntry p T β α x = T (lp.single p α x) β := rfl

theorem lp_coordinate_diagonal_on_support (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p) (Λ : Set Γ)
    (hdiag : ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
      ((lpCoordinateProjection (𝕜 := 𝕜) p {β}).comp T).comp
        (lpCoordinateProjection (𝕜 := 𝕜) p {α}) = 0)
    (x : lp (fun _ : Γ => X) p) (hx : ∀ γ ∉ Λ, x γ = 0) {α : Γ} (hα : α ∈ Λ) :
    T x α = lpCoordinateEntry p T α α (x α) := by
  let L := (lpCoordinate (𝕜 := 𝕜) p α).comp T
  let R := (lpCoordinateEntry p T α α).comp (lpCoordinate p α)
  have hsingle (γ : Γ) : L (lp.single p γ (x γ)) = R (lp.single p γ (x γ)) := by
    change T (lp.single p γ (x γ)) α =
      lpCoordinateEntry p T α α ((lp.single p γ (x γ) : lp (fun _ : Γ => X) p) α)
    by_cases hγα : γ = α
    · subst γ
      simp
    · by_cases hγ : γ ∈ Λ
      · have hz := congrArg (fun S : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p =>
          S (lp.single p γ (x γ)) α) (hdiag γ hγ α hα hγα)
        have hz' : T (lp.single p γ (x γ)) α = 0 := by
          simpa only [ContinuousLinearMap.comp_apply, lpCoordinateProjection_singleton,
            lp.single_apply_self, ContinuousLinearMap.zero_apply, lp.coeFn_zero, Pi.zero_apply] using hz
        rw [hz', lp.single_apply_ne (E := fun _ : Γ => X) p γ (x γ) (Ne.symm hγα), map_zero]
      · simp only [hx γ hγ, lp.single_zero, map_zero, lp.coeFn_zero, Pi.zero_apply]
  have hleft := (L.continuous.tendsto x).comp (lp.hasSum_single hp x)
  have hright := (R.continuous.tendsto x).comp (lp.hasSum_single hp x)
  change Tendsto (fun F : Finset Γ => L (∑ γ ∈ F, lp.single p γ (x γ))) atTop (𝓝 (L x)) at hleft
  have heq : (fun F : Finset Γ => L (∑ γ ∈ F, lp.single p γ (x γ))) =
      (fun F : Finset Γ => R (∑ γ ∈ F, lp.single p γ (x γ))) := by
    funext F
    simp only [map_sum, hsingle]
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

theorem lpExtend_apply_of_not_mem_range (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (e : Γ ↪ Γ) (x : lp (fun _ : Γ => X) p) {γ : Γ} (hγ : γ ∉ Set.range e) :
    lpExtend (𝕜 := 𝕜) p e x γ = 0 := by
  simp [lpExtend, Function.extend_apply' _ _ _ hγ]

theorem lp_coordinate_compression (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p) (Λ : Set Γ)
    (hdiag : ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
      ((lpCoordinateProjection (𝕜 := 𝕜) p {β}).comp T).comp
        (lpCoordinateProjection (𝕜 := 𝕜) p {α}) = 0)
    (e : Γ ↪ Γ) (he : ∀ γ, e γ ∈ Λ) (x : lp (fun _ : Γ => X) p) (γ : Γ) :
    T (lpExtend (𝕜 := 𝕜) p e x) (e γ) = lpCoordinateEntry p T (e γ) (e γ) (x γ) := by
  rw [lp_coordinate_diagonal_on_support p hp T Λ hdiag (lpExtend p e x) ?_ (he γ),
    lpExtend_apply_image]
  intro δ hδ
  apply lpExtend_apply_of_not_mem_range
  rintro ⟨η, rfl⟩
  exact hδ (he η)

/-- Normalized coordinate factors assemble with the same product bound.
The compressed all-vector formula is explicit, so no matrix determination
assumption is hidden in this lemma. -/
theorem lp_factors_of_coordinate_compression (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p)
    (F : Γ → X →L[𝕜] X) (e : Γ ↪ Γ)
    (hcomp : ∀ x γ, T (lpExtend (𝕜 := 𝕜) p e x) (e γ) = F (e γ) (x γ))
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ γ, FactorsIdentityWith (F (e γ)) X C) :
    FactorsIdentityWith T (lp (fun _ : Γ => X) p) C := by
  choose U V heq hU hV using fun γ => (hF γ).normalized
  let A := lpDiagonal p U C hC hU
  let B := lpDiagonal p V 1 zero_le_one hV
  let R := lpRestrict (𝕜 := 𝕜) (X := X) p e
  let J := lpExtend (𝕜 := 𝕜) (X := X) p e
  have hnA : ‖A‖ ≤ C := norm_lpDiagonal_le _ _ _ _
  have hnB : ‖B‖ ≤ 1 := norm_lpDiagonal_le _ _ _ _
  have hnR : ‖R‖ ≤ 1 := norm_lpRestrict_le e
  have hnJ : ‖J‖ ≤ 1 := norm_lpExtend_le e
  refine ⟨A.comp R, J.comp B, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext γ
    change U γ (T (lpExtend (𝕜 := 𝕜) p e (B x)) (e γ)) = x γ
    rw [hcomp]
    exact congrArg (fun f : X →L[𝕜] X => f (x γ)) (heq γ)
  · have hAR : ‖A.comp R‖ ≤ C := calc
      _ ≤ ‖A‖ * ‖R‖ := A.opNorm_comp_le R
      _ ≤ C * 1 := mul_le_mul hnA hnR (norm_nonneg _) hC
      _ = C := mul_one _
    have hJB : ‖J.comp B‖ ≤ 1 := calc
      _ ≤ ‖J‖ * ‖B‖ := J.opNorm_comp_le B
      _ ≤ 1 * 1 := mul_le_mul hnJ hnB (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
    simpa only [mul_one] using mul_le_mul hAR hJB (norm_nonneg _) hC

end ThesisCommon
