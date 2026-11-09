import BanachIsometric.AffineCarrierBoundary

/-! The affine evaluation of a singular simplex is the restriction of an
actual bounded linear map on all barycentric coordinates. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def affineSimplexLinearExtension {n : ℕ} (v : Fin (n + 1) → E) :
    (Fin (n + 1) → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (v i)

theorem affineSimplexLinearExtension_apply {n : ℕ} (v : Fin (n + 1) → E)
    (w : Fin (n + 1) → ℝ) : affineSimplexLinearExtension v w = ∑ i, w i • v i := by
  simp only [affineSimplexLinearExtension, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]

theorem affineSimplexLinearExtension_inclusion {n : ℕ} (v : Fin (n + 1) → E) :
    (⟨affineSimplexLinearExtension v, (affineSimplexLinearExtension v).continuous⟩ :
      C(Fin (n + 1) → ℝ, E)).comp (affineCarrierInclusion (stdSimplex ℝ (Fin (n + 1)))) =
      affineSingularSimplex v := by
  apply ContinuousMap.ext
  intro w
  exact affineSimplexLinearExtension_apply v w.val

end BanachIsometric.SingularPrism
