import LindenstraussRetraction.BidualMap
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-!
# Second adjoints of isometric embeddings

Hahn–Banach gives norm-preserving extensions of functionals along a linear
isometry. Consequently its second adjoint is again a linear isometry. No
completeness assumption or nonzero-space assumption is needed.
-/

noncomputable section

namespace LindenstraussRetraction

universe u v s

variable {𝕜 : Type s} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

set_option synthInstance.maxSize 512

/-- Precomposition with a linear isometry is contractive on continuous duals. -/
theorem norm_transpose_isometry_le (T : E →ₗᵢ[𝕜] F) (g : StrongDual 𝕜 F) :
    ‖transpose T.toContinuousLinearMap g‖ ≤ ‖g‖ := by
  apply (transpose T.toContinuousLinearMap g).opNorm_le_bound (norm_nonneg g)
  intro x
  simpa only [transpose_apply, LinearIsometry.coe_toContinuousLinearMap, T.norm_map]
    using g.le_opNorm (T x)

/-- Hahn–Banach produces an extension of exactly the same norm along an
arbitrary linear isometric embedding. -/
theorem exists_transpose_extension_norm_eq (T : E →ₗᵢ[𝕜] F) (f : StrongDual 𝕜 E) :
    ∃ g : StrongDual 𝕜 F, transpose T.toContinuousLinearMap g = f ∧ ‖g‖ = ‖f‖ := by
  let p : Submodule 𝕜 F := LinearMap.range T.toLinearMap
  let e : E ≃ₗᵢ[𝕜] p := T.equivRange
  let fp : StrongDual 𝕜 p := f.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hnorm : ‖fp‖ = ‖f‖ := by
    apply le_antisymm
    · apply fp.opNorm_le_bound (norm_nonneg f)
      intro x
      change ‖f (e.symm x)‖ ≤ ‖f‖ * ‖x‖
      simpa only [e.symm.norm_map] using f.le_opNorm (e.symm x)
    · apply f.opNorm_le_bound (norm_nonneg fp)
      intro x
      calc
        ‖f x‖ = ‖fp (e x)‖ := by simp [fp]
        _ ≤ ‖fp‖ * ‖e x‖ := fp.le_opNorm (e x)
        _ = ‖fp‖ * ‖x‖ := by rw [e.norm_map]
  obtain ⟨g, hg, hgnorm⟩ := exists_extension_norm_eq p fp
  refine ⟨g, ?_, hgnorm.trans hnorm⟩
  ext x
  have hx := hg (e x)
  change g (T x) = f (e.symm (e x)) at hx
  change g (T x) = f x
  simpa only [e.symm_apply_apply] using hx

/-- The second adjoint of an isometric embedding preserves the norm of
every vector of the continuous bidual. -/
theorem norm_bidualMap_isometry (T : E →ₗᵢ[𝕜] F) (z : Bidual 𝕜 E) :
    ‖bidualMap T.toContinuousLinearMap z‖ = ‖z‖ := by
  apply le_antisymm
  · apply (bidualMap T.toContinuousLinearMap z).opNorm_le_bound (norm_nonneg z)
    intro g
    rw [bidualMap_apply]
    exact (z.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_transpose_isometry_le T g) (norm_nonneg z))
  · apply z.opNorm_le_bound (norm_nonneg (bidualMap T.toContinuousLinearMap z))
    intro f
    obtain ⟨g, hg, hgnorm⟩ := exists_transpose_extension_norm_eq T f
    calc
      ‖z f‖ = ‖bidualMap T.toContinuousLinearMap z g‖ := by
        rw [bidualMap_apply, hg]
      _ ≤ ‖bidualMap T.toContinuousLinearMap z‖ * ‖g‖ :=
        (bidualMap T.toContinuousLinearMap z).le_opNorm g
      _ = ‖bidualMap T.toContinuousLinearMap z‖ * ‖f‖ := by rw [hgnorm]

/-- An isometric embedding induces an isometric embedding on the bidual. -/
def bidualIsometry (T : E →ₗᵢ[𝕜] F) : Bidual 𝕜 E →ₗᵢ[𝕜] Bidual 𝕜 F :=
  { (bidualMap T.toContinuousLinearMap).toLinearMap with
    norm_map' := norm_bidualMap_isometry T }

@[simp] theorem bidualIsometry_apply (T : E →ₗᵢ[𝕜] F) (z : Bidual 𝕜 E) :
    bidualIsometry T z = bidualMap T.toContinuousLinearMap z := rfl

end LindenstraussRetraction
