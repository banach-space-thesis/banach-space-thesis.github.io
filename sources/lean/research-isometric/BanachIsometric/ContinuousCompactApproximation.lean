import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Ambient globally Lipschitz approximation on an actual compact subset

Tietze extension is transported through genuine finite-dimensional real
coordinates. A compact cutoff first makes the extension uniformly continuous.
After actual smooth convolution approximation, a second copy of the cutoff
preserves the approximation on the specified compact set and ensures compact
support. Global Lipschitz regularity follows from smoothness AND compact
support, not from smoothness alone.
-/

namespace BanachIsometric

open Set Metric
open scoped Topology NNReal ContDiff

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A continuous map on an actual compact subset has uniformly close ambient
globally Lipschitz approximations, in the original source and target norms. -/
theorem exists_lipschitz_approximation_on_compact {s : Set E} (hs : IsCompact s)
    (f : C(s, F)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ∃ L : ℝ≥0, LipschitzWith L g ∧
      ∀ x : s, dist (g x.val) (f x) < ε := by
  letI : CompleteSpace F := FiniteDimensional.complete ℝ F
  let e : F ≃ₜ (Fin (Module.finrank ℝ F) → ℝ) :=
    (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv.toHomeomorph
  letI : TietzeExtension F := TietzeExtension.of_homeo e
  obtain ⟨u, hu⟩ := f.exists_restrict_eq hs.isClosed
  have hu_apply : ∀ x : s, u x.val = f x := fun x ↦ congrArg (fun v : C(s, F) ↦ v x) hu
  obtain ⟨R, hR, hsR⟩ := hs.isBounded.subset_closedBall_lt (0 : ℝ) (0 : E)
  let χ : ContDiffBump (0 : E) := ⟨R, 2 * R, hR, by linarith⟩
  have hχ : ∀ x : s, χ x.val = 1 := fun x ↦ χ.one_of_mem_closedBall (hsR x.property)
  let u₀ : E → F := fun x ↦ χ x • u x
  have hu₀ : Continuous u₀ := χ.continuous.smul u.continuous
  have hu₀compact : HasCompactSupport u₀ := χ.hasCompactSupport.smul_right
  have hu₀uniform : UniformContinuous u₀ := hu₀compact.uniformContinuous_of_continuous hu₀
  obtain ⟨v, hv, hvclose⟩ := hu₀uniform.exists_contDiff_dist_le hε
  have hgcompact : HasCompactSupport (fun x ↦ χ x • v x) := χ.hasCompactSupport.smul_right
  have hgsmooth : ContDiff ℝ ∞ (fun x ↦ χ x • v x) := χ.contDiff.smul hv
  obtain ⟨L, hgLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgcompact hgsmooth (by simp)
  refine ⟨fun x ↦ χ x • v x, L, hgLip, ?_⟩
  intro x
  simpa only [u₀, hχ x, one_smul, hu_apply x] using hvclose x.val

end

end BanachIsometric
