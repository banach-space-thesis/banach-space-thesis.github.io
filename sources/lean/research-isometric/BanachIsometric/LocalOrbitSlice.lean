import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Lipschitz inverse coordinates for an immersion

An injective strict derivative has a continuous linear left inverse in finite
dimensions. Composing with that left inverse reduces local inversion to the
ordinary inverse function theorem. This is the quantitative inverse-coordinate
step in the explicit orbit-slice route; it does not assert that a whole orbit
is covered by the immersed patch.
-/

namespace BanachIsometric

open Filter Set
open scoped Topology NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- A genuine local inverse on the image of a finite-dimensional immersion,
with a two-point Lipschitz estimate on an ambient neighbourhood. The left
inverse of the derivative and the nonlinear inverse are constructed here. -/
theorem exists_lipschitz_inverse_of_injective_strictDerivative
    (f : E → F) (D : E →L[ℝ] F)
    (hf : HasStrictFDerivAt f D 0) (hD : Function.Injective D) :
    ∃ g : F → E, ∃ U ∈ 𝓝 (0 : E), ∃ W ∈ 𝓝 (f 0), ∃ C : ℝ≥0,
      g (f 0) = 0 ∧ LipschitzOnWith C g W ∧
      (∀ x ∈ U, g (f x) = x) ∧
      (∀ y ∈ f '' U, f (g y) = y) := by
  classical
  obtain ⟨P₀, hP₀⟩ := D.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hD)
  let P : F →L[ℝ] E := P₀.toContinuousLinearMap
  have hPD : P.comp D = ContinuousLinearMap.id ℝ E := by
    ext x
    exact LinearMap.congr_fun hP₀ x
  let q : E → E := fun x => P (f x - f 0)
  have hq0 : q 0 = 0 := by simp [q]
  have hq : HasStrictFDerivAt q
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 := by
    have h := P.hasStrictFDerivAt.comp 0 (hf.sub (hasStrictFDerivAt_const (f 0) (0 : E)))
    simpa [q, hPD] using h
  let qinv := hq.localInverse q (ContinuousLinearEquiv.refl ℝ E) 0
  let g : F → E := fun y => qinv (P (y - f 0))
  have hqi0 : qinv 0 = 0 := by
    simpa only [hq0, qinv] using hq.localInverse_apply_image
  have hg0 : g (f 0) = 0 := by simp [g, hqi0]
  have hqi : HasStrictFDerivAt qinv
      (ContinuousLinearMap.id ℝ E) 0 := by
    simpa only [hq0, qinv] using hq.to_localInverse
  have harg : HasStrictFDerivAt (fun y : F => P (y - f 0)) P (f 0) := by
    simpa using
      P.hasStrictFDerivAt.comp (f 0) ((hasStrictFDerivAt_id (f 0)).sub
        (hasStrictFDerivAt_const (f 0) (f 0)))
  have hg : HasStrictFDerivAt g P (f 0) := by
    have hqi' : HasStrictFDerivAt qinv (ContinuousLinearMap.id ℝ E) (P (f 0 - f 0)) := by
      simpa only [sub_self, map_zero] using hqi
    have h := hqi'.comp (f 0) harg
    simpa only [sub_self, map_zero, ContinuousLinearMap.id_comp, g] using h
  obtain ⟨W, hW, happrox⟩ := hg.approximates_deriv_on_nhds
    (c := 1) (Or.inr zero_lt_one)
  obtain ⟨U, hU, hUinv⟩ := Filter.eventually_iff_exists_mem.mp hq.eventually_left_inverse
  refine ⟨g, U, hU, W, hW, ‖P‖₊ + 1, hg0, ?_, ?_, ?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    exact happrox.lipschitz.dist_le_mul (⟨y, hy⟩ : W) (⟨z, hz⟩ : W)
  · intro x hx
    exact hUinv x hx
  · rintro y ⟨x, hx, rfl⟩
    exact congrArg f (hUinv x hx)

end BanachIsometric
