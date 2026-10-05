import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.Pi

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

namespace Posets

/-- A biorthogonal family permits arbitrary prescribed functional values, while
the resulting functional still vanishes on the common kernel of the coordinates.
The extension is algebraic; no continuity is asserted. -/
theorem exists_linearMap_of_biorthogonal
    {𝕜 E ι : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (F : ι → E →ₗ[𝕜] 𝕜) (v : ι → E)
    (hF : ∀ n m, F n (v m) = if m = n then 1 else 0) (c : ι → 𝕜) :
    ∃ L : E →ₗ[𝕜] 𝕜,
      (∀ n, L (v n) = c n) ∧ (∀ x, (∀ n, F n x = 0) → L x = 0) := by
  classical
  let inclusion : (ι →₀ 𝕜) →ₗ[𝕜] (ι → 𝕜) := Finsupp.lcoeFun
  have hinj : Function.Injective inclusion := by
    intro a b h
    ext n
    exact congrFun h n
  obtain ⟨retraction, hret⟩ := inclusion.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let coordinates : E →ₗ[𝕜] (ι → 𝕜) := LinearMap.pi F
  let weightedSum : (ι →₀ 𝕜) →ₗ[𝕜] 𝕜 := Finsupp.linearCombination 𝕜 c
  refine ⟨weightedSum.comp (retraction.comp coordinates), ?_, ?_⟩
  · intro n
    have hv : coordinates (v n) = inclusion (Finsupp.single n 1) := by
      ext m
      simp [coordinates, inclusion, hF, Finsupp.single_apply]
    have hr : retraction (inclusion (Finsupp.single n 1)) = Finsupp.single n 1 :=
      DFunLike.congr_fun hret (Finsupp.single n 1)
    change weightedSum (retraction (coordinates (v n))) = c n
    rw [hv, hr]
    simp [weightedSum]
  · intro x hx
    have hzero : coordinates x = 0 := by
      ext n
      exact hx n
    change weightedSum (retraction (coordinates x)) = 0
    rw [hzero, map_zero, map_zero]

end Posets
