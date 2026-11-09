import PL1.WeakSchur
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The canonical weakly null sequence in `Ell2`

The Schur obstruction below tests the full continuous dual. Fréchet–Riesz
representation reduces this to convergence of the coordinates of a square
summable vector; the canonical unit vectors keep norm one.
-/

noncomputable section

open Filter
open scoped Topology

namespace PL1

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The `n`th canonical unit vector in the genuine scalar square-summable space. -/
def ell2UnitVector (n : ℕ) : Ell2 𝕜 :=
  lp.single 2 n (1 : 𝕜)

@[simp]
theorem norm_ell2UnitVector (n : ℕ) : ‖ell2UnitVector 𝕜 n‖ = 1 := by
  rw [ell2UnitVector, lp.norm_single (by norm_num)]
  exact norm_one

/-- Every square-summable scalar sequence converges to zero. -/
theorem ell2_coordinates_tendsto_zero (x : Ell2 𝕜) :
    Tendsto (fun n : ℕ => x n) atTop (𝓝 0) := by
  have hsq : Summable (fun n : ℕ => ‖x n‖ ^ (2 : ℕ)) := by
    simpa using (lp.memℓp x).summable (by norm_num)
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq.tendsto_atTop_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

/-- The canonical unit vectors are weakly null against every continuous linear
functional, over either real or complex scalars. -/
theorem ell2UnitVector_weaklyConverges_zero :
    WeaklyConverges 𝕜 (Ell2 𝕜) (ell2UnitVector 𝕜) 0 := by
  intro φ
  let x := (InnerProductSpace.toDual 𝕜 (Ell2 𝕜)).symm φ
  have hx := ell2_coordinates_tendsto_zero 𝕜 x
  have hconj := hx.star
  simp only [star_zero] at hconj
  simp only [map_zero]
  convert hconj using 1
  ext n
  rw [← InnerProductSpace.toDual_symm_apply]
  change inner 𝕜 x (lp.single 2 n (1 : 𝕜)) = star (x n)
  rw [lp.inner_single_right]
  simp

/-- The standard scalar `ℓ₂` space fails the Schur property. -/
theorem ell2_not_hasSchurProperty : ¬ HasSchurProperty 𝕜 (Ell2 𝕜) := by
  intro h
  have hv := h (ell2UnitVector 𝕜) 0 (ell2UnitVector_weaklyConverges_zero 𝕜)
  have hn := (tendsto_zero_iff_norm_tendsto_zero.mp hv)
  have hconstant : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [norm_ell2UnitVector] using hn
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hconstant)

/-- The Hilbert-space copy required in Theorem B already forces its ambient
range to fail the Schur property. -/
theorem not_hasSchurProperty_of_contains_ell2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hcopy : ContainsIsomorphicCopy 𝕜 (Ell2 𝕜) E) :
    ¬ HasSchurProperty 𝕜 E := by
  intro h
  exact ell2_not_hasSchurProperty 𝕜 (h.of_containsIsomorphicCopy hcopy)

end PL1
