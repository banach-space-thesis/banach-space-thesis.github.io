import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# Continuous parallelogram functions are actual real quadratic forms

This reconstructs a quadratic form on the original real module, without
turning its given auxiliary norm into the gauge or assuming a triangle
inequality for that gauge. Continuity is used only to turn additive polar
maps into real-linear maps. The parallelogram identity supplies additivity.
-/

namespace BanachIsometric

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_quadraticForm_of_continuous_parallelogram
    (q : V → ℝ) (hcont : Continuous q) (hzero : q 0 = 0)
    (hsmul : ∀ (a : ℝ) x, q (a • x) = a ^ 2 * q x)
    (hpara : ∀ x y, q (x + y) + q (x - y) = 2 * (q x + q y)) :
    ∃ Q : QuadraticForm ℝ V, ∀ x, Q x = q x := by
  let B : V → V → ℝ := fun x y => q (x + y) - q x - q y
  have hBzero (y : V) : B 0 y = 0 := by simp [B, hzero]
  have hJ (x x' y : V) : B (x + x') y + B (x - x') y = 2 * B x y := by
    have hh : q (x + x' + y) + q (x - x' + y) = 2 * (q (x + y) + q x') := by
      rw [show x + x' + y = (x + y) + x' by abel,
        show x - x' + y = (x + y) - x' by abel]
      exact hpara (x + y) x'
    dsimp [B]
    linarith [hpara x x']
  have hdouble (x y : V) : B (x + x) y = 2 * B x y := by
    have h := hJ x x y
    simpa only [sub_self, hBzero, add_zero] using h
  have hadd (x x' y : V) : B (x + x') y = B x y + B x' y := by
    have h := hJ (x + x') (x - x') y
    have hplus : x + x' + (x - x') = x + x := by module
    have hminus : x + x' - (x - x') = x' + x' := by module
    rw [hplus, hminus, hdouble, hdouble] at h
    linarith
  have hBcont (y : V) : Continuous (fun x => B x y) :=
    ((hcont.comp (continuous_id.add continuous_const)).sub hcont).sub continuous_const
  have hBsmul (a : ℝ) (x y : V) : B (a • x) y = a * B x y := by
    let f : V →+ ℝ :=
      { toFun := fun x => B x y
        map_zero' := hBzero y
        map_add' := fun x x' => hadd x x' y }
    exact map_real_smul f (hBcont y) a x
  refine ⟨QuadraticMap.ofPolar q ?_ ?_ ?_, fun _ => rfl⟩
  · intro a x
    simpa only [smul_eq_mul, pow_two] using hsmul a x
  · exact hadd
  · exact hBsmul

end BanachIsometric
