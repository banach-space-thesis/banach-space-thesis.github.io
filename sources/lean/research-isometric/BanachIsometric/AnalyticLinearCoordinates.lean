import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual continuous linear changes of source and target coordinates preserve
pointwise differentiability of every order. No norms are replaced. -/

namespace BanachIsometric

theorem contDiffAt_linearCoordinates
    {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {n : WithTop ℕ∞} {f : E → F}
    (a : E ≃L[ℝ] G) (b : F ≃L[ℝ] H) (z : G)
    (hf : ContDiffAt ℝ n f (a.symm z)) :
    ContDiffAt ℝ n (fun y => b (f (a.symm y))) z := by
  have h₁ : ContDiffAt ℝ n (fun y => f (a.symm y)) z :=
    ContDiffAt.comp (f := fun y : G => a.symm y) (g := f) z hf a.symm.contDiff.contDiffAt
  exact ContDiffAt.comp (f := fun y : G => f (a.symm y)) (g := fun v : F => b v)
    z b.contDiff.contDiffAt h₁

end BanachIsometric
