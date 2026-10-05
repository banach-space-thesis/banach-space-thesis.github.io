import ThesisCommon.Analysis.SequenceCoordinates
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic.FinCases

/-! Finite increasing paths and their genuine finite ℓp difference norms.
These are the path functionals in Bird–Laustsen, Section 2.1. -/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon

/-- A finite strictly increasing path, with `length` successive differences. -/
structure JamesPath where
  length : ℕ
  index : Fin (length + 1) → ℕ
  strictMono : StrictMono index

/-- The increasing two-node path. -/
def JamesPath.two (n m : ℕ) (h : n < m) : JamesPath where
  length := 1
  index i := if i = 0 then n else m
  strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

instance : Nonempty JamesPath := ⟨JamesPath.two 0 1 Nat.zero_lt_one⟩

variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

/-- The bounded map taking successive differences along a finite path.
The target has the actual finite ℓp norm; its topology is the finite product topology. -/
def jamesPathMap (s : JamesPath) :
    CZeroSum 𝕜 →L[𝕜] PiLp p.val (fun _ : Fin s.length => 𝕜) :=
  (PiLp.continuousLinearEquiv p.val 𝕜 (fun _ : Fin s.length => 𝕜)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j =>
      cZeroCoordinate (s.index j.castSucc) - cZeroCoordinate (s.index j.succ))

@[simp] theorem jamesPathMap_apply (s : JamesPath) (x : CZeroSum 𝕜) (j : Fin s.length) :
    jamesPathMap 𝕜 p s x j = x (s.index j.castSucc) - x (s.index j.succ) := rfl

theorem jamesPath_difference_le (s : JamesPath) (x : CZeroSum 𝕜) (j : Fin s.length) :
    ‖x (s.index j.castSucc) - x (s.index j.succ)‖ ≤ ‖jamesPathMap 𝕜 p s x‖ :=
  PiLp.norm_apply_le (jamesPathMap 𝕜 p s x) j

theorem jamesPath_two_difference_le (x : CZeroSum 𝕜) (n m : ℕ) (h : n < m) :
    ‖x n - x m‖ ≤ ‖jamesPathMap 𝕜 p (JamesPath.two n m h) x‖ := by
  simpa [JamesPath.two] using
    jamesPath_difference_le 𝕜 p (JamesPath.two n m h) x (0 : Fin 1)

/-- The displayed scalar finite-path formula, for finite p. -/
theorem jamesPathMap_norm (hp : p.val ≠ ∞) (s : JamesPath) (x : CZeroSum 𝕜) :
    ‖jamesPathMap 𝕜 p s x‖ =
      (∑ j : Fin s.length,
        ‖x (s.index j.castSucc) - x (s.index j.succ)‖ ^ p.val.toReal) ^
        (1 / p.val.toReal) := by
  exact PiLp.norm_eq_sum
    (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp) _

end ThesisCommon
