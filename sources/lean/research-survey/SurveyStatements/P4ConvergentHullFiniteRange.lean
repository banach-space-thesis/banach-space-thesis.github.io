import SurveyStatements.P4ConvergentHull
import SurveyStatements.P4ConvergentFiniteRank

/-! Actual finite-dimensional ranges of freeze maps on the closed span of
the invariant operator-generated set. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2048

open Set Filter Topology
open scoped OnePoint ENNReal

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

def convergentHullFiniteRange (R : X →L[𝕜] C(OnePoint ℕ, Y)) (m : ℕ) :
    Submodule 𝕜 C(OnePoint ℕ, Y) :=
  ⨆ k : Fin (m + 1), LinearMap.range ((convergentFreeze (𝕜 := 𝕜) (Y := Y) k.val).comp R).toLinearMap

lemma convergentHullFiniteRange_finiteDimensional (R : X →L[𝕜] C(OnePoint ℕ, Y))
    (hfinite : ∀ n, HasFiniteRank 𝕜 ((convergentFreeze (𝕜 := 𝕜) (Y := Y) n).comp R)) (m : ℕ) :
    FiniteDimensional 𝕜 (convergentHullFiniteRange R m) := by
  letI (k : Fin (m + 1)) :
      FiniteDimensional 𝕜 (LinearMap.range ((convergentFreeze (𝕜 := 𝕜) (Y := Y) k.val).comp R).toLinearMap) :=
    hfinite k.val
  exact Submodule.finiteDimensional_iSup _

lemma convergentFreezeSum_mem_finiteRange (R : X →L[𝕜] C(OnePoint ℕ, Y))
    (hfinite : ∀ n, HasFiniteRank 𝕜 ((convergentFreeze (𝕜 := 𝕜) (Y := Y) n).comp R)) (m : ℕ)
    (x : lp (fun _ : ℕ => X) 1) :
    convergentFreeze (𝕜 := 𝕜) (Y := Y) m (convergentFreezeSum R x) ∈ convergentHullFiniteRange R m := by
  let F := convergentHullFiniteRange R m
  letI : FiniteDimensional 𝕜 F := convergentHullFiniteRange_finiteDimensional R hfinite m
  have hA (n : ℕ) : ‖(convergentFreeze (𝕜 := 𝕜) (Y := Y) n).comp R‖ ≤ ‖R‖ :=
    ((convergentFreeze (𝕜 := 𝕜) (Y := Y) n).opNorm_comp_le R).trans
      ((mul_le_mul_of_nonneg_right (norm_convergentFreeze_le_one (𝕜 := 𝕜) (Y := Y) n) R.opNorm_nonneg).trans_eq
        (one_mul _))
  have hs : HasSum (fun n => (convergentFreeze (𝕜 := 𝕜) (Y := Y) n).comp R (x n)) (convergentFreezeSum R x) :=
    (lp1_operator_summable_norm _ R.opNorm_nonneg hA x).of_norm.hasSum
  apply F.closed_of_finiteDimensional.mem_of_tendsto
    (hs.map (convergentFreeze (𝕜 := 𝕜) (Y := Y) m) (convergentFreeze (𝕜 := 𝕜) (Y := Y) m).continuous)
  apply Eventually.of_forall
  intro s
  apply F.sum_mem
  intro n hn
  have hmn : min m n < m + 1 := by omega
  have hmem : (convergentFreeze (𝕜 := 𝕜) (Y := Y) (min m n)).comp R (x n) ∈ F := by
    apply (le_iSup (fun k : Fin (m + 1) =>
      LinearMap.range ((convergentFreeze (𝕜 := 𝕜) (Y := Y) k.val).comp R).toLinearMap) ⟨min m n, hmn⟩)
    exact ⟨x n, rfl⟩
  change ((convergentFreeze (𝕜 := 𝕜) (Y := Y) m).comp
    (convergentFreeze (𝕜 := 𝕜) (Y := Y) n)) (R (x n)) ∈ F
  rw [convergentFreeze_comp (𝕜 := 𝕜) (Y := Y) m n]
  exact hmem

variable [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
variable [NormedSpace ℝ Y] [IsScalarTower ℝ 𝕜 Y]

theorem convergentHull_closedSpan_finiteRange (R : X →L[𝕜] C(OnePoint ℕ, Y))
    (hfinite : ∀ n, HasFiniteRank 𝕜 ((convergentFreeze (𝕜 := 𝕜) (Y := Y) n).comp R)) (m : ℕ) :
    ∀ z ∈ closure (Submodule.span 𝕜 (operatorGaugeData (convergentFreezeSum R)).carrier : Set _),
      convergentFreeze (𝕜 := 𝕜) (Y := Y) m z ∈ convergentHullFiniteRange R m := by
  letI : FiniteDimensional 𝕜 (convergentHullFiniteRange R m) :=
    convergentHullFiniteRange_finiteDimensional R hfinite m
  exact operatorGaugeData_closedSpan_maps_into _ _ _
    (convergentHullFiniteRange R m).closed_of_finiteDimensional
    (convergentFreezeSum_mem_finiteRange R hfinite m)

end SurveyStatements.P4
