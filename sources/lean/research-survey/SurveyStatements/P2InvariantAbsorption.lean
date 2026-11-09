import SurveyStatements.P2Definitions
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-! A countable operator family can be absorbed into a genuine closed separable subspace. -/

noncomputable section
set_option autoImplicit false
open TopologicalSpace

namespace SurveyStatements.P2
universe v
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X]

def operatorWord (U : ℕ → BoundedOperators X) (w : List ℕ) : BoundedOperators X :=
  w.foldr (fun j T => U j * T) 1

@[simp] theorem operatorWord_nil (U : ℕ → BoundedOperators X) : operatorWord U [] = 1 := rfl

@[simp] theorem operatorWord_cons (U : ℕ → BoundedOperators X) (j : ℕ) (w : List ℕ) :
    operatorWord U (j :: w) = U j * operatorWord U w := rfl

def absorptionOrbit (U : ℕ → BoundedOperators X) (S : Set X) : Set X :=
  ⋃ w : List ℕ, operatorWord U w '' S

theorem subset_absorptionOrbit (U : ℕ → BoundedOperators X) (S : Set X) :
    S ⊆ absorptionOrbit U S := by
  intro x hx
  apply Set.mem_iUnion.mpr
  exact ⟨[], x, hx, rfl⟩

theorem absorptionOrbit_invariant (U : ℕ → BoundedOperators X) (S : Set X) (j : ℕ) :
    Set.MapsTo (U j) (absorptionOrbit U S) (absorptionOrbit U S) := by
  intro x hx
  obtain ⟨w, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨j :: w, y, hy, rfl⟩

theorem absorptionOrbit_isSeparable (U : ℕ → BoundedOperators X) (S : Set X)
    (hS : IsSeparable S) : IsSeparable (absorptionOrbit U S) :=
  IsSeparable.iUnion (fun w => hS.image (operatorWord U w).continuous)

def invariantAbsorptionSubspace (U : ℕ → BoundedOperators X) (S : Set X) : Submodule ℂ X :=
  (Submodule.span ℂ (absorptionOrbit U S)).topologicalClosure

theorem invariantAbsorptionSubspace_isClosed (U : ℕ → BoundedOperators X) (S : Set X) :
    IsClosed (invariantAbsorptionSubspace U S : Set X) :=
  Submodule.isClosed_topologicalClosure _

theorem subset_invariantAbsorptionSubspace (U : ℕ → BoundedOperators X) (S : Set X) :
    S ⊆ invariantAbsorptionSubspace U S := by
  intro x hx
  exact (Submodule.span ℂ (absorptionOrbit U S)).le_topologicalClosure
    (Submodule.subset_span (subset_absorptionOrbit U S hx))

theorem invariantAbsorptionSubspace_isSeparable (U : ℕ → BoundedOperators X)
    (S : Set X) (hS : IsSeparable S) :
    IsSeparable (invariantAbsorptionSubspace U S : Set X) := by
  exact ((absorptionOrbit_isSeparable U S hS).span (R := ℂ)).closure

theorem invariantAbsorptionSubspace_invariant (U : ℕ → BoundedOperators X)
    (S : Set X) (j : ℕ) :
    Set.MapsTo (U j) (invariantAbsorptionSubspace U S) (invariantAbsorptionSubspace U S) := by
  have hspan : Set.MapsTo (U j) (Submodule.span ℂ (absorptionOrbit U S))
      (Submodule.span ℂ (absorptionOrbit U S)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (absorptionOrbit_invariant U S j hx)
    | zero => simp
    | add x y hx hy hix hiy =>
      simpa only [map_add] using (Submodule.span ℂ (absorptionOrbit U S)).add_mem hix hiy
    | smul c x hx hix => simpa using (Submodule.span ℂ (absorptionOrbit U S)).smul_mem c hix
  exact hspan.closure (U j).continuous

end SurveyStatements.P2
