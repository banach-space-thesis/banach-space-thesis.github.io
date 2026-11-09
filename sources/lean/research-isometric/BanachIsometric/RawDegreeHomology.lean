import BanachIsometric.RawZeroSingularHomology
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! The existing concrete rational homology quotients, indexed by their
actual degree. The degree-zero and positive constructions stay literal. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def RawDegreeHomology (X : Type*) [TopologicalSpace X] : ℕ → Type _
  | 0 => RawZeroHomology X
  | n + 1 => RawPositiveHomology X n

instance (n : ℕ) : AddCommGroup (RawDegreeHomology X n) := by
  cases n <;> unfold RawDegreeHomology <;> infer_instance

instance (n : ℕ) : Module ℚ (RawDegreeHomology X n) := by
  cases n <;> unfold RawDegreeHomology <;> infer_instance

def rawDegreeHomologyMap (f : C(X, Y)) : (n : ℕ) →
    RawDegreeHomology X n →ₗ[ℚ] RawDegreeHomology Y n
  | 0 => rawZeroHomologyMap f
  | n + 1 => rawHomologyMap f n

theorem rawDegreeHomologyMap_id (n : ℕ) :
    rawDegreeHomologyMap (ContinuousMap.id X) n = LinearMap.id := by
  cases n with
  | zero => exact rawZeroHomologyMap_id
  | succ n => exact rawHomologyMap_id n

theorem rawDegreeHomologyMap_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    rawDegreeHomologyMap (g.comp f) n =
      (rawDegreeHomologyMap g n).comp (rawDegreeHomologyMap f n) := by
  cases n with
  | zero => exact rawZeroHomologyMap_comp f g
  | succ n => exact rawHomologyMap_comp f g n

def rawDegreeHomologyHomeomorph (e : X ≃ₜ Y) (n : ℕ) :
    RawDegreeHomology X n ≃ₗ[ℚ] RawDegreeHomology Y n := by
  let f : C(X, Y) := ⟨e, e.continuous⟩
  let g : C(Y, X) := ⟨e.symm, e.symm.continuous⟩
  refine LinearEquiv.ofLinear (rawDegreeHomologyMap f n) (rawDegreeHomologyMap g n) ?_ ?_
  · rw [← rawDegreeHomologyMap_comp]
    have h : f.comp g = ContinuousMap.id Y := by
      ext y
      exact e.apply_symm_apply y
    rw [h, rawDegreeHomologyMap_id]
  · rw [← rawDegreeHomologyMap_comp]
    have h : g.comp f = ContinuousMap.id X := by
      ext x
      exact e.symm_apply_apply x
    rw [h, rawDegreeHomologyMap_id]

theorem rawDegreeHomology_subsingleton_of_isEmpty (X : Type*) [TopologicalSpace X]
    [IsEmpty X] (n : ℕ) : Subsingleton (RawDegreeHomology X n) := by
  letI (k : ℕ) : IsEmpty (RawSingularSimplex X k) :=
    ⟨fun σ => isEmptyElim (σ (stdSimplex.vertex (0 : Fin (k + 1))))⟩
  cases n with
  | zero =>
      change Subsingleton (RawRationalChains X 0 ⧸ LinearMap.range (rawBoundary (X := X) 0))
      exact (Submodule.Quotient.subsingleton_iff _).mpr fun c =>
        (Subsingleton.elim 0 c) ▸ (LinearMap.range (rawBoundary (X := X) 0)).zero_mem
  | succ n =>
      change Subsingleton (rawCycles X n ⧸ rawBoundaries X n)
      exact (Submodule.Quotient.subsingleton_iff _).mpr fun c =>
        (Subsingleton.elim 0 c) ▸ (rawBoundaries X n).zero_mem

end BanachIsometric.SingularPrism
