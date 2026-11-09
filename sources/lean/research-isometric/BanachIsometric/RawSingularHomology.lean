import BanachIsometric.RawSingularChains
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Actual cycles modulo actual boundaries of the concrete rational singular
chain complex. `RawPositiveHomology X n` is homology in degree `n+1`.
This defines actual quotient modules and their induced maps, rather than
postulating a homology functor or homotopy invariance. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def rawCycles (X : Type*) [TopologicalSpace X] (n : ℕ) :
    Submodule ℚ (RawRationalChains X (n + 1)) := LinearMap.ker (rawBoundary n)

def rawBoundaryCycle (X : Type*) [TopologicalSpace X] (n : ℕ) :
    RawRationalChains X (n + 2) →ₗ[ℚ] rawCycles X n :=
  (rawBoundary (n + 1)).codRestrict (rawCycles X n)
    (fun c => LinearMap.congr_fun (rawBoundary_squared n) c)

def rawBoundaries (X : Type*) [TopologicalSpace X] (n : ℕ) : Submodule ℚ (rawCycles X n) :=
  LinearMap.range (rawBoundaryCycle X n)

def RawPositiveHomology (X : Type*) [TopologicalSpace X] (n : ℕ) : Type _ :=
  (rawCycles X n) ⧸ rawBoundaries X n

instance (X : Type*) [TopologicalSpace X] (n : ℕ) : AddCommGroup (RawPositiveHomology X n) :=
  inferInstanceAs (AddCommGroup ((rawCycles X n) ⧸ rawBoundaries X n))

instance (X : Type*) [TopologicalSpace X] (n : ℕ) : Module ℚ (RawPositiveHomology X n) :=
  inferInstanceAs (Module ℚ ((rawCycles X n) ⧸ rawBoundaries X n))

def rawCyclesMap (f : C(X, Y)) (n : ℕ) : rawCycles X n →ₗ[ℚ] rawCycles Y n :=
  ((rawChainMap f (n + 1)).comp (rawCycles X n).subtype).codRestrict (rawCycles Y n) (by
    intro c
    change rawBoundary n (rawChainMap f (n + 1) c.val) = 0
    calc
      _ = rawChainMap f n (rawBoundary n c.val) := LinearMap.congr_fun (rawChainMap_boundary f n) c.val
      _ = 0 := by rw [c.property, map_zero])

theorem rawCyclesMap_boundaryCycle (f : C(X, Y)) (n : ℕ) (c : RawRationalChains X (n + 2)) :
    rawCyclesMap f n (rawBoundaryCycle X n c) =
      rawBoundaryCycle Y n (rawChainMap f (n + 2) c) := by
  apply Subtype.ext
  exact (LinearMap.congr_fun (rawChainMap_boundary f (n + 1)) c).symm

theorem rawCyclesMap_preserves_boundaries (f : C(X, Y)) (n : ℕ) :
    rawBoundaries X n ≤ (rawBoundaries Y n).comap (rawCyclesMap f n) := by
  rintro _ ⟨c, rfl⟩
  exact ⟨rawChainMap f (n + 2) c, (rawCyclesMap_boundaryCycle f n c).symm⟩

def rawHomologyMap (f : C(X, Y)) (n : ℕ) : RawPositiveHomology X n →ₗ[ℚ] RawPositiveHomology Y n :=
  (rawBoundaries X n).mapQ (rawBoundaries Y n) (rawCyclesMap f n)
    (rawCyclesMap_preserves_boundaries f n)

@[simp] theorem rawHomologyMap_mk (f : C(X, Y)) (n : ℕ) (c : rawCycles X n) :
    rawHomologyMap f n (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (rawCyclesMap f n c) := rfl

theorem rawChainMap_id (n : ℕ) : rawChainMap (ContinuousMap.id X) n = LinearMap.id := by
  exact Finsupp.lmapDomain_id ℚ ℚ

theorem rawChainMap_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    rawChainMap (g.comp f) n = (rawChainMap g n).comp (rawChainMap f n) :=
  Finsupp.lmapDomain_comp ℚ ℚ (fun simplex => f.comp simplex) (fun simplex => g.comp simplex)

theorem rawHomologyMap_id (n : ℕ) : rawHomologyMap (ContinuousMap.id X) n = LinearMap.id := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk (rawCyclesMap (ContinuousMap.id X) n c) = Submodule.Quotient.mk c
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun (rawChainMap_id n.succ) c.val

theorem rawHomologyMap_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    rawHomologyMap (g.comp f) n = (rawHomologyMap g n).comp (rawHomologyMap f n) := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk (rawCyclesMap (g.comp f) n c) =
      Submodule.Quotient.mk (rawCyclesMap g n (rawCyclesMap f n c))
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun (rawChainMap_comp f g (n + 1)) c.val

end BanachIsometric.SingularPrism
