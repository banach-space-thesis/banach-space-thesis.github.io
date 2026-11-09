import PL1.LatticeDefinitions
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Definitions for Theorems A and B of the updated PL1 paper

All function and sequence spaces are standard Mathlib Lp/lp spaces. No abstract
placeholder substitutes for the actual interval L1, continuous dual, range, or
bounded inverse. RNP is given its vector-measure definition, not replaced by a
single representability test or the Schur property.
-/

noncomputable section
universe u v w

open Filter MeasureTheory Module
open scoped Topology ENNReal

namespace PL1

/-- Lebesgue measure restricted to [0,1]. Outside values are ignored modulo a.e.
equality. Mathlib's a.e.-strongly-measurable Lp construction also accommodates
completed-measure representatives. -/
def intervalMeasure : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- Genuine interval L1 with its integral norm. -/
abbrev IntervalL1 (𝕜 : Type*) [RCLike 𝕜] := Lp 𝕜 1 intervalMeasure

/-- Standard scalar square-summable sequence space over ℕ. -/
abbrev Ell2 (𝕜 : Type*) [RCLike 𝕜] := lp (fun _ : ℕ => 𝕜) 2

/-- Standard scalar absolutely summable sequence space over ℕ. -/
abbrev Ell1 (𝕜 : Type*) [RCLike 𝕜] := lp (fun _ : ℕ => 𝕜) 1

/-- Updated bound claimed in both main theorems; no optimality is asserted. -/
def projectionBound : ℝ := 4 + 3 * Real.sqrt 2

/-- The same normed additive group with its scalar action restricted to ℝ.
This makes every use of the underlying real space explicit. -/
abbrev UnderlyingReal (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :=
  RestrictScalars ℝ 𝕜 E

/-- Register scalar restriction on the explicit type alias. This uses the
original norm and restricts only the scalar action. -/
instance underlyingRealNormedSpace (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    NormedSpace ℝ (UnderlyingReal 𝕜 E) :=
  NormedSpace.restrictScalars ℝ 𝕜 E

section WeakConvergence

variable (𝕜 : Type*) [RCLike 𝕜]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Weak convergence tested against the entire continuous dual over 𝕜. -/
def WeaklyConverges (x : ℕ → E) (a : E) : Prop :=
  ∀ φ : E →L[𝕜] 𝕜, Tendsto (fun n => φ (x n)) atTop (𝓝 (φ a))

/-- Weak sequential convergence implies convergence in the given norm. -/
def HasSchurProperty : Prop :=
  ∀ (x : ℕ → E) (a : E),
    WeaklyConverges 𝕜 E x a → Tendsto x atTop (𝓝 a)

variable {𝕜 E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Dunford–Pettis OPERATOR, or completely continuous operator.
The all-convergent-sequences formulation is equivalent to the weak-null
formulation in the paper, by subtracting the limit. -/
def IsDunfordPettis (T : E →L[𝕜] F) : Prop :=
  ∀ (x : ℕ → E) (a : E),
    WeaklyConverges 𝕜 E x a →
      Tendsto (fun n => T (x n)) atTop (𝓝 (T a))

/-- Boundedness is already contained in the continuous-linear-map type. -/
def IsProjection (P : E →L[𝕜] E) : Prop := P.comp P = P

end WeakConvergence

/-- An isomorphic copy is a closed subspace and a bounded linear equivalence
onto it with bounded inverse. An injective continuous linear map alone would
not express this condition. -/
def ContainsIsomorphicCopy (𝕜 : Type*) [RCLike 𝕜]
    (D : Type*) [NormedAddCommGroup D] [NormedSpace 𝕜 D]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∃ V : Submodule 𝕜 E,
    IsClosed (V : Set E) ∧ Nonempty (D ≃L[𝕜] V)

/-- The standard vector-measure Radon–Nikodym property.

For EVERY finite measure space and EVERY countably additive vector measure of
finite total variation vanishing on measure-zero measurable sets, there is a
Bochner-integrable density giving its value on every measurable set.

The source measurable spaces range over Type v; this universe is independent
of the target space's universe. It is explicit in statement inspection.
The property uses the underlying real scalar action, as does Bochner integration;
the same definition applies to the underlying real space of a complex space.
-/
def HasRadonNikodymProperty (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Prop :=
  ∀ (Ω : Type v) (mΩ : MeasurableSpace Ω),
    letI := mΩ
    ∀ μ : Measure Ω, μ Set.univ < ∞ →
      ∀ ν : VectorMeasure Ω E, ν.variation Set.univ < ∞ →
        (∀ A : Set Ω, MeasurableSet A → μ A = 0 → ν A = 0) →
          ∃ g : Ω → E, Integrable g μ ∧
            ∀ A : Set Ω, MeasurableSet A → ν A = ∫ x in A, g x ∂μ

end PL1
