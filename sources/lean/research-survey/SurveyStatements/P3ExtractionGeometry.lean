import SurveyStatements.P3Preannihilator
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Set.Countable
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.LinearAlgebra.Isomorphisms

/-! Quotient separation upgrades a continuous map satisfying the extracted
pairing identities to a linear operator over the original scalar field. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000

namespace SurveyStatements.P3

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A separable normed space has a countable dense rational vector subspace. -/
theorem exists_countable_dense_rationalSubspace [Module ℚ Y]
    [TopologicalSpace.SeparableSpace Y] :
    ∃ D : Submodule ℚ Y, Countable D ∧ Dense (D : Set Y) := by
  obtain ⟨s, hs⟩ := TopologicalSpace.exists_dense_seq Y
  refine ⟨Submodule.span ℚ (Set.range s), ?_, hs.mono Submodule.subset_span⟩
  -- This explicit proof is the countable-span argument from mathlib's
  -- `LinearAlgebra.Countable`, whose compiled module is not in the local cache.
  refine Set.countable_coe_iff.mpr (Set.Countable.mono ?_ (Set.countable_range
    (fun c : ℕ →₀ ℚ => c.sum fun i _ => c i • s i)))
  exact fun _ h => Finsupp.mem_span_range_iff_exists_finsupp.mp (SetLike.mem_coe.mp h)

/-- Finitely many linear constraints on an infinite-dimensional space leave
a vector outside any prescribed finite-dimensional subspace. -/
theorem exists_kernel_vector_outside_finite_subspace
    {V W : Type*} [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W]
    (hV : ¬ FiniteDimensional 𝕜 V) (L : V →ₗ[𝕜] W)
    (M : Submodule 𝕜 V) [FiniteDimensional 𝕜 M] :
    ∃ v : V, L v = 0 ∧ v ∉ M := by
  by_contra h
  have hker : LinearMap.ker L ≤ M := by
    intro v hv
    by_contra hvm
    exact h ⟨v, hv, hvm⟩
  letI : FiniteDimensional 𝕜 (LinearMap.ker L) :=
    Submodule.finiteDimensional_of_le hker
  letI : FiniteDimensional 𝕜 (V ⧸ LinearMap.ker L) :=
    L.quotKerEquivRange.symm.finiteDimensional
  exact hV (Module.Finite.of_submodule_quotient (LinearMap.ker L))

/-- Full scalar linearity follows from the separating family on the quotient.
This permits the extraction construction to start on a dense rational subspace
in both the real and complex cases. -/
def operatorOfPreannihilatorPairing
    (E : Submodule 𝕜 (X →L[𝕜] 𝕜)) (U : E → (Y →L[𝕜] 𝕜))
    (a : Y → X ⧸ preannihilator E) (ha : Continuous a)
    (hp : ∀ (f : E) (y : Y), preannihilatorLift E f (a y) = U f y) :
    Y →L[𝕜] (X ⧸ preannihilator E) where
  toFun := a
  map_add' y z := by
    apply sub_eq_zero.mp
    apply quotient_eq_zero_of_preannihilatorLift_eq_zero E
    intro f
    rw [map_sub, map_add, hp, hp, hp, map_add, sub_self]
  map_smul' c y := by
    apply sub_eq_zero.mp
    apply quotient_eq_zero_of_preannihilatorLift_eq_zero E
    intro f
    simp only [map_sub, map_smul, hp, RingHom.id_apply, sub_self]
  cont := ha

/-- The constructed operator has the required preadjoint identity. -/
theorem operatorOfPreannihilatorPairing_adjoint
    (E : Submodule 𝕜 (X →L[𝕜] 𝕜)) (U : E → (Y →L[𝕜] 𝕜))
    (a : Y → X ⧸ preannihilator E) (ha : Continuous a)
    (hp : ∀ (f : E) (y : Y), preannihilatorLift E f (a y) = U f y) (f : E) :
    adjoint (operatorOfPreannihilatorPairing E U a ha hp) (preannihilatorLift E f) =
      U f := by
  ext y
  exact hp f y

end SurveyStatements.P3
