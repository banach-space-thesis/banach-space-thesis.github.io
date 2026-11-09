import SurveyStatements.P3ExtractionGeometry
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! A quotient separated by an independent sequence of functionals. Using
their algebraic span suffices for the factorization argument. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000

namespace SurveyStatements.P3

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def generatedDualSpace (g : ℕ → X →L[𝕜] 𝕜) : Submodule 𝕜 (X →L[𝕜] 𝕜) :=
  Submodule.span 𝕜 (Set.range g)

def generatorInSpace (g : ℕ → X →L[𝕜] 𝕜) (i : ℕ) : generatedDualSpace g :=
  ⟨g i, Submodule.subset_span (Set.mem_range_self i)⟩

def generatorLift (g : ℕ → X →L[𝕜] 𝕜) (i : ℕ) :
    (X ⧸ preannihilator (generatedDualSpace g)) →L[𝕜] 𝕜 :=
  preannihilatorLift (generatedDualSpace g) (generatorInSpace g i)

@[simp] theorem generatorLift_apply (g : ℕ → X →L[𝕜] 𝕜) (i : ℕ) (x : X) :
    generatorLift g i (quotientMap (preannihilator (generatedDualSpace g)) x) = g i x := rfl

theorem mem_generated_preannihilator (g : ℕ → X →L[𝕜] 𝕜) (x : X) :
    x ∈ preannihilator (generatedDualSpace g) ↔ ∀ i, g i x = 0 := by
  constructor
  · intro h i
    exact (mem_preannihilator _ x).mp h (generatorInSpace g i)
  · intro h
    apply (mem_preannihilator _ x).mpr
    intro f
    have hle : generatedDualSpace g ≤
        LinearMap.ker (ContinuousLinearMap.apply 𝕜 𝕜 x) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact h i
    exact hle f.property

theorem quotient_eq_zero_of_generatorLift_eq_zero (g : ℕ → X →L[𝕜] 𝕜)
    (z : X ⧸ preannihilator (generatedDualSpace g))
    (hz : ∀ i, generatorLift g i z = 0) : z = 0 := by
  obtain ⟨x, rfl⟩ := (preannihilator (generatedDualSpace g)).mkQ_surjective z
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (mem_generated_preannihilator g x).mpr hz

theorem generatedDualSpace_infiniteDimensional (g : ℕ → X →L[𝕜] 𝕜)
    (hg : LinearIndependent 𝕜 g) : ¬ FiniteDimensional 𝕜 (generatedDualSpace g) := by
  intro hF
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional (generatedDualSpace g)).mpr hF
  have hspan : Set.range g ⊆ Submodule.span 𝕜 (s : Set (X →L[𝕜] 𝕜)) := by
    rw [hs]
    exact Submodule.subset_span
  have hfinite : Finite ℕ := LinearIndependent.finite_of_le_span_finite g hg
    (s : Set (X →L[𝕜] 𝕜)) hspan
  letI := hfinite
  exact not_finite ℕ

/-- Generator pairings suffice to recover full scalar linearity after extending
from the countable rational domain. -/
def operatorOfGeneratorPairing (g : ℕ → X →L[𝕜] 𝕜) (w : ℕ → Y →L[𝕜] 𝕜)
    (a : Y → X ⧸ preannihilator (generatedDualSpace g)) (ha : Continuous a)
    (hp : ∀ i y, generatorLift g i (a y) = w i y) :
    Y →L[𝕜] (X ⧸ preannihilator (generatedDualSpace g)) where
  toFun := a
  map_add' y z := by
    apply sub_eq_zero.mp
    apply quotient_eq_zero_of_generatorLift_eq_zero g
    intro i
    rw [map_sub, map_add, hp, hp, hp, map_add, sub_self]
  map_smul' c y := by
    apply sub_eq_zero.mp
    apply quotient_eq_zero_of_generatorLift_eq_zero g
    intro i
    simp only [map_sub, map_smul, hp, RingHom.id_apply, sub_self]
  cont := ha

/-- The independent-generator pairing needed to finish the main theorem's
hard implication. The resulting quotient is the actual preannihilator quotient. -/
theorem not_strictlyCosingular_of_generator_pairing
    (g : ℕ → X →L[𝕜] 𝕜) (hg : LinearIndependent 𝕜 g) (T : X →L[𝕜] Y)
    (A : Y →L[𝕜] (X ⧸ preannihilator (generatedDualSpace g)))
    (hp : ∀ i x, generatorLift g i (A (T x)) = g i x) :
    ¬ IsStrictlyCosingular T := by
  apply not_strictlyCosingular_of_quotient_factorization T A
    (quotientMap (preannihilator (generatedDualSpace g)))
    (preannihilator_quotient_infiniteDimensional _ (generatedDualSpace_infiniteDimensional g hg))
    (preannihilator (generatedDualSpace g)).mkQ_surjective
  ext x
  apply sub_eq_zero.mp
  apply quotient_eq_zero_of_generatorLift_eq_zero g
  intro i
  rw [map_sub, generatorLift_apply, ContinuousLinearMap.comp_apply, hp, sub_self]

end SurveyStatements.P3
