import PL1CD.GeneratedIdeals
import PL1CD.ProjectionFamily
import PL1.DunfordPettis

noncomputable section

namespace PL1CD

variable (𝕜 : Type) [RCLike 𝕜]

def dunfordPettisIdeal : Submodule 𝕜 (L1Operator 𝕜) := PL1.dunfordPettisSubmodule

theorem dunfordPettisIdeal_isClosedTwoSided :
    IsNormClosedTwoSidedIdeal 𝕜 (dunfordPettisIdeal 𝕜) :=
  ⟨PL1.isClosed_setOf_isDunfordPettis,
    fun _T hT U => ⟨hT.comp_left U, hT.comp_right U⟩⟩

theorem dunfordPettisIdeal_isProper : IsProperOperatorIdeal 𝕜 (dunfordPettisIdeal 𝕜) := by
  intro h
  apply intervalL1_identity_not_dunfordPettis 𝕜
  change ContinuousLinearMap.id 𝕜 (PL1.IntervalL1 𝕜) ∈ dunfordPettisIdeal 𝕜
  rw [h]
  trivial

theorem generatedIdeal_le_dunfordPettis (P : ContinuumIndex → L1Operator 𝕜)
    (hP : ∀ a, PL1.HasSchurProperty 𝕜 (P a).range) (S : Set ContinuumIndex) :
    generatedIdeal 𝕜 P S ≤ dunfordPettisIdeal 𝕜 :=
  generatedIdeal_le 𝕜 P S _ (dunfordPettisIdeal_isClosedTwoSided 𝕜)
    (fun a _ => PL1.isDunfordPettis_of_hasSchurProperty_range (P a) (hP a))

theorem generatedIdeal_isProper (P : ContinuumIndex → L1Operator 𝕜)
    (hP : ∀ a, PL1.HasSchurProperty 𝕜 (P a).range) (S : Set ContinuumIndex) :
    IsProperOperatorIdeal 𝕜 (generatedIdeal 𝕜 P S) := by
  intro h
  apply dunfordPettisIdeal_isProper 𝕜
  apply top_unique
  have hle := generatedIdeal_le_dunfordPettis 𝕜 P hP S
  rwa [h] at hle

theorem generatedIdeal_additionalSpec (P : ContinuumIndex → L1Operator 𝕜)
    (hprojection : ∀ a, PL1.IsProjection (P a))
    (hschur : ∀ a, PL1.HasSchurProperty 𝕜 (P a).range)
    (hinfinite : ∀ a, ¬ FiniteDimensional 𝕜 (P a).range) :
    TheoremDAdditionalSpec 𝕜 P (generatedIdeal 𝕜 P) := by
  refine ⟨coe_generatedIdeal 𝕜 P, ?_, generatedIdeal_empty 𝕜 P, ?_⟩
  · intro S T hT
    exact generatedIdeal_le_dunfordPettis 𝕜 P hschur S hT
  · intro S hS
    obtain ⟨a, ha⟩ := hS
    exact ⟨a, ha, generator_mem_generatedIdeal 𝕜 P S ha, hprojection a, hinfinite a⟩

end PL1CD
