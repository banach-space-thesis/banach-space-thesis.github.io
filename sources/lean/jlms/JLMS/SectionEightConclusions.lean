import JLMS.PaperConstructions
import JLMS.CZeroRetract
import JLMS.CompleteUniqueness
import JLMS.FiniteCases

/-!
# Section 8 after discharging Rudin, the retract, and complete uniqueness

The only remaining general analytic inputs here are the cited factorization
bridge and the admissibility of C₀(K). Finite K uses its independently proved
zero-Calkin argument; infinite K uses the constructed norm-one retract.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]

/-- The complete Theorem 1.1, including complete uniqueness, after supplying
the remaining cited bridge and the original C₀(K) admissibility theorem. -/
theorem theorem_1_1_of_bridge_admissible
    (hbridge : FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := CZero 𝕜 K))
    (hX : AdmissibleCodomain 𝕜 (CZero 𝕜 K)) : Theorem_1_1 𝕜 K := by
  intro hK
  cases fintypeOrInfinite K with
  | inl hfinite => exact theorem_1_1_of_finite hK
  | inr hinfinite =>
    obtain ⟨A, B, hBA, hA, hB⟩ := exists_cZero_retract (𝕜 := 𝕜) hK
    have hminimal := essentialNormIsMinimal_of_rudin_bridge_retract
      rudinRepresentation hbridge hK hX A B hBA
    exact ⟨hminimal, hasUniqueCompleteCalkinNorm_of_minimal hminimal⟩

/-- Theorem 1.5 after supplying the remaining bridge and C₀(K) admissibility.
The norm-one retract and representation inputs are now constructed. -/
theorem theorem_1_5_of_bridge_admissible
    (hbridge : FactorizationFromDisjointFunctions (𝕜 := 𝕜) (K := K) (X := CZero 𝕜 K))
    (hX : AdmissibleCodomain 𝕜 (CZero 𝕜 K)) : Theorem_1_5 𝕜 K := by
  intro hK
  cases fintypeOrInfinite K with
  | inl hfinite => exact theorem_1_5_of_finite hK
  | inr hinfinite =>
    obtain ⟨A, B, hBA, hA, hB⟩ := exists_cZero_retract (𝕜 := 𝕜) hK
    exact bonsallMinimality_of_rudin_bridge_retract rudinRepresentation hbridge
      hK hX A B hBA hA.le hB.le

end JLMS
