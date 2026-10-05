import JFA.MrowkaScattered
import JFA.CompactIdeal
import JLMS.ScatteredCZeroFactorization

/-! Every noncompact operator on the actual amplified space factors the
identity of c₀. The analytic input is the kernel-checked scattered-C₀
factorisation theorem in the sibling JLMS project. Two-sided ideal stability
then puts the full algebraic c₀ factorisation ideal inside any such ideal. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Set
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]

theorem amplified_noncompact_factors_cZero_identity {𝒜 : Set (Set ℕ)}
    (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜)
    (hT : ¬ IsCompactOperator T) :
    ∃ U : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] cZero 𝕜,
    ∃ V : cZero 𝕜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜,
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) := by
  letI := mrowka_locallyCompactSpace (𝒜 := 𝒜)
  letI := mrowka_t2Space h𝒜
  have hsc := amplifiedMrowka_isScattered (𝒜 := 𝒜)
  obtain ⟨U, V, hUV, _⟩ :=
    JLMS.theorem_1_6_of_scatteredCZero (𝕜 := 𝕜) (K := ℕ × Mrowka 𝒜)
      (L := ℕ × Mrowka 𝒜) hsc hsc (JLMS.cZero_admissible hsc) T hT 1 zero_lt_one
  exact ⟨U, V, hUV⟩

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem factorizationOperators_subset_ideal_of_factors_identity
    {I : Set (E →L[𝕜] E)} (hI : IsClosedOperatorIdeal 𝕜 E I)
    {T : E →L[𝕜] E} (hT : T ∈ I)
    (U : E →L[𝕜] F) (V : F →L[𝕜] E)
    (hUV : (U.comp T).comp V = ContinuousLinearMap.id 𝕜 F) :
    factorizationOperators 𝕜 E F ⊆ I := by
  rcases hI with ⟨hc, h0, ha, hs, hm⟩
  let W : Submodule 𝕜 (E →L[𝕜] E) := {
    carrier := I
    zero_mem' := h0
    add_mem' := fun hS hQ => ha _ hS _ hQ
    smul_mem' := fun a Q hQ => hs a Q hQ }
  have hle : factorizationSpan 𝕜 E F ≤ W := by
    apply Submodule.span_le.mpr
    rintro Q ⟨A, B, rfl⟩
    have hin := (hm (V.comp A) T hT).2
    have hout := (hm (B.comp U) (T.comp (V.comp A)) hin).1
    have heq : (B.comp U).comp (T.comp (V.comp A)) = B.comp A := by
      apply ContinuousLinearMap.ext
      intro x
      have hx := congrArg (fun L : F →L[𝕜] F => L (A x)) hUV
      change U (T (V (A x))) = A x at hx
      change B (U (T (V (A x)))) = B (A x)
      rw [hx]
    exact heq ▸ hout
  exact hle

theorem amplified_ideal_contains_cZero_factorizations_of_not_subset_compact
    {𝒜 : Set (Set ℕ)} (h𝒜 : IsAlmostDisjoint 𝒜)
    {I : Set (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜)}
    (hI : IsClosedOperatorIdeal 𝕜 (AmplifiedMrowka 𝕜 𝒜) I)
    (hnot : ¬ I ⊆ compactOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜)) :
    factorizationOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) (cZero 𝕜) ⊆ I := by
  classical
  obtain ⟨T, hTI, hT⟩ := Set.not_subset.mp hnot
  obtain ⟨U, V, hUV⟩ := amplified_noncompact_factors_cZero_identity h𝒜 T hT
  exact factorizationOperators_subset_ideal_of_factors_identity hI hTI U V hUV

end JFA
