import JFA.CZeroFactorization
import JFA.CZeroDiscreteTensor
import JFA.ProjectionCompact

/-! Actual complemented c₀ copies in the amplified space and in each of its
infinite-dimensional complemented subspaces. A norm-one retract supplies a
separable, noncompact projection, proving K(Y) is strictly below X(Y). -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Set
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

theorem amplified_exists_cZero_retract (h𝒜 : IsAlmostDisjoint 𝒜) :
    ∃ A : cZero 𝕜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜,
    ∃ B : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] cZero 𝕜,
      B.comp A = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧ ‖A‖ = 1 ∧ ‖B‖ = 1 := by
  letI := mrowka_locallyCompactSpace (𝒜 := 𝒜)
  letI := mrowka_t2Space h𝒜
  letI : Nonempty (Mrowka 𝒜) := ⟨Sum.inl 0⟩
  exact JLMS.exists_cZero_retract (amplifiedMrowka_isScattered (𝒜 := 𝒜))

theorem amplified_complemented_infinite_contains_cZero_retract (h𝒜 : IsAlmostDisjoint 𝒜)
    (W : Submodule 𝕜 (AmplifiedMrowka 𝕜 𝒜))
    (hW : IsComplemented 𝕜 (AmplifiedMrowka 𝕜 𝒜) W) (hWinf : ¬ FiniteDimensional 𝕜 W) :
    ∃ A : cZero 𝕜 →L[𝕜] W, ∃ B : W →L[𝕜] cZero 𝕜,
      B.comp A = ContinuousLinearMap.id 𝕜 (cZero 𝕜) := by
  obtain ⟨P, hP, hPW⟩ := hW
  rw [← hPW] at hWinf ⊢
  have hPc : ¬ IsCompactOperator P :=
    fun h => hWinf ((projection_compact_iff_finiteDimensional P hP).mp h)
  obtain ⟨U, V, hUV⟩ := amplified_noncompact_factors_cZero_identity h𝒜 P hPc
  refine ⟨P.rangeRestrict.comp V, U.comp (LinearMap.range P.toLinearMap).subtypeL, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun L : cZero 𝕜 →L[𝕜] cZero 𝕜 => L x) hUV

theorem amplified_exists_separable_noncompact_projection (h𝒜 : IsAlmostDisjoint 𝒜) :
    ∃ P : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜,
      P.comp P = P ∧ HasSeparableRange 𝕜 (AmplifiedMrowka 𝕜 𝒜) (AmplifiedMrowka 𝕜 𝒜) P ∧
        ¬ IsCompactOperator P := by
  obtain ⟨A, B, hBA, _, _⟩ := amplified_exists_cZero_retract (𝕜 := 𝕜) h𝒜
  have hr (x : cZero 𝕜) : B (A x) = x := congrArg (fun L => L x) hBA
  let P := A.comp B
  refine ⟨P, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro y
    change A (B (A (B y))) = A (B y)
    rw [hr]
  · letI := czero_countable_discrete_separable (𝕜 := 𝕜) (A := ℕ)
    have hA : HasSeparableRange 𝕜 (cZero 𝕜) (AmplifiedMrowka 𝕜 𝒜) A :=
      isSeparable_range A.continuous
    exact hA.comp_right B
  · intro hc
    have hci := (hc.comp_clm A).clm_comp B
    have heq : B.comp (P.comp A) = ContinuousLinearMap.id 𝕜 (cZero 𝕜) := by
      apply ContinuousLinearMap.ext
      intro x
      change B (A (B (A x))) = x
      rw [hr, hr]
    change IsCompactOperator (B.comp (P.comp A)) at hci
    rw [heq] at hci
    exact JLMS.cZero_not_finiteDimensional 𝕜 (JLMS.finiteDimensional_of_compact_identity hci)

theorem amplified_compact_strictly_below_separable (h𝒜 : IsAlmostDisjoint 𝒜) :
    compactOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) ⊂ separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) := by
  obtain ⟨P, _, hsep, hPc⟩ := amplified_exists_separable_noncompact_projection (𝕜 := 𝕜) h𝒜
  refine ssubset_iff_subset_ne.mpr ⟨compactOperators_subset_separableOperators, ?_⟩
  intro heq
  apply hPc
  change P ∈ compactOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜)
  rw [heq]
  exact hsep

end JFA
