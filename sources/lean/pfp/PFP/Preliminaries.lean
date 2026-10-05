import ThesisCommon.Analysis.QuantitativePrimary
import ThesisCommon.Analysis.PrimaryIdeal

/-! Statements and checked proofs for the paper's Section 2. The full printed
Proposition 2.6 is retained, and is disproved for the zero space below. -/
noncomputable section
namespace PFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Source §2, `prop:iso-invariance`: transport C-PFP with squared distortion. -/
def Proposition_2_5 (S : E ≃L[𝕜] F) (C : ℝ) : Prop :=
  HasCPFP 𝕜 F C →
    HasCPFP 𝕜 E (C * ‖S.toContinuousLinearMap‖ ^ 2 * ‖S.symm.toContinuousLinearMap‖ ^ 2)

theorem proposition_2_5 (S : E ≃L[𝕜] F) (C : ℝ) : Proposition_2_5 S C :=
  fun h => h.of_equiv_exact S

/-- Source §2, `prop:maximal-ideal-pfp`, including uniqueness. This target
deliberately has no Nontrivial assumption: that is what the manuscript prints. -/
def Proposition_2_6 (𝕜 : Type*) [RCLike 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  (HasPFP 𝕜 E ↔ ∃ J : TwoSidedIdeal (E →L[𝕜] E),
    (∀ T, T ∈ J ↔ T ∈ nonfactorSet 𝕜 E) ∧ IsCoatom J) ∧
  (HasPFP 𝕜 E → ∀ J : TwoSidedIdeal (E →L[𝕜] E),
    IsCoatom J → ∀ T, T ∈ J ↔ T ∈ nonfactorSet 𝕜 E)

/-- Corrected version, with the additional hypothesis explicitly visible. -/
theorem proposition_2_6_nontrivial [Nontrivial E] : Proposition_2_6 𝕜 E := by
  refine ⟨hasPFP_iff_maximal_nonfactor, ?_⟩
  intro h J hJ T
  rw [FactorizationRing.nonfactorIdeal_unique h hJ]
  exact FactorizationRing.mem_nonfactorIdeal h T

/-- For the zero space every operator factors the (zero) identity. Thus the
nonfactorisation set is empty, and cannot be the carrier of any ideal. -/
theorem proposition_2_6_false_on_zero [Subsingleton E] : ¬ Proposition_2_6 𝕜 E := by
  intro h
  have hp : HasPFP 𝕜 E := hasUPFP_of_subsingleton.hasPFP
  obtain ⟨J, hJ, _⟩ := h.1.mp hp
  have hn := (hJ 0).mp J.zero_mem
  exact hn ⟨0, 0, Subsingleton.elim _ _⟩

/-- Concrete real Banach counterexample, with no abstract extra hypothesis. -/
theorem proposition_2_6_counterexample : ¬ Proposition_2_6 ℝ (Fin 0 → ℝ) :=
  proposition_2_6_false_on_zero

/-- Source §5 `lem:bb-complemented-implies-factor`: S is an isomorphism on Y
onto complemented Z. We prove the stronger form which does not need Y
complemented. The factors are exactly V⁻¹ W⁻¹ P and inclusion ∘ V. -/
theorem lemma_5_3 (S : E →L[𝕜] E) (Y Z : Submodule 𝕜 E)
    (V : E ≃L[𝕜] Y) (W : Y ≃L[𝕜] Z) (hW : ∀ y : Y, (W y : E) = S y)
    (P : E →L[𝕜] Z) (hP : ∀ z : Z, P z = z) : FactorsIdentity S E :=
  factorsIdentity_of_complemented_restriction S Y Z V W hW P hP

end PFP
