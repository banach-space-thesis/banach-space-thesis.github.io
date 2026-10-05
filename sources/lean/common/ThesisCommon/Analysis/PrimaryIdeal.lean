import ThesisCommon.Analysis.Factorization
import ThesisCommon.FactorizationIdeal

/-! Operator specialisation of the factorisation-ideal argument, and the
norm-closedness argument in the proof of Proposition 2.6. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem factorsIdentity_iff_factorsOne (T : X →L[𝕜] X) :
    FactorsIdentity T X ↔ FactorizationRing.FactorsOne T := Iff.rfl

theorem hasPFP_iff_ringDichotomy :
    HasPFP 𝕜 X ↔ FactorizationRing.HasDichotomy (X →L[𝕜] X) := Iff.rfl

def nonfactorSet (𝕜 : Type*) [RCLike 𝕜] (X : Type*)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Set (X →L[𝕜] X) :=
  {T | ¬ FactorsIdentity T X}

/-- The maximal-ideal equivalence needs X ≠ {0}, a missing boundary hypothesis
in the printed Proposition 2.6. `IsCoatom` means maximal proper two-sided ideal. -/
theorem hasPFP_iff_maximal_nonfactor [Nontrivial X] :
    HasPFP 𝕜 X ↔ ∃ J : TwoSidedIdeal (X →L[𝕜] X),
      (∀ T, T ∈ J ↔ T ∈ nonfactorSet 𝕜 X) ∧ IsCoatom J :=
  FactorizationRing.dichotomy_iff_maximal_nonfactor

/-- The proof establishes closedness independently of the dichotomy. -/
theorem isClosed_nonfactorSet [CompleteSpace X] : IsClosed (nonfactorSet 𝕜 X) := by
  have hopen : IsOpen {T : X →L[𝕜] X | FactorsIdentity T X} := by
    rw [Metric.isOpen_iff]
    intro T hT
    obtain ⟨C, hC, hfact⟩ := (factorsIdentity_iff_exists_bound T).mp hT
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
    refine ⟨1 / (2 * C), by positivity, ?_⟩
    intro S hS
    apply FactorsIdentityWith.forget_bound
    apply hfact.perturb
    have hdist : ‖S - T‖ < 1 / (2 * C) := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hS
    calc
      C * ‖S - T‖ < C * (1 / (2 * C)) := mul_lt_mul_of_pos_left hdist hCpos
      _ = 1 / 2 := by field_simp
  exact hopen.isClosed_compl

end ThesisCommon
