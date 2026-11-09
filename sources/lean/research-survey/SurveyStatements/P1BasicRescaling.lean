import SurveyStatements.P1BasicCriterion

/-! Pointwise rescaling of an ordered basic sequence by nonzero scalars.
No uniform bound on the scalar factors is needed for this basis property. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem sequenceClosedSpan_smul_nonzero (e : ℕ → X) (a : ℕ → ℂ)
    (ha : ∀ n, a n ≠ 0) :
    sequenceClosedSpan (fun n => a n • e n) = sequenceClosedSpan e := by
  have hspan : Submodule.span ℂ (Set.range (fun n => a n • e n)) =
      Submodule.span ℂ (Set.range e) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      have hmem := (Submodule.span ℂ (Set.range (fun n => a n • e n))).smul_mem
        (a n)⁻¹ (Submodule.subset_span ⟨n, rfl⟩)
      simpa only [smul_smul, inv_mul_cancel₀ (ha n), one_smul] using hmem
  unfold sequenceClosedSpan
  rw [hspan]

theorem sequencePartialSum_smul (e : ℕ → X) (a b : ℕ → ℂ) (N : ℕ) :
    sequencePartialSum (fun n => a n • e n) b N =
      sequencePartialSum e (fun n => b n * a n) N := by
  simp only [sequencePartialSum, smul_smul]

theorem basicSequence_smul_nonzero {e : ℕ → X} (he : IsBasicSequence e)
    (a : ℕ → ℂ) (ha : ∀ n, a n ≠ 0) :
    IsBasicSequence (fun n => a n • e n) := by
  intro x hx
  rw [sequenceClosedSpan_smul_nonzero e a ha] at hx
  obtain ⟨b, hb, hbuniq⟩ := he x hx
  refine ⟨fun n => b n / a n, ?_, ?_⟩
  · have hfun : sequencePartialSum (fun n => a n • e n) (fun n => b n / a n) =
        sequencePartialSum e b := by
      funext N
      rw [sequencePartialSum_smul]
      congr 1
      funext n
      exact div_mul_cancel₀ _ (ha n)
    change Tendsto (sequencePartialSum (fun n => a n • e n) (fun n => b n / a n))
      atTop (𝓝 x)
    rw [hfun]
    exact hb
  · intro c hc
    change Tendsto (sequencePartialSum (fun n => a n • e n) c) atTop (𝓝 x) at hc
    have hfun : sequencePartialSum (fun n => a n • e n) c =
        sequencePartialSum e (fun n => c n * a n) :=
      funext (sequencePartialSum_smul e a c)
    rw [hfun] at hc
    have hcb : (fun n => c n * a n) = b := hbuniq _ hc
    funext n
    have h := congrFun hcb n
    apply (eq_div_iff (ha n)).mpr
    exact h

end SurveyStatements.P1
