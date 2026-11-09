import SurveyStatements.P1StronglySummingPreparation

/-! The scalar limits of an actual weak-Cauchy sequence determine a bounded
bidual functional. Nontrivial weak Cauchyness means this functional is
outside the canonical image of the original space. -/

/- The limit-functional construction adapts the dependency-free argument in
ThesisCommon/Analysis/BoundedWeakCauchyBidual.lean. Provenance is recorded in
verification/P1-weak-cauchy-bidual-provenance.json. All dependencies used here
are checked survey helpers and mathlib. -/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def weakCauchyScalarLimit (s : ℕ → X) (hs : IsWeakCauchySequence s)
    (f : X →L[ℂ] ℂ) : ℂ := (cauchySeq_tendsto_of_complete (hs f)).choose

theorem weakCauchyScalarLimit_tendsto (s : ℕ → X) (hs : IsWeakCauchySequence s)
    (f : X →L[ℂ] ℂ) :
    Tendsto (fun n => f (s n)) atTop (𝓝 (weakCauchyScalarLimit s hs f)) :=
  (cauchySeq_tendsto_of_complete (hs f)).choose_spec

def weakCauchyLimitLinear (s : ℕ → X) (hs : IsWeakCauchySequence s) :
    (X →L[ℂ] ℂ) →ₗ[ℂ] ℂ where
  toFun := weakCauchyScalarLimit s hs
  map_add' f g := tendsto_nhds_unique (weakCauchyScalarLimit_tendsto s hs (f + g))
    ((weakCauchyScalarLimit_tendsto s hs f).add (weakCauchyScalarLimit_tendsto s hs g))
  map_smul' z f := tendsto_nhds_unique (weakCauchyScalarLimit_tendsto s hs (z • f))
    (tendsto_const_nhds.smul (weakCauchyScalarLimit_tendsto s hs f))

theorem weakCauchyScalarLimit_norm_le (s : ℕ → X) (hs : IsWeakCauchySequence s)
    {M : ℝ} (hM : ∀ n, ‖s n‖ ≤ M) (f : X →L[ℂ] ℂ) :
    ‖weakCauchyScalarLimit s hs f‖ ≤ M * ‖f‖ := by
  apply le_of_tendsto (weakCauchyScalarLimit_tendsto s hs f).norm
  apply Eventually.of_forall
  intro n
  exact ((f.le_opNorm (s n)).trans
    (mul_le_mul_of_nonneg_left (hM n) (norm_nonneg f))).trans_eq (mul_comm _ _)

def weakCauchyLimitBidual (s : ℕ → X) (hs : IsWeakCauchySequence s) :
    (X →L[ℂ] ℂ) →L[ℂ] ℂ :=
  (weakCauchyLimitLinear s hs).mkContinuous (weakCauchy_norm_bounded hs).choose
    (weakCauchyScalarLimit_norm_le s hs (weakCauchy_norm_bounded hs).choose_spec)

theorem weakCauchyLimitBidual_tendsto (s : ℕ → X) (hs : IsWeakCauchySequence s)
    (f : X →L[ℂ] ℂ) :
    Tendsto (fun n => f (s n)) atTop (𝓝 (weakCauchyLimitBidual s hs f)) :=
  weakCauchyScalarLimit_tendsto s hs f

theorem weakCauchy_weakly_convergent_iff_bidual_mem_range (s : ℕ → X)
    (hs : IsWeakCauchySequence s) :
    (∃ x : X, ∀ f : X →L[ℂ] ℂ,
      Tendsto (fun n => f (s n)) atTop (𝓝 (f x))) ↔
        weakCauchyLimitBidual s hs ∈ Set.range (NormedSpace.inclusionInDoubleDual ℂ X) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    ext f
    exact (tendsto_nhds_unique (weakCauchyLimitBidual_tendsto s hs f) (hx f)).symm
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro f
    have h := weakCauchyLimitBidual_tendsto s hs f
    rw [← hx] at h
    exact h

end SurveyStatements.P1
