import SurveyStatements.P1Geometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
Ordered basic-sequence definitions and the series obstruction used in the
boundedly complete case. Ordered convergence is used throughout: it does not
assert unconditional convergence of a series.
-/

noncomputable section

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Ordered initial partial sums of an expansion. -/
def sequencePartialSum (e : ℕ → X) (a : ℕ → ℂ) (N : ℕ) : X :=
  ∑ n ∈ Finset.range N, a n • e n

/-- The norm-closed linear span of a sequence. -/
def sequenceClosedSpan (e : ℕ → X) : Submodule ℂ X :=
  (Submodule.span ℂ (Set.range e)).topologicalClosure

/-- A basic sequence is a Schauder basis of its own closed linear span. -/
def IsBasicSequence (e : ℕ → X) : Prop :=
  ∀ x : X, x ∈ sequenceClosedSpan e →
    ∃! a : ℕ → ℂ, Tendsto (sequencePartialSum e a) atTop (𝓝 x)

/-- Boundedness of all initial partial sums, with one common bound. -/
def HasBoundedPartialSums (e : ℕ → X) (a : ℕ → ℂ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, ‖sequencePartialSum e a N‖ ≤ C

/-- Bounded completeness for an ordered basic sequence. -/
def IsBoundedlyComplete (e : ℕ → X) : Prop :=
  IsBasicSequence e ∧ ∀ a : ℕ → ℂ, HasBoundedPartialSums e a →
    ∃ x : X, Tendsto (sequencePartialSum e a) atTop (𝓝 x)

/-- Weak Cauchyness tested by every bounded complex-linear functional. -/
def IsWeakCauchySequence (e : ℕ → X) : Prop :=
  ∀ f : X →L[ℂ] ℂ, CauchySeq (fun n => f (e n))

/-- Source strongly summing definition, with ordered scalar partial sums. -/
def IsStronglySumming (e : ℕ → X) : Prop :=
  IsBasicSequence e ∧ IsWeakCauchySequence e ∧
    ∀ a : ℕ → ℂ, HasBoundedPartialSums e a →
      ∃ c : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 c)

/-- The equivalent tail-initial formulation in the source definition. -/
def IsAsymptoticallyMonotone (e : ℕ → X) : Prop :=
  IsBasicSequence e ∧ (∀ n, ‖e n‖ = 1) ∧
    ∀ γ : ℝ, 0 < γ → ∃ N : ℕ,
      ∀ p q r : ℕ, N ≤ p → p ≤ q → q ≤ r → ∀ a : ℕ → ℂ,
        ‖∑ i ∈ Finset.Icc p q, a i • e i‖ ≤
          (1 + γ) * ‖∑ i ∈ Finset.Icc p r, a i • e i‖

/-- A flat block may have gaps in its finite support, as the source specifies. -/
def IsFlatBlock (e : ℕ → X) (d : X) : Prop :=
  d ≠ 0 ∧ ∃ F : Finset ℕ, F.Nonempty ∧ ∃ a : ℕ → ℂ,
    (∀ i ∈ F, a i ∈ unitScalars) ∧ d = ∑ i ∈ F, a i • e i

/-- The source's η-flat unit block. Its customary parameter range `0 < η < 1`
is imposed when the property is used. -/
def IsEtaFlatUnitBlock (e : ℕ → X) (η : ℝ) (b : X) : Prop :=
  ∃ d : X, IsFlatBlock e d ∧ |‖d‖ - 1| ≤ η ∧ b = (‖d‖ : ℂ)⁻¹ • d

theorem norm_etaFlatUnitBlock {e : ℕ → X} {η : ℝ} {b : X}
    (hb : IsEtaFlatUnitBlock e η b) : ‖b‖ = 1 := by
  obtain ⟨d, hd, _, rfl⟩ := hb
  exact norm_smul_inv_norm hd.1

theorem flatBlock_mem_closedSpan {e : ℕ → X} {d : X} (hd : IsFlatBlock e d) :
    d ∈ sequenceClosedSpan e := by
  apply (Submodule.span ℂ (Set.range e)).le_topologicalClosure
  obtain ⟨_, F, _, a, _, hdEq⟩ := hd
  rw [hdEq]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem etaFlatUnitBlock_mem_closedSpan {e : ℕ → X} {η : ℝ} {b : X}
    (hb : IsEtaFlatUnitBlock e η b) : b ∈ sequenceClosedSpan e := by
  obtain ⟨d, hd, _, rfl⟩ := hb
  exact (sequenceClosedSpan e).smul_mem _ (flatBlock_mem_closedSpan hd)

/-- Ordered convergence forces each individual term to tend to zero. -/
theorem orderedSeries_terms_tendsto_zero {e : ℕ → X} {a : ℕ → ℂ} {x : X}
    (h : Tendsto (sequencePartialSum e a) atTop (𝓝 x)) :
    Tendsto (fun n => a n • e n) atTop (𝓝 0) := by
  have hnext := h.comp (tendsto_add_atTop_nat 1)
  have hdiff := hnext.sub h
  simpa [sequencePartialSum, Finset.sum_range_succ] using hdiff

/-- The norm-one phased blocks from the rapid alternative cannot form a
convergent ordered series. This is the contradiction in the source's
boundedly complete case. -/
theorem phasedSeries_not_convergent {e : ℕ → X} {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ unitScalars)
    (he : Tendsto (fun n => ‖e n‖) atTop (𝓝 1)) :
    ¬ ∃ x : X, Tendsto (sequencePartialSum e a) atTop (𝓝 x) := by
  rintro ⟨x, hx⟩
  have hnorm := (orderedSeries_terms_tendsto_zero hx).norm
  have hnorm' : Tendsto (fun n => ‖e n‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_unit_smul (ha _), norm_zero] using hnorm
  have hfalse : (0 : ℝ) = 1 := tendsto_nhds_unique hnorm' he
  norm_num at hfalse

theorem boundedlyComplete_phased_obstruction {e : ℕ → X} (he : IsBoundedlyComplete e)
    {a : ℕ → ℂ} (ha : ∀ n, a n ∈ unitScalars)
    (hnorm : Tendsto (fun n => ‖e n‖) atTop (𝓝 1)) :
    ¬ HasBoundedPartialSums e a := by
  intro hbound
  exact phasedSeries_not_convergent ha hnorm (he.2 a hbound)

/-- The final scalar-series consequence used in the source's strongly summing
case: bounded vector partial sums force coefficients to tend to zero. -/
theorem stronglySumming_coefficients_tendsto_zero {e : ℕ → X}
    (he : IsStronglySumming e) {a : ℕ → ℂ} (hbound : HasBoundedPartialSums e a) :
    Tendsto a atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := he.2.2 a hbound
  have hnext := hc.comp (tendsto_add_atTop_nat 1)
  have hdiff := hnext.sub hc
  simpa [Finset.sum_range_succ] using hdiff

end SurveyStatements.P1
