import Posets.AlspachCounterexampleLimitBound
import Posets.AlspachCounterexampleOrdinalOperator
import Posets.WolfePositiveOperator

/-! The quantitative Wolfe estimate for the actual Alspach operator.
Every positive threshold dies at a countable level strictly below ω²,
both for the probability rows and for the full adjoint unit ball. The
quantitative statement, not merely emptiness at ω², is needed for the
necessary preservation criterion quoted by Alspach. -/

noncomputable section
open Set Topology Order ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem alspachOrdinalBase_successor_derived_empty :
    ordinalDerived (univ : Set AlspachOrdinalBase) ((ω : Ordinal.{0}) + 1) = ∅ := by
  rw [Ordinal.add_one_eq_succ, ordinalDerived_succ, alspachOrdinalBase_ordinalDerived]
  exact derivedSet_eq_empty_of_finite (finite_singleton _)

theorem alspachOrdinalRows_wolfe_bound (m : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hpow : 1 < (2 : ℝ) ^ m * ε) :
    wolfeFamily (alspachOrdinalRows 𝕜).pointAtomicModel ε
      (range (alspachOrdinalRows 𝕜).weakRows)
      ((ω : Ordinal.{0}) * ((m + 1 : ℕ) : Ordinal) + 1) = ∅ :=
  alspachOmega_wolfe_bound alspachOrdinalBasePoint
    alspachOrdinalBase_successor_derived_empty m hε hpow

theorem alspachOrdinalEvaluation_wolfe_bound (m : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hpow : 1 < (2 : ℝ) ^ m * (ε / 2)) :
    wolfeFamily (alspachOrdinalRows 𝕜).pointAtomicModel ε
      (adjointUnitBall (alspachOrdinalRows 𝕜).evaluation)
      ((ω : Ordinal.{0}) * ((m + 1 : ℕ) : Ordinal) + 1) = ∅ :=
  (alspachOrdinalRows 𝕜).wolfe_evaluation_empty_of_rows (half_pos hε).le
    (half_lt_self hε) _ (alspachOrdinalRows_wolfe_bound m (half_pos hε) hpow)

theorem alspachOrdinalEvaluation_wolfe_empty_below_omega_sq {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : Ordinal.{0}, γ < ω ^ (2 : Ordinal) ∧
      wolfeFamily (alspachOrdinalRows 𝕜).pointAtomicModel ε
        (adjointUnitBall (alspachOrdinalRows 𝕜).evaluation) γ = ∅ := by
  obtain ⟨m, hm⟩ := alspach_exists_doubling_depth (half_pos hε)
  exact ⟨ω * ((m + 1 : ℕ) : Ordinal) + 1, alspach_next_block_add_one_lt_omega_sq m,
    alspachOrdinalEvaluation_wolfe_bound m hε hm⟩

end Posets
