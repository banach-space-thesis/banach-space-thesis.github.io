import PL1.Statements
import PL1.IntervalWalsh
import PL1.SchurExample
import PL1.SingularResolvents
import PL1.RNPTransport
import PL1.RealSchur
import PL1.SeparableRange

/-!
# Proved interval-level parts of the main theorems

These are concrete existence results on the reviewed interval L1 space.
Theorem A's nonlattice clause and Theorem B's exclusion of L1 copies and
nonlattice clause are not asserted here. The full reviewed target definitions
in `PL1.Statements` remain unchanged. `PL1.MainTheoremA` now proves all of A;
the complete B endpoint remains conditional on explicit structural results.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace PL1.Noise

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The actual projection on L1([0,1]), obtained through the constructed
isometric embedding and contractive retraction. -/
def intervalProjection (rates : ℕ → ℝ≥0) : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜 :=
  (IntervalWalsh.walshSumContractiveRetract 𝕜).transport (projection 𝕜 rates)

def intervalProjectionRangeEquiv (rates : ℕ → ℝ≥0) :
    (projection 𝕜 rates).range ≃L[𝕜] (intervalProjection 𝕜 rates).range :=
  (IntervalWalsh.walshSumContractiveRetract 𝕜).rangeEquiv (projection 𝕜 rates)

theorem intervalProjection_isProjection (rates : ℕ → ℝ≥0) :
    IsProjection (intervalProjection 𝕜 rates) :=
  (IntervalWalsh.walshSumContractiveRetract 𝕜).isProjection (projection_isProjection 𝕜 rates)

theorem norm_intervalProjection_le (rates : ℕ → ℝ≥0) :
    ‖intervalProjection 𝕜 rates‖ ≤ projectionBound :=
  ((IntervalWalsh.walshSumContractiveRetract 𝕜).norm_transport_le _).trans
    (norm_projection_le 𝕜 rates)

theorem intervalProjection_range_isClosed (rates : ℕ → ℝ≥0) :
    IsClosed ((intervalProjection 𝕜 rates).range : Set (IntervalL1 𝕜)) :=
  (intervalProjection_isProjection 𝕜 rates).isClosed_range

theorem intervalProjection_range_infiniteDimensional (rates : ℕ → ℝ≥0) :
    ¬ FiniteDimensional 𝕜 (intervalProjection 𝕜 rates).range := by
  intro h
  exact projection_range_infiniteDimensional 𝕜 rates
    (((IntervalWalsh.walshSumContractiveRetract 𝕜).finiteDimensional_range_iff _).mp h)

theorem schur_intervalProjection_isDunfordPettis :
    IsDunfordPettis (intervalProjection 𝕜 schurRates) :=
  (IntervalWalsh.walshSumContractiveRetract 𝕜).isDunfordPettis
    (schurRates_projection_isDunfordPettis 𝕜)

theorem schur_intervalProjection_range_hasSchurProperty :
    HasSchurProperty 𝕜 (intervalProjection 𝕜 schurRates).range :=
  (hasSchurProperty_equiv_iff (intervalProjectionRangeEquiv 𝕜 schurRates)).mp
    (schurRates_projection_range_hasSchurProperty 𝕜)

theorem schur_intervalProjection_range_not_RNP :
    ¬ @HasRadonNikodymProperty.{_, 0}
      (UnderlyingReal 𝕜 (intervalProjection 𝕜 schurRates).range)
      (inferInstanceAs (NormedAddCommGroup (intervalProjection 𝕜 schurRates).range))
      (NormedSpace.restrictScalars ℝ 𝕜 (intervalProjection 𝕜 schurRates).range) := by
  intro h
  exact schur_projection_range_not_RNP 𝕜
    ((RNPTransport.hasRadonNikodymProperty_restrictScalars_iff
      (intervalProjectionRangeEquiv 𝕜 schurRates)).mpr h)

theorem constant_intervalProjection_range_contains_ell2 :
    ContainsIsomorphicCopy 𝕜 (Ell2 𝕜) (intervalProjection 𝕜 constantRates).range :=
  (constantRates_projection_range_contains_ell2 𝕜).map
    (intervalProjectionRangeEquiv 𝕜 constantRates)

theorem constant_intervalProjection_range_not_schur :
    ¬ HasSchurProperty 𝕜 (intervalProjection 𝕜 constantRates).range :=
  not_hasSchurProperty_of_contains_ell2 𝕜
    (constant_intervalProjection_range_contains_ell2 𝕜)

theorem constant_intervalProjection_range_not_RNP :
    ¬ @HasRadonNikodymProperty.{_, 0}
      (UnderlyingReal 𝕜 (intervalProjection 𝕜 constantRates).range)
      (inferInstanceAs (NormedAddCommGroup (intervalProjection 𝕜 constantRates).range))
      (NormedSpace.restrictScalars ℝ 𝕜 (intervalProjection 𝕜 constantRates).range) := by
  intro h
  exact constant_projection_range_not_RNP 𝕜
    ((RNPTransport.hasRadonNikodymProperty_restrictScalars_iff
      (intervalProjectionRangeEquiv 𝕜 constantRates)).mpr h)

end PL1.Noise

namespace PL1

/-- All reviewed Theorem A clauses except nonlattice, for one actual interval
projection. `PL1.MainTheoremA` supplies the full theorem separately. -/
theorem theoremA_except_nonlattice (𝕜 : Type*) [RCLike 𝕜] :
    ∃ P : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜,
      IsProjection P ∧ ‖P‖ ≤ projectionBound ∧
      IsClosed (P.range : Set (IntervalL1 𝕜)) ∧ ¬ FiniteDimensional 𝕜 P.range ∧
      IsDunfordPettis P ∧ HasSchurProperty 𝕜 P.range ∧
      ¬ @HasRadonNikodymProperty.{_, 0} (UnderlyingReal 𝕜 P.range)
        (inferInstanceAs (NormedAddCommGroup P.range))
        (NormedSpace.restrictScalars ℝ 𝕜 P.range) :=
  ⟨Noise.intervalProjection 𝕜 Noise.schurRates,
    Noise.intervalProjection_isProjection 𝕜 Noise.schurRates,
    Noise.norm_intervalProjection_le 𝕜 Noise.schurRates,
    Noise.intervalProjection_range_isClosed 𝕜 Noise.schurRates,
    Noise.intervalProjection_range_infiniteDimensional 𝕜 Noise.schurRates,
    Noise.schur_intervalProjection_isDunfordPettis 𝕜,
    Noise.schur_intervalProjection_range_hasSchurProperty 𝕜,
    Noise.schur_intervalProjection_range_not_RNP 𝕜⟩

/-- The constructed non-Schur interval projection and its closed ell2 copy.
The exclusion of L1 copies and the nonlattice clause are still unproved.
The additional RNP failure is the paper's later non-Schur geometry claim. -/
theorem theoremB_partial (𝕜 : Type*) [RCLike 𝕜] :
    ∃ Q : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜,
      IsProjection Q ∧ ‖Q‖ ≤ projectionBound ∧
      IsClosed (Q.range : Set (IntervalL1 𝕜)) ∧ ¬ FiniteDimensional 𝕜 Q.range ∧
      ContainsIsomorphicCopy 𝕜 (Ell2 𝕜) Q.range ∧ ¬ HasSchurProperty 𝕜 Q.range ∧
      ¬ @HasRadonNikodymProperty.{_, 0} (UnderlyingReal 𝕜 Q.range)
        (inferInstanceAs (NormedAddCommGroup Q.range))
        (NormedSpace.restrictScalars ℝ 𝕜 Q.range) :=
  ⟨Noise.intervalProjection 𝕜 Noise.constantRates,
    Noise.intervalProjection_isProjection 𝕜 Noise.constantRates,
    Noise.norm_intervalProjection_le 𝕜 Noise.constantRates,
    Noise.intervalProjection_range_isClosed 𝕜 Noise.constantRates,
    Noise.intervalProjection_range_infiniteDimensional 𝕜 Noise.constantRates,
    Noise.constant_intervalProjection_range_contains_ell2 𝕜,
    Noise.constant_intervalProjection_range_not_schur 𝕜,
    Noise.constant_intervalProjection_range_not_RNP 𝕜⟩

end PL1
