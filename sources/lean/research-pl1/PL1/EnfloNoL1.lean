import PL1.EnfloCopyExclusion
import PL1.EnfloSmoothing
import PL1.PartialMainTheorems
import PL1.ComplementedLatticeReduction

/-! # Actual exclusion of arbitrary interval L1 copies in the constant-rate example

Positive-time noise decay is proved for every real L1 source operator. The
resolvent and intrinsic-coordinate arguments then exclude bounded-below maps,
and actual range equivalences transport the conclusion to interval L1.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped NNReal ENNReal
namespace PL1.Noise
open Walsh EnfloBush

/-- Every actual dyadic constant-rate resolvent has the full arbitrary-source
maximum-mass decay required by the intrinsic argument. -/
theorem constant_dyadicOperator_comp_dyadicVanishing
    (n : ℕ) (S : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 haar) :
    DyadicVanishing (((dyadicSystem ℝ constantRates).operator n).comp S) :=
  dyadicVanishing_resolvent_of_noise constantRates noise_comp_dyadicVanishing (dyadicTime n) S

theorem constant_intrinsic_no_real_L1 (K : Type*) [RCLike K] :
    ¬ ContainsIsomorphicCopy ℝ (IntervalL1 ℝ) (dyadicSystem K constantRates).IntrinsicSpace :=
  scalarIntrinsic_no_real_L1_of_operators K constantRates constant_dyadicOperator_comp_dyadicVanishing

theorem constant_projection_range_no_real_L1 (K : Type*) [RCLike K] :
    ¬ ContainsIsomorphicCopy ℝ (IntervalL1 ℝ) (projection K constantRates).range := by
  change ¬ ContainsIsomorphicCopy ℝ (IntervalL1 ℝ) (dyadicSystem K constantRates).projection.range
  rw [DyadicSystem.projection_range]
  exact constant_intrinsic_no_real_L1 K

/-- Restriction of the actual range equivalence to the compatible real actions.
The pinned continuous-equivalence restriction API only handles endomorphisms,
so the two different range types are bundled explicitly. -/
def intervalProjectionRangeRealEquiv (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0) :
    (projection K rates).range ≃L[ℝ] (intervalProjection K rates).range where
  toLinearEquiv := (intervalProjectionRangeEquiv K rates).toLinearEquiv.restrictScalars ℝ
  continuous_toFun := (intervalProjectionRangeEquiv K rates).continuous
  continuous_invFun := (intervalProjectionRangeEquiv K rates).symm.continuous
/-- Even the natural real Banach space underlying the real or complex
interval projection range contains no closed isomorphic real interval-L1 copy. -/
theorem constant_intervalProjection_range_no_real_L1 (K : Type*) [RCLike K] :
    ¬ ContainsIsomorphicCopy ℝ (IntervalL1 ℝ) (intervalProjection K constantRates).range := by
  intro hc
  exact constant_projection_range_no_real_L1 K
    (hc.map (intervalProjectionRangeRealEquiv K constantRates).symm)

/-- The same no-copy result with the explicitly restricted scalar convention
used in the reviewed theorem statements. -/
theorem constant_intervalProjection_range_no_underlying_real_L1 (K : Type*) [RCLike K] :
    ¬ @ContainsIsomorphicCopy ℝ _ (IntervalL1 ℝ) _ _
      (UnderlyingReal K (intervalProjection K constantRates).range)
      (inferInstanceAs (NormedAddCommGroup (intervalProjection K constantRates).range))
      (NormedSpace.restrictScalars ℝ K (intervalProjection K constantRates).range) := by
  intro hc
  exact constant_intervalProjection_range_no_real_L1 K
    (hc.map (ComplementedLattice.naturalToUnderlyingReal (K := K)
      (intervalProjection K constantRates).range).symm)

/-- In particular no scalar interval-L1 copy exists, with the original scalar
field and the original interval projection range norm. -/
theorem constant_intervalProjection_range_no_L1 (K : Type*) [RCLike K] :
    ¬ ContainsIsomorphicCopy K (IntervalL1 K) (intervalProjection K constantRates).range := by
  let : CompleteSpace (intervalProjection K constantRates).range :=
    (intervalProjection_range_isClosed K constantRates).isComplete.completeSpace_coe
  intro hc
  exact constant_intervalProjection_range_no_real_L1 K
    (ComplementedLattice.scalar_L1_copy_contains_real_L1 hc)

#print axioms constant_intervalProjection_range_no_real_L1
#print axioms constant_intervalProjection_range_no_underlying_real_L1
#print axioms constant_intervalProjection_range_no_L1
end PL1.Noise

