import ThesisCommon.Analysis.DisjointSequenceBlocks
import ThesisCommon.Analysis.SequenceCoordinates
import Mathlib.Data.Set.Finite.Lattice

/-! The actual isomorphism c₀(c₀(X)) ≃ c₀(X).
Flattening has finitely many large coordinates because only finitely many
rows have large norm, and each of those rows has finitely many large entries.
Conversely, the first-coordinate projection of a finite exceptional set
controls the norms of all but finitely many rows. Thus both maps preserve
the actual vanishing-at-infinity condition.
-/
noncomputable section
open Filter Topology
open scoped ZeroAtInfty
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem cZero_finite_norm_exception (x : CZeroSum X) {ε : ℝ} (hε : 0 < ε) :
    {n | ¬ ‖x n‖ < ε}.Finite := by
  have h := Metric.tendsto_nhds.mp x.zero_at_infty' ε hε
  rw [cocompact_eq_cofinite] at h
  simpa only [dist_zero_right] using mem_cofinite.mp h

def cZeroFlattenValue (x : CZeroSum (CZeroSum X)) : CZeroSum X where
  toFun n := x (Nat.unpair n).1 (Nat.unpair n).2
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    rw [cocompact_eq_cofinite]
    let A := {i | ¬ ‖x i‖ < ε}
    let B := fun i => {j | ¬ ‖x i j‖ < ε}
    have hA : A.Finite := cZero_finite_norm_exception x hε
    have hB (i : ℕ) : (B i).Finite := cZero_finite_norm_exception (x i) hε
    have hbad : (⋃ i ∈ A, Nat.pair i '' B i).Finite :=
      hA.biUnion (fun i _ => (hB i).image (Nat.pair i))
    filter_upwards [hbad.compl_mem_cofinite] with n hn
    rw [dist_zero_right]
    by_contra hnlarge
    have hi : (Nat.unpair n).1 ∈ A := by
      intro hsmall
      exact hnlarge ((BoundedContinuousFunction.norm_coe_le_norm
        (x (Nat.unpair n).1).toBCF (Nat.unpair n).2).trans_lt hsmall)
    have hj : (Nat.unpair n).2 ∈ B (Nat.unpair n).1 := hnlarge
    exact hn (Set.mem_iUnion.mpr ⟨(Nat.unpair n).1,
      Set.mem_iUnion.mpr ⟨hi, ⟨(Nat.unpair n).2, hj, Nat.pair_unpair n⟩⟩⟩)

theorem norm_cZeroFlattenValue_le (x : CZeroSum (CZeroSum X)) :
    ‖cZeroFlattenValue x‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro n
  exact (BoundedContinuousFunction.norm_coe_le_norm
    (x (Nat.unpair n).1).toBCF (Nat.unpair n).2).trans
      (BoundedContinuousFunction.norm_coe_le_norm x.toBCF (Nat.unpair n).1)

def cZeroUnflattenValue (x : CZeroSum X) : CZeroSum (CZeroSum X) where
  toFun i := cZeroRead (disjointCoordinateEmbedding i) x
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    rw [cocompact_eq_cofinite]
    let B := {n | ¬ ‖x n‖ < ε / 2}
    have hB : B.Finite := cZero_finite_norm_exception x (half_pos hε)
    filter_upwards [(hB.image (fun n => (Nat.unpair n).1)).compl_mem_cofinite] with i hi
    have hpoint (j : ℕ) : ‖x (Nat.pair i j)‖ < ε / 2 := by
      by_contra hlarge
      exact hi ⟨Nat.pair i j, hlarge, by simp⟩
    have hnorm : ‖cZeroRead (disjointCoordinateEmbedding i) x‖ ≤ ε / 2 := by
      apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
      intro j
      exact (hpoint j).le
    simpa only [dist_zero_right] using hnorm.trans_lt (half_lt_self hε)

theorem norm_cZeroUnflattenValue_le (x : CZeroSum X) :
    ‖cZeroUnflattenValue x‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro i
  exact norm_cZeroRead_le (disjointCoordinateEmbedding i) x

def cZeroFlatten : CZeroSum (CZeroSum X) →L[𝕜] CZeroSum X :=
  LinearMap.mkContinuous
    { toFun := cZeroFlattenValue
      map_add' := by intros; ext n; rfl
      map_smul' := by intros; ext n; rfl }
    1 (fun x => by simpa only [one_mul] using norm_cZeroFlattenValue_le x)

def cZeroUnflatten : CZeroSum X →L[𝕜] CZeroSum (CZeroSum X) :=
  LinearMap.mkContinuous
    { toFun := cZeroUnflattenValue
      map_add' := by intros; ext i j; rfl
      map_smul' := by intros; ext i j; rfl }
    1 (fun x => by simpa only [one_mul] using norm_cZeroUnflattenValue_le x)

/-- Pairing is a bounded isomorphism of the genuine null-sequence spaces. -/
def cZeroFlattenEquiv : CZeroSum (CZeroSum X) ≃L[𝕜] CZeroSum X :=
  ContinuousLinearEquiv.equivOfInverse cZeroFlatten cZeroUnflatten
    (by
      intro x
      ext i j
      change x (Nat.unpair (Nat.pair i j)).1 (Nat.unpair (Nat.pair i j)).2 = x i j
      rw [Nat.unpair_pair])
    (by
      intro x
      ext n
      change x (Nat.pair (Nat.unpair n).1 (Nat.unpair n).2) = x n
      rw [Nat.pair_unpair])

theorem cZero_sequenceSelfSimilar : IsSequenceSelfSimilar 𝕜 (CZeroSum X) :=
  Or.inr ⟨cZeroFlattenEquiv.symm⟩

end ThesisCommon
