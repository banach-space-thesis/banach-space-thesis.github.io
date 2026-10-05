import Posets.QuotientStatements
import Posets.ReducedMatrixBound
import PosetsCommon.DiscreteCZero

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology ThesisCommon
open scoped ZeroAtInfty
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜] {P : Type*} [PartialOrder P]

omit [PartialOrder P] in
theorem discreteUnit_eq_unitVector (p : Discrete P) :
    discreteUnit (𝕜 := 𝕜) p = unitVector 𝕜 p.val := by
  ext q
  cases p
  cases q
  simp [discreteUnit_apply, unitVector]

theorem continuous_czero_evaluation {K : Type*} [TopologicalSpace K] (x : K) :
    Continuous (fun f : C₀(K, 𝕜) => f x) :=
  BoundedContinuousFunction.continuous_eval_const.comp
    ZeroAtInftyContinuousMap.isometry_toBCF.continuous

omit [PartialOrder P] in
theorem continuous_scalarMatrix (s t : P) :
    Continuous (fun T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P => scalarMatrix 𝕜 T s t) :=
  (continuous_czero_evaluation (𝕜 := 𝕜) (⟨s⟩ : Discrete P)).comp
    (ContinuousLinearMap.apply 𝕜 (CZeroOn 𝕜 P) (unitVector 𝕜 t)).continuous

/-- The upper-triangular zero pattern is preserved under actual operator composition. -/
theorem incidenceOperators_mul {S T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P}
    (hS : S ∈ incidenceOperators 𝕜 P) (hT : T ∈ incidenceOperators 𝕜 P) :
    S * T ∈ incidenceOperators 𝕜 P := by
  intro s t hst
  let f := T (unitVector 𝕜 t)
  have hlim : Tendsto (fun F : Finset (Discrete P) => S (discreteTruncation F f) ⟨s⟩)
      atTop (𝓝 (S f ⟨s⟩)) :=
    ((continuous_czero_evaluation (𝕜 := 𝕜) (⟨s⟩ : Discrete P)).comp S.continuous).continuousAt.tendsto.comp
      (discreteTruncation_tendsto f)
  have hzero : ∀ F : Finset (Discrete P), S (discreteTruncation F f) ⟨s⟩ = 0 := by
    intro F
    simp only [discreteTruncation, map_sum, map_smul, czero_finset_sum_apply,
      ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro p _
    rw [discreteUnit_eq_unitVector]
    by_cases hsp : s ≤ p.val
    · have hpt : ¬ p.val ≤ t := fun h => hst (hsp.trans h)
      have hz : f p = 0 := hT p.val t hpt
      rw [hz, zero_mul]
    · have hz : S (unitVector 𝕜 p.val) ⟨s⟩ = 0 := hS s p.val hsp
      rw [hz, mul_zero]
  exact tendsto_nhds_unique hlim (by simpa only [hzero] using
    (tendsto_const_nhds : Tendsto (fun _ : Finset (Discrete P) => (0 : 𝕜)) atTop (𝓝 0)))

/-- The incidence algebra with its concrete inherited operator norm and multiplication. -/
def incidenceSubalgebra (𝕜 : Type*) [RCLike 𝕜] (P : Type*) [PartialOrder P] :
    Subalgebra 𝕜 (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) where
  carrier := incidenceOperators 𝕜 P
  mul_mem' := incidenceOperators_mul
  add_mem' := by
    intro S T hS hT s t hst
    change scalarMatrix 𝕜 S s t + scalarMatrix 𝕜 T s t = 0
    rw [hS s t hst, hT s t hst, add_zero]
  algebraMap_mem' := by
    intro a s t hst
    have hne : s ≠ t := fun h => hst (h ▸ le_rfl)
    simp [scalarMatrix, unitVector, hne]

theorem incidenceOperators_isClosed :
    IsClosed (incidenceOperators 𝕜 P) := by
  have heq : incidenceOperators 𝕜 P =
      ⋂ s, ⋂ t, ⋂ (_ : ¬ s ≤ t), {T | scalarMatrix 𝕜 T s t = 0} := by
    ext T
    simp [incidenceOperators]
  rw [heq]
  exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
    isClosed_eq (continuous_scalarMatrix s t) continuous_const

theorem proposition_6_11_proof (𝕜 : Type) [RCLike 𝕜] (P : Type)
    [PartialOrder P] [Countable P] [Infinite P] : Proposition_6_11 𝕜 P :=
  ⟨incidenceSubalgebra 𝕜 P, rfl, incidenceOperators_isClosed⟩

def oppositeIncidenceSubalgebra (𝕜 : Type*) [RCLike 𝕜] (P : Type*) [PartialOrder P] :
    Subalgebra 𝕜 (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) :=
  incidenceSubalgebra 𝕜 Pᵒᵈ

theorem oppositeIncidenceSubalgebra_carrier :
    (oppositeIncidenceSubalgebra 𝕜 P : Set _) = oppositeIncidenceOperators 𝕜 P := rfl

theorem oppositeIncidenceOperators_isClosed :
    IsClosed (oppositeIncidenceOperators 𝕜 P) :=
  incidenceOperators_isClosed (P := Pᵒᵈ)

/-- Example 6.12: the usual order on ℕ gives upper-triangular matrices. -/
theorem nat_incidence_iff_upperTriangular
    (T : CZeroOn 𝕜 ℕ →L[𝕜] CZeroOn 𝕜 ℕ) :
    T ∈ incidenceOperators 𝕜 ℕ ↔ ∀ s t, t < s → scalarMatrix 𝕜 T s t = 0 := by
  simp [incidenceOperators, not_le]

/-- The opposite order in Example 6.12 gives lower-triangular matrices. -/
theorem nat_oppositeIncidence_iff_lowerTriangular
    (T : CZeroOn 𝕜 ℕ →L[𝕜] CZeroOn 𝕜 ℕ) :
    T ∈ oppositeIncidenceOperators 𝕜 ℕ ↔ ∀ s t, s < t → scalarMatrix 𝕜 T s t = 0 := by
  simp [oppositeIncidenceOperators, not_le]

end Posets
