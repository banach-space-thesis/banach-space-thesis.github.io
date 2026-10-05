import Posets.IncidenceOperators

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology ThesisCommon
open scoped ZeroAtInfty
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type*}

@[simp] theorem unitVector_apply (t : P) (s : Discrete P) :
    unitVector 𝕜 t s = if s.val = t then 1 else 0 := rfl

theorem scalarMatrix_injective : Function.Injective (scalarMatrix (P := P) 𝕜) := by
  intro S T h
  apply ContinuousLinearMap.ext_on discreteUnit_dense_span
  rintro _ ⟨p, rfl⟩
  rw [discreteUnit_eq_unitVector]
  ext q
  exact congrFun (congrFun h q.val) p.val

theorem norm_finite_unit_sum_le (F : Finset P) (c : P → 𝕜)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t ∈ F, ‖c t‖ ≤ C) :
    ‖∑ t ∈ F, c t • unitVector 𝕜 t‖ ≤ C := by
  apply (BoundedContinuousFunction.norm_le hC).mpr
  intro p
  change ‖(∑ t ∈ F, c t • unitVector 𝕜 t) p‖ ≤ C
  rw [czero_finset_sum_apply]
  simp only [ZeroAtInftyContinuousMap.smul_apply, unitVector_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hp
  · exact hc p.val hp
  · simpa using hC

theorem scalarMatrix_finite_row_bound (T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P)
    (s : P) (F : Finset P) : ∑ t ∈ F, ‖scalarMatrix 𝕜 T s t‖ ≤ ‖T‖ := by
  let c : P → 𝕜 := fun t => normingPhase (scalarMatrix 𝕜 T s t)
  let f : CZeroOn 𝕜 P := ∑ t ∈ F, c t • unitVector 𝕜 t
  have hf : ‖f‖ ≤ 1 := norm_finite_unit_sum_le F c zero_le_one
    (fun _ _ => norm_normingPhase_le _)
  have heval : T f ⟨s⟩ = ((∑ t ∈ F, ‖scalarMatrix 𝕜 T s t‖ : ℝ) : 𝕜) := by
    simp only [f, map_sum, map_smul, czero_finset_sum_apply,
      ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
    simp_rw [show ∀ t, c t * T (unitVector 𝕜 t) ⟨s⟩ = (‖scalarMatrix 𝕜 T s t‖ : 𝕜) from
      fun t => by rw [mul_comm]; exact mul_normingPhase _]
  calc
    (∑ t ∈ F, ‖scalarMatrix 𝕜 T s t‖) = ‖T f ⟨s⟩‖ := by
      rw [heval, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    _ ≤ ‖T f‖ := (T f).toBCF.norm_coe_le_norm _
    _ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
    _ ≤ ‖T‖ := by nlinarith [norm_nonneg T]

theorem scalarMatrix_row_summable (T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) (s : P) :
    Summable (fun t => ‖scalarMatrix 𝕜 T s t‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _) (scalarMatrix_finite_row_bound T s)

theorem scalarMatrix_row_bound (T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) (s : P) :
    (∑' t, ‖scalarMatrix 𝕜 T s t‖) ≤ ‖T‖ :=
  (scalarMatrix_row_summable T s).tsum_le_of_sum_le (scalarMatrix_finite_row_bound T s)

theorem scalarMatrix_boundedRows (T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) :
    BoundedRowsOn 𝕜 (scalarMatrix 𝕜 T) :=
  ⟨scalarMatrix_row_summable T, ‖T‖, scalarMatrix_row_bound T⟩

theorem scalarMatrix_zeroColumns (T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) :
    ZeroColumnsOn 𝕜 (scalarMatrix 𝕜 T) := by
  intro t
  have h := zero_at_infty (T (unitVector 𝕜 t))
  rw [cocompact_eq_cofinite] at h
  exact h.comp (show Function.Injective (fun p : P => (⟨p⟩ : Discrete P)) from
    fun _ _ h => Discrete.mk.inj h).tendsto_cofinite

end Posets
