import Posets.MatrixNorm
import Posets.SupportingStatements
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
open scoped ZeroAtInfty
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 ℬ : Set (Set ℕ)}

theorem czero_finset_sum_apply {I K : Type*} [TopologicalSpace K]
    (s : Finset I) (f : I → C₀(K, 𝕜)) (x : K) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih => simp [Finset.sum_insert ha, ZeroAtInftyContinuousMap.add_apply, ih]

theorem norm_finite_isolated_sum_le (𝒜 : Set (Set ℕ)) (F : Finset ℕ)
    (c : ℕ → 𝕜) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ n ∈ F, ‖c n‖ ≤ C) :
    ‖∑ n ∈ F, c n • isolatedVector 𝕜 𝒜 n‖ ≤ C := by
  classical
  apply (BoundedContinuousFunction.norm_le hC).mpr
  intro p
  change ‖(∑ n ∈ F, c n • isolatedVector 𝕜 𝒜 n) p‖ ≤ C
  rw [czero_finset_sum_apply]
  cases p with
  | inl k =>
    simp only [ZeroAtInftyContinuousMap.smul_apply, isolatedVector_natural, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hk
    · exact hc k hk
    · simpa using hC
  | inr A => simpa only [ZeroAtInftyContinuousMap.smul_apply, isolatedVector_family,
      smul_zero, Finset.sum_const_zero, norm_zero] using hC

/-- Test a finite row against its complex conjugate phases in the isolated span. -/
theorem reducedMatrix_finite_row_bound (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ)
    (k : ℕ) (F : Finset ℕ) : ∑ n ∈ F, ‖reducedMatrix 𝕜 T k n‖ ≤ ‖T‖ := by
  let c : ℕ → 𝕜 := fun n => normingPhase (reducedMatrix 𝕜 T k n)
  let f : Space 𝕜 𝒜 := ∑ n ∈ F, c n • isolatedVector 𝕜 𝒜 n
  have hf : ‖f‖ ≤ 1 := norm_finite_isolated_sum_le 𝒜 F c zero_le_one
    (fun n _ => norm_normingPhase_le _)
  have heval : T f (Sum.inl k) = ((∑ n ∈ F, ‖reducedMatrix 𝕜 T k n‖ : ℝ) : 𝕜) := by
    simp only [f, map_sum, map_smul, czero_finset_sum_apply,
      ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
    simp_rw [show ∀ n, c n * T (isolatedVector 𝕜 𝒜 n) (Sum.inl k) =
        (‖reducedMatrix 𝕜 T k n‖ : 𝕜) from
      fun n => by rw [mul_comm]; exact mul_normingPhase _]
  calc
    (∑ n ∈ F, ‖reducedMatrix 𝕜 T k n‖) = ‖T f (Sum.inl k)‖ := by
      rw [heval, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    _ ≤ ‖T f‖ := (T f).toBCF.norm_coe_le_norm _
    _ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
    _ ≤ ‖T‖ := by nlinarith [norm_nonneg T]

theorem reducedMatrix_row_summable (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) (k : ℕ) :
    Summable (fun n => ‖reducedMatrix 𝕜 T k n‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _) (reducedMatrix_finite_row_bound T k)

theorem reducedMatrix_row_bound (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) (k : ℕ) :
    (∑' n, ‖reducedMatrix 𝕜 T k n‖) ≤ ‖T‖ :=
  (reducedMatrix_row_summable T k).tsum_le_of_sum_le (reducedMatrix_finite_row_bound T k)

theorem reducedMatrixBound_proof (𝕜 : Type) [RCLike 𝕜] (𝒜 ℬ : Set (Set ℕ)) :
    ReducedMatrixBound 𝕜 𝒜 ℬ := by
  intro _ _ T
  exact ⟨⟨reducedMatrix_row_summable T, ‖T‖, reducedMatrix_row_bound T⟩,
    ciSup_le (reducedMatrix_row_bound T)⟩

end Posets
