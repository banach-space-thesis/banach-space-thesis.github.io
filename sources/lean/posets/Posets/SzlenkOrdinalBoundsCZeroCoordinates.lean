import Posets.SzlenkIdealComposition
import Posets.Definitions
import JLMS.DisjointWeakNull

/-! The scalar c₀ dual's ℓ¹ coordinates, with estimates separating a finite
coordinate set from its complement. -/

noncomputable section
open Set Topology Filter ThesisCommon
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]

theorem cZeroDual_summable_norm (φ : StrongDual 𝕜 (cZero 𝕜)) :
    Summable (fun n => ‖φ (JLMS.cZeroUnit 𝕜 n)‖) := by
  obtain ⟨a, rfl⟩ := JLMS.atomicSynthesis_surjective (𝕜 := 𝕜)
    (JLMS.isScattered_discrete ℕ) φ
  simpa only [JLMS.atomicSynthesis_apply, JLMS.atomicFunctional_cZeroUnit]
    using JLMS.ellOneOn_summable_norm a

theorem cZeroDual_norm_eq_tsum (φ : StrongDual 𝕜 (cZero 𝕜)) :
    ‖φ‖ = ∑' n, ‖φ (JLMS.cZeroUnit 𝕜 n)‖ := by
  obtain ⟨a, rfl⟩ := JLMS.atomicSynthesis_surjective (𝕜 := 𝕜)
    (JLMS.isScattered_discrete ℕ) φ
  simp only [JLMS.atomicSynthesis_apply, JLMS.atomicFunctional_cZeroUnit,
    JLMS.norm_atomicFunctional (JLMS.isScattered_discrete ℕ), JLMS.ellOneOn_norm_eq_tsum]

theorem cZeroDual_finite_mass_approx (φ : StrongDual 𝕜 (cZero 𝕜))
    {r : ℝ} (hr : r < ‖φ‖) : ∃ s : Finset ℕ, r < ∑ i ∈ s, ‖φ (JLMS.cZeroUnit 𝕜 i)‖ := by
  have ht := (cZeroDual_summable_norm φ).hasSum
  rw [← cZeroDual_norm_eq_tsum] at ht
  exact (ht.eventually (Ioi_mem_nhds hr)).exists

theorem cZeroDual_norm_sub_le_head_tails (φ ψ : StrongDual 𝕜 (cZero 𝕜)) (s : Finset ℕ) :
    ‖φ - ψ‖ ≤ (∑ i ∈ s, ‖φ (JLMS.cZeroUnit 𝕜 i) - ψ (JLMS.cZeroUnit 𝕜 i)‖) +
      (‖φ‖ - ∑ i ∈ s, ‖φ (JLMS.cZeroUnit 𝕜 i)‖) +
      (‖ψ‖ - ∑ i ∈ s, ‖ψ (JLMS.cZeroUnit 𝕜 i)‖) := by
  classical
  have hφ := (cZeroDual_summable_norm φ).sum_add_tsum_subtype_compl s
  have hψ := (cZeroDual_summable_norm ψ).sum_add_tsum_subtype_compl s
  have hdiff := (cZeroDual_summable_norm (φ - ψ)).sum_add_tsum_subtype_compl s
  rw [← cZeroDual_norm_eq_tsum] at hφ hψ hdiff
  simp only [ContinuousLinearMap.sub_apply] at hdiff
  have htφ : Summable (fun i : {n // n ∉ s} => ‖φ (JLMS.cZeroUnit 𝕜 i.val)‖) :=
    (cZeroDual_summable_norm φ).subtype {n | n ∉ s}
  have htψ : Summable (fun i : {n // n ∉ s} => ‖ψ (JLMS.cZeroUnit 𝕜 i.val)‖) :=
    (cZeroDual_summable_norm ψ).subtype {n | n ∉ s}
  have htd : Summable (fun i : {n // n ∉ s} => ‖(φ - ψ) (JLMS.cZeroUnit 𝕜 i.val)‖) :=
    (cZeroDual_summable_norm (φ - ψ)).subtype {n | n ∉ s}
  have ht : (∑' i : {n // n ∉ s}, ‖(φ - ψ) (JLMS.cZeroUnit 𝕜 i.val)‖) ≤
      (∑' i : {n // n ∉ s}, ‖φ (JLMS.cZeroUnit 𝕜 i.val)‖) +
        ∑' i : {n // n ∉ s}, ‖ψ (JLMS.cZeroUnit 𝕜 i.val)‖ := by
    calc
      _ ≤ ∑' i : {n // n ∉ s},
          (‖φ (JLMS.cZeroUnit 𝕜 i.val)‖ + ‖ψ (JLMS.cZeroUnit 𝕜 i.val)‖) :=
        htd.tsum_le_tsum (fun i => norm_sub_le
          (φ (JLMS.cZeroUnit 𝕜 i.val)) (ψ (JLMS.cZeroUnit 𝕜 i.val))) (htφ.add htψ)
      _ = _ := htφ.tsum_add htψ
  simp only [ContinuousLinearMap.sub_apply] at ht
  linarith

theorem cZeroDual_head_norm_le (φ ψ : StrongDual 𝕜 (cZero 𝕜)) (s : Finset ℕ) :
    (∑ i ∈ s, ‖φ (JLMS.cZeroUnit 𝕜 i)‖) ≤
      (∑ i ∈ s, ‖φ (JLMS.cZeroUnit 𝕜 i) - ψ (JLMS.cZeroUnit 𝕜 i)‖) +
        ∑ i ∈ s, ‖ψ (JLMS.cZeroUnit 𝕜 i)‖ := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => norm_le_norm_sub_add _ _)

theorem cZeroDual_head_distance_triangle (φ ψ χ : StrongDual 𝕜 (cZero 𝕜)) (s : Finset ℕ) :
    (∑ i ∈ s, ‖φ (JLMS.cZeroUnit 𝕜 i) - ψ (JLMS.cZeroUnit 𝕜 i)‖) ≤
      (∑ i ∈ s, ‖φ (JLMS.cZeroUnit 𝕜 i) - χ (JLMS.cZeroUnit 𝕜 i)‖) +
        ∑ i ∈ s, ‖ψ (JLMS.cZeroUnit 𝕜 i) - χ (JLMS.cZeroUnit 𝕜 i)‖ := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [norm_sub_rev] using
    norm_sub_le_norm_sub_add_norm_sub (φ (JLMS.cZeroUnit 𝕜 i))
      (χ (JLMS.cZeroUnit 𝕜 i)) (ψ (JLMS.cZeroUnit 𝕜 i))

end Posets
