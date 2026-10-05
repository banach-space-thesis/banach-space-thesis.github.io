import ThesisCommon.Analysis.ContinuousMapComplexPartition
import ThesisCommon.Analysis.ContinuousMapDualAL

/-! Positive domination on real nonnegative continuous tests controls the
full complex dual norm sharply. The proof uses genuine finite partitions
of unity and uniform approximation. -/
noncomputable section
open Finset
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

theorem norm_continuousMap_complex_functional_le_positive_bound
    (φ : C(K, ℂ) →L[ℂ] ℂ) (R : C(K, ℝ) →L[ℝ] ℝ)
    (hR : ∀ f, 0 ≤ f → 0 ≤ R f)
    (hdom : ∀ f, 0 ≤ f → ‖φ (continuousMapOfReal f)‖ ≤ R f) : ‖φ‖ ≤ R 1 := by
  have hR1 : 0 ≤ R 1 := hR _ (fun _ => zero_le_one)
  apply ContinuousLinearMap.opNorm_le_bound _ hR1
  intro f
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (‖φ‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨s, p, hp, hsum, happ⟩ := exists_continuousMap_complex_positive_partition f hδ
  let g : C(K, ℂ) := ∑ i : s, f i.val • continuousMapOfReal (𝕜 := ℂ) (p i)
  have hg : ‖φ g‖ ≤ R 1 * ‖f‖ := by
    calc
      ‖φ g‖ = ‖∑ i : s, f i.val • φ (continuousMapOfReal (p i))‖ := by
        simp only [g, map_sum, map_smul]
      _ ≤ ∑ i : s, ‖f i.val • φ (continuousMapOfReal (p i))‖ := norm_sum_le _ _
      _ ≤ ∑ i : s, ‖f‖ * R (p i) := by
        apply sum_le_sum
        intro i hi
        rw [norm_smul]
        exact mul_le_mul (f.norm_coe_le_norm i.val) (hdom _ (hp i))
          (norm_nonneg _) (norm_nonneg f)
      _ = R 1 * ‖f‖ := by rw [← mul_sum, ← map_sum, hsum, mul_comm]
  have he : ‖φ (f - g)‖ ≤ ε := by
    have happ' : ‖f - g‖ ≤ δ := by rw [norm_sub_rev]; exact happ
    apply (φ.le_opNorm _).trans ((mul_le_mul_of_nonneg_left happ' (norm_nonneg φ)).trans ?_)
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < ‖φ‖ + 1)).mpr
    nlinarith
  calc
    ‖φ f‖ = ‖φ (f - g) + φ g‖ := by rw [← map_add, sub_add_cancel]
    _ ≤ ‖φ (f - g)‖ + ‖φ g‖ := norm_add_le _ _
    _ ≤ R 1 * ‖f‖ + ε := by linarith

theorem norm_continuousMap_complex_functional_eq_positive_one
    (φ : C(K, ℂ) →L[ℂ] ℂ) (R : C(K, ℝ) →L[ℝ] ℝ)
    (hR : ∀ f, 0 ≤ f → 0 ≤ R f)
    (hreal : ∀ f, φ (continuousMapOfReal f) = (R f : ℂ)) : ‖φ‖ = R 1 := by
  apply le_antisymm
  · apply norm_continuousMap_complex_functional_le_positive_bound φ R hR
    intro f hf
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hR f hf)]
  · have h1 : φ 1 = (R 1 : ℂ) := by simpa using hreal 1
    have hone : ‖(1 : C(K, ℂ))‖ ≤ 1 :=
      (ContinuousMap.norm_le _ zero_le_one).mpr (fun _ => by simp)
    calc
      R 1 = ‖φ 1‖ := by
        rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hR _ (fun _ => zero_le_one))]
      _ ≤ ‖φ‖ * ‖(1 : C(K, ℂ))‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ := by simpa using mul_le_mul_of_nonneg_left hone (norm_nonneg φ)

end ThesisCommon
