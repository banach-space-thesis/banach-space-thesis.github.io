import PL1CD.LpEntropyGap
import PL1CD.FiniteEntropy
import PL1CD.CylinderRefinement

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PL1CD.Entropy

variable {ι κ Ω : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]

theorem finiteAverage_sq_le (f : ι → ℝ) :
    finiteAverage f ^ 2 ≤ finiteAverage (fun i => f i ^ 2) := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) f (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hcs
  have h := mul_le_mul_of_nonneg_left hcs (sq_nonneg (Fintype.card ι : ℝ)⁻¹)
  unfold finiteAverage
  field_simp at h ⊢
  nlinarith

theorem finiteAverage_prod (f : ι × κ → ℝ) :
    finiteAverage f = finiteAverage (fun i => finiteAverage (fun j => f (i, j))) := by
  simp only [finiteAverage, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

variable [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem bounded_lp_average_energy (f : ι → Lp ℝ 1 μ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i, ∀ᵐ x ∂μ, f i x ∈ Set.Icc 0 C)
    (hmass : ∀ i, ∫ x, f i x ∂μ ≤ 1) :
    finiteAverage (fun i => ‖f i - lpAverage μ f‖) ^ 2 ≤
      4 * (finiteAverage (fun i => Phi μ (f i)) - Phi μ (lpAverage μ f)) := by
  have hgap := bounded_lp_average_entropy_gap μ f C hC hbound hmass
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ finiteAverage (fun i => ‖f i - lpAverage μ f‖ ^ 2) := finiteAverage_sq_le _
    _ = 4 * ((4 * (Fintype.card ι : ℝ))⁻¹ * ∑ i, ‖f i - lpAverage μ f‖ ^ 2) := by
      unfold finiteAverage
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by norm_num)

end PL1CD.Entropy

namespace PL1CD.CylinderRefinement
open PL1.Walsh PL1.FiniteCoordinateKernels PL1CD.Entropy

theorem descendant_entropy_gap (B : Lp ℝ 1 haar →L[ℝ] Lp ℝ 1 haar)
    (S T : Finset ℕ) (hST : Disjoint S T) (a : Assignments S)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ b : Assignments T, ∀ᵐ x ∂haar,
      B (kernelL1 (S ∪ T) (merge S T a b)) x ∈ Set.Icc 0 C)
    (hmass : ∀ b : Assignments T,
      ∫ x, B (kernelL1 (S ∪ T) (merge S T a b)) x ∂haar ≤ 1) :
    finiteAverage (fun b : Assignments T =>
      ‖B (kernelL1 (S ∪ T) (merge S T a b)) - B (kernelL1 S (extend S a))‖) ^ 2 ≤
      4 * (finiteAverage (fun b : Assignments T =>
        Phi haar (B (kernelL1 (S ∪ T) (merge S T a b)))) -
          Phi haar (B (kernelL1 S (extend S a)))) := by
  have hmean : lpAverage haar (fun b : Assignments T =>
      B (kernelL1 (S ∪ T) (merge S T a b))) = B (kernelL1 S (extend S a)) :=
    mean_operator_descendants B S T hST a
  have h := bounded_lp_average_energy haar (fun b : Assignments T =>
    B (kernelL1 (S ∪ T) (merge S T a b))) C hC hbound hmass
  simpa only [hmean] using h

end PL1CD.CylinderRefinement
