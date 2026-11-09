import PL1CD.PositiveKernelAverages
import PL1CD.RealL1Order
import PL1.L1Masks

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators

namespace PL1CD.HaarPartitions
open PL1.Walsh PL1.FiniteCoordinateKernels PL1CD.PositiveHaarOperators PL1CD.L1Order

def cell (S : Finset ℕ) (a : Assignments S) : Set PL1.Walsh.Group :=
  cylinder S (extend S a)

theorem measurableSet_cell (S : Finset ℕ) (a : Assignments S) : MeasurableSet (cell S a) := by
  simp only [cell, PL1.FiniteCoordinateKernels.cylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
    measurableSet_eq_fun (measurable_pi_apply j) measurable_const))

theorem cell_pairwise_disjoint (S : Finset ℕ) : Pairwise (fun a b : Assignments S =>
    Disjoint (cell S a) (cell S b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hab ((cylinder_extend_iff S a x).mp hx |>.trans
    ((cylinder_extend_iff S b x).mp hy).symm)

def cellMask (S : Finset ℕ) (a : Assignments S) : HaarL1 →L[ℝ] HaarL1 :=
  PL1.L1Masks.mask haar (cell S a) (measurableSet_cell S a)

def cellMass (S : Finset ℕ) (a : Assignments S) : HaarL1 →L[ℝ] ℝ :=
  mass.comp (cellMask S a)

theorem norm_cellMass_apply_le (S : Finset ℕ) (a : Assignments S) (f : HaarL1) :
    ‖cellMass S a f‖ ≤ ‖cellMask S a f‖ := by
  change ‖mass (cellMask S a f)‖ ≤ ‖cellMask S a f‖
  rw [mass_apply, L1.norm_eq_integral_norm]
  exact norm_integral_le_integral_norm _

theorem cellMass_nonneg (S : Finset ℕ) (a : Assignments S) (f : HaarL1)
    (hf : Nonneg f) : 0 ≤ cellMass S a f := by
  rw [cellMass, ContinuousLinearMap.comp_apply, mass_apply]
  apply integral_nonneg_of_ae
  filter_upwards [hf, PL1.L1Masks.coeFn_mask haar (cell S a) (measurableSet_cell S a) f]
    with x hx he
  change 0 ≤ cellMask S a f x
  change cellMask S a f x = (cell S a).indicator f x at he
  rw [he]
  by_cases ha : x ∈ cell S a <;> simp [ha, hx]

def absoluteOperator (B : HaarL1 →L[ℝ] HaarL1) (S : Finset ℕ) : HaarL1 →L[ℝ] HaarL1 :=
  ∑ a : Assignments S, (cellMass S a).smulRight (absL1 (B (kernelL1 S (extend S a))))

theorem absoluteOperator_apply (B : HaarL1 →L[ℝ] HaarL1) (S : Finset ℕ) (f : HaarL1) :
    absoluteOperator B S f = ∑ a : Assignments S,
      cellMass S a f • absL1 (B (kernelL1 S (extend S a))) := by
  simp only [absoluteOperator, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

theorem norm_absoluteOperator_le (B : HaarL1 →L[ℝ] HaarL1) (S : Finset ℕ) :
    ‖absoluteOperator B S‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro f
  rw [absoluteOperator_apply]
  calc
    _ ≤ ∑ a : Assignments S, ‖cellMass S a f • absL1 (B (kernelL1 S (extend S a)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a : Assignments S, ‖cellMask S a f‖ * ‖B‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, norm_absL1]
      apply mul_le_mul (norm_cellMass_apply_le S a f) _ (norm_nonneg _) (norm_nonneg _)
      simpa only [PL1.FiniteCoordinateKernels.norm_kernelL1, mul_one] using
        B.le_opNorm (kernelL1 S (extend S a))
    _ ≤ ‖f‖ * ‖B‖ := by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg B)
      exact PL1.L1Masks.sum_norm_mask_le haar Finset.univ (cell S)
        (measurableSet_cell S) (cell_pairwise_disjoint S) f
    _ = ‖B‖ * ‖f‖ := mul_comm _ _

theorem absoluteOperator_positive (B : HaarL1 →L[ℝ] HaarL1) (S : Finset ℕ) :
    IsPositive (absoluteOperator B S) := by
  intro f hf
  rw [absoluteOperator_apply]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun a : Assignments S =>
    cellMass S a f • absL1 (B (kernelL1 S (extend S a)))),
    ae_all_iff.mpr (fun a : Assignments S => Lp.coeFn_smul (cellMass S a f)
      (absL1 (B (kernelL1 S (extend S a))))),
    ae_all_iff.mpr (fun a : Assignments S => absL1_nonneg (B (kernelL1 S (extend S a))))]
    with x hs hsm hp
  rw [hs]
  apply Finset.sum_nonneg
  intro a _
  rw [hsm a, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg (cellMass_nonneg S a f hf) (hp a)

end PL1CD.HaarPartitions
