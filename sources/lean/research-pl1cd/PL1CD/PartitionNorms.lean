import PL1CD.PositiveKernelAverages
import PL1.L1Sum
import PL1.DyadicCoordinateDomination

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped BigOperators Topology

namespace PL1CD.PartitionNorms
open PL1.Walsh PL1.FiniteCoordinateKernels PL1CD.Entropy PL1CD.CylinderRefinement

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def partitionNorm (B : Variation.HaarL1 ℝ →L[ℝ] Y) (m : ℕ) : ℝ :=
  finiteAverage (fun a : Assignments (Finset.range m) =>
    ‖B (kernelL1 (Finset.range m) (extend _ a))‖)

theorem partitionNorm_nonneg (B : Variation.HaarL1 ℝ →L[ℝ] Y) (m : ℕ) :
    0 ≤ partitionNorm B m := finiteAverage_nonneg _ (fun _ => norm_nonneg _)

theorem average_norm_refinement (B : Variation.HaarL1 ℝ →L[ℝ] Y)
    (S T : Finset ℕ) (hST : Disjoint S T) :
    finiteAverage (fun a : Assignments S => ‖B (kernelL1 S (extend S a))‖) ≤
      finiteAverage (fun a : Assignments (S ∪ T) =>
        ‖B (kernelL1 (S ∪ T) (extend _ a))‖) := by
  rw [← finiteAverage_equiv (assignmentEquiv S T hST).symm, finiteAverage_prod]
  apply finiteAverage_mono
  intro a
  rw [← mean_operator_descendants B S T hST a, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (Fintype.card (Assignments T) : ℝ)⁻¹)]
  exact (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans_eq
    (by simp only [finiteAverage, extend_assignmentEquiv_symm])

theorem partitionNorm_monotone (B : Variation.HaarL1 ℝ →L[ℝ] Y) :
    Monotone (partitionNorm B) := by
  apply monotone_nat_of_le_succ
  intro m
  have hd : Disjoint (Finset.range m) {m} := by simp
  have hu : Finset.range m ∪ {m} = Finset.range (m + 1) := by
    rw [Finset.range_add_one]; ext j; simp
  have h := average_norm_refinement B (Finset.range m) {m} hd
  rw [hu] at h
  exact h

theorem level_le_partitionNorm (B : Variation.HaarL1 ℝ →L[ℝ] Y)
    (M : ℕ → ℕ) (hM : Monotone M) (n : ℕ) :
    Variation.levelSeminorm ℝ Y M n B ≤ partitionNorm B (M (n + 1)) +
      partitionNorm B (M n) := by
  let S := Finset.range (M n)
  let T := Finset.range (M (n + 1)) \ S
  have hd : Disjoint S T := Finset.disjoint_left.mpr (fun _ hs ht =>
    (Finset.mem_sdiff.mp ht).2 hs)
  have hu : S ∪ T = Finset.range (M (n + 1)) :=
    Finset.union_sdiff_of_subset (Finset.range_mono (hM (Nat.le_succ n)))
  change finiteAverage (fun a : Assignments (Finset.range (M (n + 1))) =>
    ‖B (PL1.ExplicitMartingale.kernelL1 ℝ (M (n + 1)) (extend _ a) -
      PL1.ExplicitMartingale.kernelL1 ℝ (M n) (extend _ a))‖) ≤ _
  simp_rw [map_sub, ← kernelL1_range]
  calc
    _ ≤ finiteAverage (fun a : Assignments (Finset.range (M (n + 1))) =>
        ‖B (kernelL1 (Finset.range (M (n + 1))) (extend _ a))‖ +
        ‖B (kernelL1 S (extend _ a))‖) :=
      finiteAverage_mono _ _ (fun _ => norm_sub_le _ _)
    _ = _ := by
      rw [finiteAverage_add]
      congr 1
      rw [← hu]
      exact PositiveHaarOperators.finiteAverage_parent S T hd (fun f => ‖B f‖)

theorem finiteAverage_finsetSum {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (f : ι → κ → ℝ) :
    finiteAverage (fun a => ∑ i ∈ s, f a i) = ∑ i ∈ s, finiteAverage (fun a => f a i) := by
  simp only [finiteAverage]
  rw [Finset.sum_comm, Finset.mul_sum]

def coordinateOperator (U : Variation.HaarL1 ℝ →L[ℝ] PL1.L1Sum Y) (i : ℕ) :
    Variation.HaarL1 ℝ →L[ℝ] Y := (lp.evalCLM ℝ (fun _ : ℕ => Y) 1 i).comp U

theorem coordinate_partition_bound (U : Variation.HaarL1 ℝ →L[ℝ] PL1.L1Sum Y)
    (m : ℕ) (s : Finset ℕ) :
    ∑ i ∈ s, partitionNorm (coordinateOperator U i) m ≤ ‖U‖ := by
  unfold partitionNorm
  rw [← finiteAverage_finsetSum]
  calc
    _ ≤ finiteAverage (fun _a : Assignments (Finset.range m) => ‖U‖) := by
      apply finiteAverage_mono
      intro a
      let x := U (kernelL1 (Finset.range m) (extend _ a))
      change ∑ i ∈ s, ‖x i‖ ≤ ‖U‖
      calc
        _ ≤ ∑' i, ‖x i‖ := (PL1.L1Sum.summable_norm x).sum_le_tsum s (fun _ _ => norm_nonneg _)
        _ = ‖x‖ := (PL1.L1Sum.norm_eq_tsum x).symm
        _ ≤ ‖U‖ := by
          have h := U.le_opNorm (kernelL1 (Finset.range m) (extend _ a))
          simpa only [x, norm_kernelL1, mul_one] using h
    _ = ‖U‖ := finiteAverage_const _

theorem exists_coordinate_majorant (U : Variation.HaarL1 ℝ →L[ℝ] PL1.L1Sum Y) :
    ∃ b : ℕ → ℝ, Summable b ∧ (∀ i, 0 ≤ b i) ∧
      (∀ m i, partitionNorm (coordinateOperator U i) m ≤ b i) := by
  obtain ⟨b, hb, hb0, hle, _⟩ := PL1.DyadicCoordinateDomination.exists_summable_majorant
    (fun m i => partitionNorm (coordinateOperator U i) m) ‖U‖
    (fun m i => partitionNorm_nonneg _ _) (fun i => partitionNorm_monotone _)
    (coordinate_partition_bound U)
  exact ⟨b, hb, hb0, hle⟩

end PL1CD.PartitionNorms
