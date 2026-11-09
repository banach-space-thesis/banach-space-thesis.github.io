import PL1.ExplicitMartingale
import PL1.FiniteCoordinateKernels

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

namespace PL1CD.FiniteExpectations

open PL1.Walsh

def outsideProjection (S : Finset ℕ) (x : PL1.Walsh.Group) : PL1.Walsh.Group :=
  fun j => if j ∈ S then 1 else x j

theorem continuous_outsideProjection (S : Finset ℕ) : Continuous (outsideProjection S) := by
  apply continuous_pi
  intro j
  by_cases hj : j ∈ S
  · simpa only [outsideProjection, hj, ite_true] using continuous_const
  · simpa only [outsideProjection, hj, ite_false] using continuous_apply j

theorem character_outsideProjection (S F : Finset ℕ) (x : PL1.Walsh.Group) :
    character F (outsideProjection S x) = character (F.filter (fun j => j ∉ S)) x := by
  classical
  unfold character
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j ∈ S <;> simp [outsideProjection, hj]

def outsideMeasure (S : Finset ℕ) : Measure PL1.Walsh.Group :=
  haar.map (outsideProjection S)

instance (S : Finset ℕ) : IsProbabilityMeasure (outsideMeasure S) := by
  unfold outsideMeasure
  infer_instance

theorem coefficient_outsideMeasure (S F : Finset ℕ) :
    coefficient (outsideMeasure S) F = if F ⊆ S then 1 else 0 := by
  classical
  rw [coefficient, outsideMeasure,
    integral_map (continuous_outsideProjection S).measurable.aemeasurable
      (continuous_character F).aestronglyMeasurable]
  simp_rw [character_outsideProjection]
  rw [PL1.Walsh.integral_character]
  have h : F.filter (fun j => j ∉ S) = ∅ ↔ F ⊆ S := by
    simp [Finset.filter_eq_empty_iff, Finset.subset_iff]
  simp only [h]

variable (𝕜 : Type*) [RCLike 𝕜]

def expectation (S : Finset ℕ) : Lp 𝕜 1 haar →L[𝕜] Lp 𝕜 1 haar :=
  convolutionL1 (outsideMeasure S)

theorem norm_expectation_le_one (S : Finset ℕ) : ‖expectation 𝕜 S‖ ≤ 1 :=
  norm_convolutionL1_le_one _

theorem expectation_character (S F : Finset ℕ) :
    expectation 𝕜 S (scalarCharacterLp 𝕜 1 F) =
      if F ⊆ S then scalarCharacterLp 𝕜 1 F else 0 := by
  classical
  rw [expectation, convolutionL1_scalarCharacter, coefficient_outsideMeasure]
  split_ifs <;> simp

theorem expectation_convolution_commute (S : Finset ℕ)
    (ν : Measure PL1.Walsh.Group) [IsProbabilityMeasure ν] :
    (expectation 𝕜 S).comp (convolutionL1 ν) =
      (convolutionL1 ν).comp (expectation 𝕜 S) := by
  classical
  apply continuousLinearMap_ext_on_scalarCharacterL1
  intro F
  simp only [ContinuousLinearMap.comp_apply, convolutionL1_scalarCharacter,
    map_smul, expectation_character]
  split_ifs
  · exact (convolutionL1_scalarCharacter ν F).symm
  · simp

def kernel (S : Finset ℕ) (x : PL1.Walsh.Group) : Lp 𝕜 1 haar :=
  PL1.ScalarRealification.ofRealL1 𝕜 (PL1.FiniteCoordinateKernels.kernelL1 S x)

theorem kernel_eq_sum (S : Finset ℕ) (x : PL1.Walsh.Group) :
    kernel 𝕜 S x = ∑ F ∈ S.powerset, (character F x : 𝕜) • scalarCharacterLp 𝕜 1 F := by
  rw [kernel, PL1.FiniteCoordinateKernels.kernelL1_eq_sum]
  simp only [map_sum, map_smul, PL1.ScalarRealification.ofRealL1_character]
  apply Finset.sum_congr rfl
  intro F _
  exact (IsScalarTower.algebraMap_smul 𝕜 (character F x) (scalarCharacterLp 𝕜 1 F)).symm

theorem kernel_range (m : ℕ) (x : PL1.Walsh.Group) :
    kernel 𝕜 (Finset.range m) x = PL1.ExplicitMartingale.kernelL1 𝕜 m x := by
  rw [kernel_eq_sum, PL1.ExplicitMartingale.kernelL1_eq_sum]

theorem expectation_kernel (S T : Finset ℕ) (x : PL1.Walsh.Group) :
    expectation 𝕜 S (kernel 𝕜 T x) = kernel 𝕜 (S ∩ T) x := by
  classical
  have hf : T.powerset.filter (fun F => F ⊆ S) = (S ∩ T).powerset := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => Finset.subset_inter h.2 h.1,
      fun h => ⟨h.trans Finset.inter_subset_right, h.trans Finset.inter_subset_left⟩⟩
  rw [kernel_eq_sum, map_sum]
  simp_rw [map_smul, expectation_character, smul_ite, smul_zero]
  rw [← Finset.sum_filter, hf, kernel_eq_sum]

theorem project_increment (S : Finset ℕ) (m n : ℕ)
    (hSn : S ⊆ Finset.range n) (hSm : Disjoint S (Finset.range m))
    (ν : Measure PL1.Walsh.Group) [IsProbabilityMeasure ν] (x : PL1.Walsh.Group) :
    expectation 𝕜 S (convolutionL1 ν
      (PL1.ExplicitMartingale.kernelL1 𝕜 n x - PL1.ExplicitMartingale.kernelL1 𝕜 m x)) =
      convolutionL1 ν (kernel 𝕜 S x - kernel 𝕜 ∅ x) := by
  have he := DFunLike.congr_fun (expectation_convolution_commute 𝕜 S ν)
    (PL1.ExplicitMartingale.kernelL1 𝕜 n x - PL1.ExplicitMartingale.kernelL1 𝕜 m x)
  change expectation 𝕜 S (convolutionL1 ν _) = convolutionL1 ν (expectation 𝕜 S _) at he
  rw [he, map_sub, ← kernel_range, ← kernel_range, expectation_kernel, expectation_kernel,
    Finset.inter_eq_left.mpr hSn, Finset.disjoint_iff_inter_eq_empty.mp hSm]

theorem norm_project_increment_le (S : Finset ℕ) (m n : ℕ)
    (hSn : S ⊆ Finset.range n) (hSm : Disjoint S (Finset.range m))
    (ν : Measure PL1.Walsh.Group) [IsProbabilityMeasure ν] (x : PL1.Walsh.Group) :
    ‖convolutionL1 (𝕜 := 𝕜) ν (kernel 𝕜 S x - kernel 𝕜 ∅ x)‖ ≤
      ‖convolutionL1 ν
        (PL1.ExplicitMartingale.kernelL1 𝕜 n x - PL1.ExplicitMartingale.kernelL1 𝕜 m x)‖ := by
  rw [← project_increment 𝕜 S m n hSn hSm ν x]
  exact ((expectation 𝕜 S).le_opNorm _).trans
    (by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (norm_expectation_le_one 𝕜 S) (norm_nonneg _)))

end PL1CD.FiniteExpectations
