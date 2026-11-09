import PL1CD.PartitionEntropy
import PL1CD.Variation

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PL1CD.Entropy

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]

omit [Nonempty ι] [Nonempty κ] in
theorem finiteAverage_equiv (e : ι ≃ κ) (f : κ → ℝ) :
    finiteAverage (fun i => f (e i)) = finiteAverage f := by
  unfold finiteAverage
  rw [Fintype.card_congr e, e.sum_comp]

omit [Nonempty ι] in
theorem finiteAverage_sub (f g : ι → ℝ) :
    finiteAverage (fun i => f i - g i) = finiteAverage f - finiteAverage g := by
  simp only [finiteAverage, Finset.sum_sub_distrib, mul_sub]

theorem finiteAverage_mono (f g : ι → ℝ) (hfg : ∀ i, f i ≤ g i) :
    finiteAverage f ≤ finiteAverage g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hfg i)) (by positivity)

end PL1CD.Entropy

namespace PL1CD.CylinderRefinement
open PL1.Walsh PL1.FiniteCoordinateKernels PL1CD.Entropy

theorem kernelL1_congr (S : Finset ℕ) (x y : PL1.Walsh.Group)
    (hxy : ∀ j ∈ S, x j = y j) : kernelL1 S x = kernelL1 S y := by
  unfold kernelL1
  congr 1
  ext z
  simp only [kernel_apply]
  apply Finset.sum_congr rfl
  intro F hF
  congr 1
  unfold character
  exact Finset.prod_congr rfl (fun j hj => congrArg signValue
    (hxy j ((Finset.mem_powerset.mp hF) hj)))

theorem extend_assignmentEquiv_symm (S T : Finset ℕ) (hST : Disjoint S T)
    (a : Assignments S) (b : Assignments T) :
    extend (S ∪ T) ((assignmentEquiv S T hST).symm (a, b)) = merge S T a b := by
  funext j
  by_cases hs : j ∈ S <;> by_cases ht : j ∈ T <;>
    simp [PL1.FiniteCoordinateKernels.extend, merge, assignmentEquiv, hs, ht]

theorem parent_kernel_merge (S T : Finset ℕ)
    (a : Assignments S) (b : Assignments T) :
    kernelL1 S (merge S T a b) = kernelL1 S (extend S a) := by
  apply kernelL1_congr
  intro j hj
  exact (merge_left S T a b ⟨j, hj⟩).trans (extend_apply S a ⟨j, hj⟩).symm

def averagePhi (B : Lp ℝ 1 haar →L[ℝ] Lp ℝ 1 haar) (S : Finset ℕ) : ℝ :=
  finiteAverage (fun a : Assignments S => Phi haar (B (kernelL1 S (extend S a))))

def refinementVariation (B : Lp ℝ 1 haar →L[ℝ] Lp ℝ 1 haar) (S T : Finset ℕ) : ℝ :=
  finiteAverage (fun ab : Assignments S × Assignments T =>
    ‖B (kernelL1 (S ∪ T) (merge S T ab.1 ab.2)) - B (kernelL1 S (extend S ab.1))‖)

theorem averagePhi_union (B : Lp ℝ 1 haar →L[ℝ] Lp ℝ 1 haar)
    (S T : Finset ℕ) (hST : Disjoint S T) :
    averagePhi B (S ∪ T) = finiteAverage (fun a : Assignments S =>
      finiteAverage (fun b : Assignments T => Phi haar (B (kernelL1 (S ∪ T) (merge S T a b))))) := by
  unfold averagePhi
  rw [← finiteAverage_equiv (assignmentEquiv S T hST).symm,
    finiteAverage_prod]
  congr 1
  funext a
  congr 1
  funext b
  rw [extend_assignmentEquiv_symm S T hST a b]

theorem refinement_energy_le (B : Lp ℝ 1 haar →L[ℝ] Lp ℝ 1 haar)
    (S T : Finset ℕ) (hST : Disjoint S T) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (a : Assignments S) (b : Assignments T), ∀ᵐ x ∂haar,
      B (kernelL1 (S ∪ T) (merge S T a b)) x ∈ Set.Icc 0 C)
    (hmass : ∀ (a : Assignments S) (b : Assignments T),
      ∫ x, B (kernelL1 (S ∪ T) (merge S T a b)) x ∂haar ≤ 1) :
    refinementVariation B S T ^ 2 ≤ 4 * (averagePhi B (S ∪ T) - averagePhi B S) := by
  unfold refinementVariation
  rw [finiteAverage_prod]
  calc
    _ ≤ finiteAverage (fun a : Assignments S =>
        finiteAverage (fun b : Assignments T =>
          ‖B (kernelL1 (S ∪ T) (merge S T a b)) - B (kernelL1 S (extend S a))‖) ^ 2) :=
      finiteAverage_sq_le _
    _ ≤ finiteAverage (fun a : Assignments S =>
        4 * (finiteAverage (fun b : Assignments T =>
          Phi haar (B (kernelL1 (S ∪ T) (merge S T a b)))) -
            Phi haar (B (kernelL1 S (extend S a))))) :=
      finiteAverage_mono _ _ (fun a => descendant_entropy_gap B S T hST a C hC
        (hbound a) (hmass a))
    _ = _ := by
      rw [finiteAverage_mul, finiteAverage_sub, ← averagePhi_union B S T hST]
      rfl

theorem refinementVariation_eq_finiteVariation (B : Lp ℝ 1 haar →L[ℝ] Lp ℝ 1 haar)
    (S T : Finset ℕ) (hST : Disjoint S T) :
    refinementVariation B S T = PL1CD.Variation.finiteVariation
      (fun a : Assignments (S ∪ T) => kernelL1 (S ∪ T) (extend (S ∪ T) a))
      (fun a => kernelL1 S (extend (S ∪ T) a)) B := by
  change refinementVariation B S T = finiteAverage
    (fun a : Assignments (S ∪ T) => ‖B
      (kernelL1 (S ∪ T) (extend (S ∪ T) a) - kernelL1 S (extend (S ∪ T) a))‖)
  rw [← finiteAverage_equiv (assignmentEquiv S T hST).symm]
  unfold refinementVariation
  congr 1
  funext ab
  rcases ab with ⟨a, b⟩
  rw [extend_assignmentEquiv_symm S T hST a b, map_sub, parent_kernel_merge S T a b]

theorem kernelL1_range (m : ℕ) (s : PL1.Walsh.Group) :
    kernelL1 (Finset.range m) s = PL1.ExplicitMartingale.kernelL1 ℝ m s := by
  apply Lp.ext
  filter_upwards [coeFn_kernelL1 (Finset.range m) s,
    PL1.ExplicitMartingale.coeFn_kernelL1 ℝ m s] with x hx hy
  rw [hx, hy]
  rfl

def levelEntropy (B : Lp ℝ 1 haar →L[ℝ] Lp ℝ 1 haar) (M : ℕ → ℕ) (n : ℕ) : ℝ :=
  averagePhi B (Finset.range (M n))

theorem level_energy_le (B : Lp ℝ 1 haar →L[ℝ] Lp ℝ 1 haar) (M : ℕ → ℕ)
    (n : ℕ) (hM : M n ≤ M (n + 1)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ a : Assignments (Finset.range (M (n + 1))), ∀ᵐ x ∂haar,
      B (PL1.ExplicitMartingale.kernelL1 ℝ (M (n + 1)) (extend _ a)) x ∈ Set.Icc 0 C)
    (hmass : ∀ a : Assignments (Finset.range (M (n + 1))),
      ∫ x, B (PL1.ExplicitMartingale.kernelL1 ℝ (M (n + 1)) (extend _ a)) x ∂haar ≤ 1) :
    PL1CD.Variation.levelSeminorm ℝ (Lp ℝ 1 haar) M n B ^ 2 ≤
      4 * (levelEntropy B M (n + 1) - levelEntropy B M n) := by
  let S := Finset.range (M n)
  let T := Finset.range (M (n + 1)) \ S
  have hST : Disjoint S T := Finset.disjoint_left.mpr (fun _ hs ht =>
    (Finset.mem_sdiff.mp ht).2 hs)
  have hU : S ∪ T = Finset.range (M (n + 1)) :=
    Finset.union_sdiff_of_subset (Finset.range_mono hM)
  have hb (a : Assignments S) (b : Assignments T) : ∀ᵐ x ∂haar,
      B (kernelL1 (S ∪ T) (merge S T a b)) x ∈ Set.Icc 0 C := by
    have he := hbound (fun j => merge S T a b j)
    rw [← kernelL1_range] at he
    have hk : kernelL1 (Finset.range (M (n + 1)))
        (extend (Finset.range (M (n + 1))) (fun j : Finset.range (M (n + 1)) =>
          merge S T a b j)) = kernelL1 (S ∪ T) (merge S T a b) := by
      rw [hU]
      apply kernelL1_congr
      intro j hj
      exact extend_apply _ _ ⟨j, hj⟩
    rwa [hk] at he
  have hm (a : Assignments S) (b : Assignments T) :
      ∫ x, B (kernelL1 (S ∪ T) (merge S T a b)) x ∂haar ≤ 1 := by
    have he := hmass (fun j => merge S T a b j)
    rw [← kernelL1_range] at he
    have hk : kernelL1 (Finset.range (M (n + 1)))
        (extend (Finset.range (M (n + 1))) (fun j : Finset.range (M (n + 1)) =>
          merge S T a b j)) = kernelL1 (S ∪ T) (merge S T a b) := by
      rw [hU]
      apply kernelL1_congr
      intro j hj
      exact extend_apply _ _ ⟨j, hj⟩
    rwa [hk] at he
  have h := refinement_energy_le B S T hST C hC hb hm
  rw [refinementVariation_eq_finiteVariation B S T hST] at h
  dsimp [levelEntropy]
  rw [hU] at h
  dsimp [S] at h
  simpa only [PL1CD.Variation.levelSeminorm, kernelL1_range] using h

end PL1CD.CylinderRefinement
