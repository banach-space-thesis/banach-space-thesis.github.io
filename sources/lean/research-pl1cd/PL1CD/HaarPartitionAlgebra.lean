import PL1CD.HaarPartitions

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators

namespace PL1CD.HaarPartitions
open PL1.Walsh PL1.FiniteCoordinateKernels PL1CD.PositiveHaarOperators PL1CD.L1Order
open PL1CD.CylinderRefinement

def atom (S : Finset ℕ) (a : Assignments S) : HaarL1 :=
  ((2 : ℝ) ^ S.card)⁻¹ • kernelL1 S (extend S a)

theorem coeFn_atom (S : Finset ℕ) (a : Assignments S) :
    atom S a =ᵐ[haar] (cell S a).indicator (fun _ => (1 : ℝ)) := by
  filter_upwards [Lp.coeFn_smul (((2 : ℝ) ^ S.card)⁻¹) (kernelL1 S (extend S a)),
    PL1.FiniteCoordinateKernels.coeFn_kernelL1 S (extend S a)] with x hs hk
  change (((2 : ℝ) ^ S.card)⁻¹ • kernelL1 S (extend S a)) x = _
  rw [hs, Pi.smul_apply, smul_eq_mul, hk, kernel_eq_indicator]
  by_cases hx : x ∈ cell S a
  · simp only [cell] at hx
    simp [cell, hx]
  · simp only [cell] at hx
    simp [cell, hx]

theorem atom_nonneg (S : Finset ℕ) (a : Assignments S) : Nonneg (atom S a) := by
  filter_upwards [coeFn_atom S a] with x hx
  rw [hx]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem norm_atom (S : Finset ℕ) (a : Assignments S) : ‖atom S a‖ = ((2 : ℝ) ^ S.card)⁻¹ := by
  rw [atom, norm_smul, PL1.FiniteCoordinateKernels.norm_kernelL1, mul_one,
    Real.norm_of_nonneg (by positivity)]

theorem mass_atom (S : Finset ℕ) (a : Assignments S) : mass (atom S a) = ((2 : ℝ) ^ S.card)⁻¹ := by
  rw [← norm_eq_mass_of_nonneg _ (atom_nonneg S a), norm_atom]

def restrict (S T : Finset ℕ) (hTS : T ⊆ S) (a : Assignments S) : Assignments T :=
  fun j => a ⟨j, hTS j.property⟩

theorem cellMask_atom (S T : Finset ℕ) (hTS : T ⊆ S)
    (a : Assignments S) (b : Assignments T) :
    cellMask S a (atom T b) = if restrict S T hTS a = b then atom S a else 0 := by
  apply Lp.ext
  filter_upwards [PL1.L1Masks.coeFn_mask haar (cell S a) (measurableSet_cell S a) (atom T b),
    coeFn_atom S a, coeFn_atom T b, Lp.coeFn_zero ℝ 1 haar] with x hm hs ht hz
  change PL1.L1Masks.mask haar (cell S a) _ (atom T b) x = _
  rw [hm]
  by_cases hab : restrict S T hTS a = b
  · rw [if_pos hab, hs]
    by_cases hx : x ∈ cell S a
    · have hy : x ∈ cell T b := by
        apply (cylinder_extend_iff T b x).mpr
        rw [← hab]
        funext j
        exact congrFun ((cylinder_extend_iff S a x).mp hx) ⟨j, hTS j.property⟩
      rw [Set.indicator_of_mem hx, ht, Set.indicator_of_mem hy,
        Set.indicator_of_mem hx]
    · simp [hx]
  · rw [if_neg hab, hz, Pi.zero_apply]
    by_cases hx : x ∈ cell S a
    · have hy : x ∉ cell T b := by
        intro hy
        apply hab
        funext j
        exact (congrFun ((cylinder_extend_iff S a x).mp hx) ⟨j, hTS j.property⟩).trans
          (congrFun ((cylinder_extend_iff T b x).mp hy) j).symm
      rw [Set.indicator_of_mem hx, ht, Set.indicator_of_notMem hy]
    · simp [hx]

theorem cellMass_atom (S T : Finset ℕ) (hTS : T ⊆ S)
    (a : Assignments S) (b : Assignments T) :
    cellMass S a (atom T b) =
      if restrict S T hTS a = b then ((2 : ℝ) ^ S.card)⁻¹ else 0 := by
  simp only [cellMass, ContinuousLinearMap.comp_apply, cellMask_atom S T hTS a b]
  split_ifs <;> simp only [mass_atom, map_zero]

theorem absL1_nonneg_smul (c : ℝ) (hc : 0 ≤ c) (f : HaarL1) :
    absL1 (c • f) = c • absL1 f := by
  apply Lp.ext
  filter_upwards [coeFn_absL1 (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_smul c (absL1 f), coeFn_absL1 f] with x hab hs ha hf
  rw [hab, hs, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc,
    ha, Pi.smul_apply, smul_eq_mul, hf]

theorem absoluteOperator_atom (B : HaarL1 →L[ℝ] HaarL1)
    (S T : Finset ℕ) (hTS : T ⊆ S) (b : Assignments T) :
    absoluteOperator B S (atom T b) = ∑ a : Assignments S,
      if restrict S T hTS a = b then absL1 (B (atom S a)) else 0 := by
  rw [absoluteOperator_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [cellMass_atom S T hTS a b]
  by_cases h : restrict S T hTS a = b
  · rw [if_pos h, if_pos h, atom, map_smul, absL1_nonneg_smul _ (by positivity)]
  · simp [h]

theorem sum_descendant_atom (S T : Finset ℕ) (hST : Disjoint S T) (a : Assignments S) :
    (∑ b : Assignments T, atom (S ∪ T) ((assignmentEquiv S T hST).symm (a, b))) = atom S a := by
  simp only [atom, extend_assignmentEquiv_symm]
  rw [← Finset.smul_sum]
  have h := mean_descendant_kernelL1 S T hST a
  rw [card_assignments] at h
  push_cast at h
  have h2 : (2 : ℝ) ^ T.card ≠ 0 := by positivity
  calc
    _ = ((2 : ℝ) ^ S.card)⁻¹ •
        (((2 : ℝ) ^ T.card)⁻¹ • ∑ b : Assignments T,
          kernelL1 (S ∪ T) (merge S T a b)) := by
      rw [smul_smul, Finset.card_union_of_disjoint hST, pow_add, mul_inv_rev]
      congr 1
      ring
    _ = _ := by rw [h]

end PL1CD.HaarPartitions
