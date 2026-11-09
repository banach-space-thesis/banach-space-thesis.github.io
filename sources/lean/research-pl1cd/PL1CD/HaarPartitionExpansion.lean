import PL1CD.HaarPartitionAlgebra
import PL1CD.CubeApproximation

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators

namespace PL1CD.HaarPartitions
open PL1.Walsh PL1.FiniteCoordinateKernels PL1CD.PositiveHaarOperators PL1CD.L1Order
open PL1.Bonami PL1CD.Entropy

theorem scalarCharacter_atom_sum (S F : Finset ℕ) (hF : F ⊆ S) :
    scalarCharacterLp ℝ 1 F = ∑ a : Assignments S,
      character F (extend S a) • atom S a := by
  classical
  apply Lp.ext
  filter_upwards [coeFn_scalarCharacterLp ℝ 1 F,
    Lp.coeFn_fun_finsetSum Finset.univ (fun a : Assignments S =>
      character F (extend S a) • atom S a),
    ae_all_iff.mpr (fun a : Assignments S => Lp.coeFn_smul (character F (extend S a)) (atom S a)),
    ae_all_iff.mpr (fun a : Assignments S => coeFn_atom S a)] with x hx hs hsm ha
  rw [hx, hs]
  simp_rw [hsm, Pi.smul_apply, smul_eq_mul, ha]
  simp only [cell]
  change character F x = _
  rw [Finset.sum_eq_single (fun j : S => x j)]
  · rw [Set.indicator_of_mem ((cylinder_extend_iff S _ x).mpr rfl), mul_one]
    unfold character
    apply Finset.prod_congr rfl
    intro j hj
    rw [extend_apply S _ ⟨j, hF hj⟩]
  · intro a _ ha
    rw [Set.indicator_of_notMem (fun hx => ha ((cylinder_extend_iff S a x).mp hx)), mul_zero]
  · simp

theorem liftLp_atom_sum (n : ℕ) (g : Cube n → ℝ) :
    liftLp n g = ∑ a : Assignments (Finset.range n),
      g (sample n (extend (Finset.range n) a)) • atom (Finset.range n) a := by
  classical
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar (liftContinuous n g),
    Lp.coeFn_fun_finsetSum Finset.univ (fun a : Assignments (Finset.range n) =>
      g (sample n (extend (Finset.range n) a)) • atom (Finset.range n) a),
    ae_all_iff.mpr (fun a : Assignments (Finset.range n) =>
      Lp.coeFn_smul (g (sample n (extend (Finset.range n) a))) (atom (Finset.range n) a)),
    ae_all_iff.mpr (fun a : Assignments (Finset.range n) => coeFn_atom (Finset.range n) a)]
    with x hx hs hsm ha
  change liftLp n g x = _
  change liftLp n g x = g (sample n x) at hx
  rw [hx, hs]
  simp_rw [hsm, Pi.smul_apply, smul_eq_mul, ha]
  simp only [cell]
  rw [Finset.sum_eq_single (fun j : Finset.range n => x j)]
  · rw [Set.indicator_of_mem ((cylinder_extend_iff _ _ x).mpr rfl), mul_one]
    congr 1
    apply sample_congr
    intro j hj
    exact (extend_apply (Finset.range n) (fun j : Finset.range n => x j)
      ⟨j, Finset.mem_range.mpr hj⟩).symm
  · intro a _ ha
    rw [Set.indicator_of_notMem (fun hx => ha ((cylinder_extend_iff _ a x).mp hx)), mul_zero]
  · simp

theorem liftLp_nonneg_iff (n : ℕ) (g : Cube n → ℝ) :
    Nonneg (liftLp n g) ↔ ∀ x, 0 ≤ g x := by
  constructor
  · intro h
    have he : ∀ᵐ x ∂haar, 0 ≤ g (sample n x) := by
      filter_upwards [h, ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar (liftContinuous n g)]
        with x hx hg
      change liftLp n g x = g (sample n x) at hg
      rwa [hg] at hx
    have hc := ((isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).preimage
      (continuous_lift n g)).ae_eq_univ_iff_eq.mp (ae_eq_univ.mpr he)
    intro x
    obtain ⟨y, rfl⟩ := sample_surjective n x
    have hy : y ∈ (fun x => g (sample n x)) ⁻¹' Set.Ici 0 := hc.symm ▸ Set.mem_univ y
    exact hy
  · intro h
    filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar (liftContinuous n g)]
      with x hx
    change liftLp n g x = g (sample n x) at hx
    rw [hx]
    exact h _

end PL1CD.HaarPartitions
