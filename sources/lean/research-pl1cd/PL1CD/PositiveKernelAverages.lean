import PL1CD.PositiveHaarOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators NNReal

namespace PL1CD.PositiveHaarOperators
open PL1.Walsh PL1.FiniteCoordinateKernels PL1CD.Entropy PL1CD.CylinderRefinement

theorem mean_all_kernel (S : Finset ℕ) :
    (Fintype.card (Assignments S) : ℝ)⁻¹ •
      (∑ a : Assignments S, kernelL1 S (extend S a)) = oneL1 := by
  have he : (Fintype.card (Assignments S) : ℝ)⁻¹ •
      (∑ a : Assignments S, kernel S (extend S a)) = kernel ∅ 1 := by
    ext x
    simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul]
    rw [sum_kernel_extend, card_assignments]
    push_cast
    simp [kernel_apply]
  have h := congrArg (ContinuousMap.toLp 1 haar ℝ) he
  have h' : (Fintype.card (Assignments S) : ℝ)⁻¹ •
      (∑ a : Assignments S, kernelL1 S (extend S a)) = kernelL1 ∅ 1 := by
    simpa only [map_smul, map_sum, kernelL1] using h
  have hz : kernelL1 ∅ 1 = oneL1 := by
    simpa only [Finset.range_zero, oneL1] using kernelL1_range 0 1
  exact h'.trans hz

def mass : HaarL1 →L[ℝ] ℝ := L1.integralCLM

theorem mass_apply (f : HaarL1) : mass f = ∫ x, f x ∂haar := by
  rw [mass, ← L1.integral_eq, L1.integral_eq_integral]

theorem norm_eq_mass_of_nonneg (f : HaarL1) (hf : ∀ᵐ x ∂haar, 0 ≤ f x) :
    ‖f‖ = mass f := by
  rw [mass_apply, L1.norm_eq_integral_norm]
  exact integral_congr_ae (hf.mono (fun x hx => Real.norm_of_nonneg hx))

theorem average_norm_image (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B)
    (S : Finset ℕ) : finiteAverage (fun a : Assignments S =>
      ‖B (kernelL1 S (extend S a))‖) = ‖B oneL1‖ := by
  have hp (a : Assignments S) : ∀ᵐ x ∂haar, 0 ≤ kernelL1 S (extend S a) x := by
    filter_upwards [PL1.FiniteCoordinateKernels.coeFn_kernelL1 S (extend S a)] with x hx
    rw [hx]
    exact PL1.FiniteCoordinateKernels.kernel_nonneg S (extend S a) x
  simp_rw [norm_eq_mass_of_nonneg _ (hB _ (hp _))]
  rw [norm_eq_mass_of_nonneg _ (hB _ (coeFn_oneL1.mono (fun x hx => by simp [hx])))]
  unfold finiteAverage
  have h := congrArg (mass.comp B) (mean_all_kernel S)
  simpa only [ContinuousLinearMap.comp_apply, map_smul, map_sum, smul_eq_mul] using h

theorem finiteAverage_parent (S T : Finset ℕ) (hST : Disjoint S T)
    (F : HaarL1 → ℝ) :
    finiteAverage (fun a : Assignments (S ∪ T) => F (kernelL1 S (extend (S ∪ T) a))) =
      finiteAverage (fun a : Assignments S => F (kernelL1 S (extend S a))) := by
  rw [← finiteAverage_equiv (assignmentEquiv S T hST).symm, finiteAverage_prod]
  congr 1
  funext a
  simp only [extend_assignmentEquiv_symm, parent_kernel_merge, finiteAverage_const]

theorem positive_level_bound (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B)
    (M : ℕ → ℕ) (hM : Monotone M) (n : ℕ) :
    PL1CD.Variation.levelSeminorm ℝ HaarL1 M n B ≤ 2 * ‖B oneL1‖ := by
  let S := Finset.range (M n)
  let T := Finset.range (M (n + 1)) \ S
  have hST : Disjoint S T := Finset.disjoint_left.mpr (fun _ hs ht =>
    (Finset.mem_sdiff.mp ht).2 hs)
  have hU : S ∪ T = Finset.range (M (n + 1)) :=
    Finset.union_sdiff_of_subset (Finset.range_mono (hM (Nat.le_succ n)))
  change finiteAverage (fun a : Assignments (Finset.range (M (n + 1))) =>
    ‖B (PL1.ExplicitMartingale.kernelL1 ℝ (M (n + 1)) (extend _ a) -
      PL1.ExplicitMartingale.kernelL1 ℝ (M n) (extend _ a))‖) ≤ _
  simp_rw [map_sub, ← kernelL1_range]
  calc
    _ ≤ finiteAverage (fun a : Assignments (Finset.range (M (n + 1))) =>
        ‖B (kernelL1 (Finset.range (M (n + 1))) (extend _ a))‖ +
        ‖B (kernelL1 S (extend _ a))‖) :=
      finiteAverage_mono _ _ (fun a => norm_sub_le _ _)
    _ = 2 * ‖B oneL1‖ := by
      rw [finiteAverage_add, average_norm_image B hB, ← hU,
        finiteAverage_parent S T hST (fun f => ‖B f‖), average_norm_image B hB]
      ring

theorem noise_positive (rates : ℕ → ℝ≥0) (u : ℝ≥0) :
    IsPositive (PL1.Noise.noiseL1 ℝ rates u) := by
  intro f hf
  let ν := PL1.Noise.measure rates u
  have hb := (measurePreserving_multiply ν).quasiMeasurePreserving.ae hf
  filter_upwards [coeFn_convolutionL1 ν f, Measure.ae_ae_of_ae_prod hb]
    with x hx hbound
  change 0 ≤ convolutionL1 ν f x
  rw [hx]
  exact integral_nonneg_of_ae hbound

theorem IsPositive.comp {B D : HaarL1 →L[ℝ] HaarL1}
    (hB : IsPositive B) (hD : IsPositive D) : IsPositive (D.comp B) :=
  fun f hf => hD (B f) (hB f hf)

theorem norm_noise_nonneg (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    (f : HaarL1) (hf : ∀ᵐ x ∂haar, 0 ≤ f x) :
    ‖PL1.Noise.noiseL1 ℝ rates u f‖ = ‖f‖ := by
  rw [norm_eq_mass_of_nonneg _ (noise_positive rates u f hf),
    norm_eq_mass_of_nonneg _ hf, mass_apply, mass_apply]
  exact integral_convolutionL1 _ f

theorem positive_noise_level_bound (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B)
    (M : ℕ → ℕ) (hM : Monotone M) (n : ℕ) :
    PL1CD.Variation.levelSeminorm ℝ HaarL1 M n
      ((PL1.Noise.noiseL1 ℝ rates u).comp B) ≤ 2 * ‖B oneL1‖ := by
  have h := positive_level_bound _ (hB.comp (noise_positive rates u)) M hM n
  have hone : ∀ᵐ x ∂haar, 0 ≤ oneL1 x :=
    coeFn_oneL1.mono (fun x hx => by rw [hx]; norm_num)
  change PL1CD.Variation.levelSeminorm ℝ HaarL1 M n
    ((PL1.Noise.noiseL1 ℝ rates u).comp B) ≤
      2 * ‖PL1.Noise.noiseL1 ℝ rates u (B oneL1)‖ at h
  rwa [norm_noise_nonneg rates u (B oneL1) (hB _ hone)] at h

end PL1CD.PositiveHaarOperators
