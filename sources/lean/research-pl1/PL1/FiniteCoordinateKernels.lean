import PL1.ExplicitMartingale

/-!
# Finite-coordinate probability kernels

Arbitrary finite coordinate sets are allowed, so all constructions apply
beyond a prescribed initial segment. Convolution with an arbitrary probability
measure gives a nonnegative finite Walsh polynomial of Haar integral one.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace PL1.FiniteCoordinateKernels
open Walsh

def cylinder (S : Finset ℕ) (s : Walsh.Group) : Set Walsh.Group :=
  {x | ∀ j ∈ S, x j = s j}

def kernel (S : Finset ℕ) (s : Walsh.Group) : C(Walsh.Group, ℝ) :=
  ∑ F ∈ S.powerset, character F s • characterContinuous F

theorem kernel_apply (S : Finset ℕ) (s x : Walsh.Group) :
    kernel S s x = ∑ F ∈ S.powerset, character F s * character F x := by
  simp only [kernel, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, characterContinuous, ContinuousMap.coe_mk]

theorem kernel_eq_indicator (S : Finset ℕ) (s x : Walsh.Group) :
    kernel S s x = (cylinder S s).indicator (fun _ => (2 : ℝ) ^ S.card) x := by
  classical
  have heq : kernel S s x = ∏ j ∈ S, (1 + signValue (s j * x j)) := by
    rw [kernel_apply, Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro F hF
    exact (character_mul F s x).symm
  rw [heq]
  simp_rw [ExplicitMartingale.one_add_sign_mul]
  by_cases hx : x ∈ cylinder S s
  · rw [Set.indicator_of_mem hx]
    simp only [Finset.prod_congr rfl (fun j hj => ite_eq_left (hx j hj)), Finset.prod_const]
  · rw [Set.indicator_of_notMem hx]
    have h : ∃ j ∈ S, x j ≠ s j := by
      simpa only [cylinder, Set.mem_ofPred_eq, not_forall, exists_prop] using hx
    obtain ⟨j, hj, hneq⟩ := h
    exact Finset.prod_eq_zero hj (ite_eq_right hneq)

theorem kernel_nonneg (S : Finset ℕ) (s x : Walsh.Group) : 0 ≤ kernel S s x := by
  rw [kernel_eq_indicator]
  exact Set.indicator_nonneg (fun _ _ => by positivity) _

theorem integral_kernel (S : Finset ℕ) (s : Walsh.Group) :
    ∫ x, kernel S s x ∂haar = 1 := by
  simp_rw [kernel_apply]
  rw [integral_finsetSum _ (fun F _ => (integrable_character F).const_mul _)]
  simp_rw [integral_const_mul, Walsh.integral_character]
  simp

def kernelL1 (S : Finset ℕ) (s : Walsh.Group) : Lp ℝ 1 haar :=
  ContinuousMap.toLp 1 haar ℝ (kernel S s)

theorem coeFn_kernelL1 (S : Finset ℕ) (s : Walsh.Group) :
    kernelL1 S s =ᵐ[haar] kernel S s := ContinuousMap.coeFn_toLp haar _

theorem kernelL1_eq_sum (S : Finset ℕ) (s : Walsh.Group) :
    kernelL1 S s = ∑ F ∈ S.powerset, character F s • characterLp 1 F := by
  simp only [kernelL1, kernel, map_sum, map_smul, toLp_characterContinuous]

theorem norm_kernelL1 (S : Finset ℕ) (s : Walsh.Group) : ‖kernelL1 S s‖ = 1 := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ x, kernel S s x ∂haar := by
      apply integral_congr_ae
      filter_upwards [coeFn_kernelL1 S s] with x hx
      rw [hx, Real.norm_of_nonneg (kernel_nonneg S s x)]
    _ = 1 := integral_kernel S s

def density (ν : Measure Walsh.Group) (S : Finset ℕ) : C(Walsh.Group, ℝ) :=
  ∑ F ∈ S.powerset, coefficient ν F • characterContinuous F

theorem density_apply (ν : Measure Walsh.Group) (S : Finset ℕ) (x : Walsh.Group) :
    density ν S x = ∑ F ∈ S.powerset, coefficient ν F * character F x := by
  simp only [density, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, characterContinuous, ContinuousMap.coe_mk]

theorem density_eq_integral (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (S : Finset ℕ) (x : Walsh.Group) :
    density ν S x = ∫ y, kernel S y x ∂ν := by
  simp_rw [density_apply, kernel_apply]
  have hchar (F : Finset ℕ) : Integrable (character F) ν :=
    (characterContinuous F).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun F _ => (hchar F).mul_const _)]
  simp only [integral_mul_const, coefficient]

theorem density_nonneg (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (S : Finset ℕ) (x : Walsh.Group) : 0 ≤ density ν S x := by
  rw [density_eq_integral]
  exact integral_nonneg (fun y => kernel_nonneg S y x)

theorem integral_density (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (S : Finset ℕ) : ∫ x, density ν S x ∂haar = 1 := by
  simp_rw [density_apply]
  rw [integral_finsetSum _ (fun F _ => (integrable_character F).const_mul _)]
  simp_rw [integral_const_mul, Walsh.integral_character]
  simp [coefficient]

theorem density_eq_convolution (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (S : Finset ℕ) :
    ContinuousMap.toLp 1 haar ℝ (density ν S) = convolutionL1 ν (kernelL1 S 1) := by
  simp only [density, map_sum, map_smul, toLp_characterContinuous,
    kernelL1_eq_sum, character_one, one_smul, convolutionL1_character]

/-- A set genuinely depends only on the displayed finite coordinates. -/
def DependsOn (S : Finset ℕ) (B : Set Walsh.Group) : Prop :=
  ∀ x y : Walsh.Group, (∀ j ∈ S, x j = y j) → (x ∈ B ↔ y ∈ B)

theorem indicator_kernel (S : Finset ℕ) {B : Set Walsh.Group} (hB : DependsOn S B)
    (y x : Walsh.Group) :
    B.indicator (kernel S y) x = B.indicator (fun _ => kernel S y x) y := by
  classical
  by_cases hxy : x ∈ cylinder S y
  · have hiff := hB x y hxy
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hiff.mpr hy)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun hx => hy (hiff.mp hx))]
  · have hk : kernel S y x = 0 := by
      rw [kernel_eq_indicator, Set.indicator_of_notMem hxy]
    simp only [Set.indicator_apply, hk, ite_self]

theorem setIntegral_kernel (S : Finset ℕ) {B : Set Walsh.Group}
    (hBm : MeasurableSet B) (hB : DependsOn S B) (y : Walsh.Group) :
    ∫ x in B, kernel S y x ∂haar = B.indicator (fun _ => (1 : ℝ)) y := by
  classical
  rw [← integral_indicator hBm]
  simp_rw [indicator_kernel S hB y]
  by_cases hy : y ∈ B
  · simp only [Set.indicator_of_mem hy, integral_kernel]
  · simp only [integral_zero, Set.indicator_of_notMem hy]

theorem setIntegral_density (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (S : Finset ℕ) {B : Set Walsh.Group} (hBm : MeasurableSet B) (hB : DependsOn S B) :
    ∫ x in B, density ν S x ∂haar = ν.real B := by
  have hc : Continuous (fun z : Walsh.Group × Walsh.Group => kernel S z.2 z.1) := by
    simp only [kernel_apply]
    exact continuous_finsetSum _ (fun F _ =>
      ((characterContinuous F).continuous.comp continuous_snd).mul
        ((characterContinuous F).continuous.comp continuous_fst))
  have hi : Integrable (fun z : Walsh.Group × Walsh.Group => kernel S z.2 z.1)
      ((haar.restrict B).prod ν) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [density_eq_integral]
  rw [integral_integral_swap hi]
  simp_rw [setIntegral_kernel S hBm hB]
  rw [integral_indicator hBm, integral_const]
  simp

end PL1.FiniteCoordinateKernels
