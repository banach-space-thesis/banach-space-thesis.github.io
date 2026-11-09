import PL1.FiniteCoordinateKernels
import PL1.ResolventAlmostInvariant

/-! # Finite translated probability densities and their exact average -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace PL1.FiniteCoordinateKernels
open Walsh Noise

abbrev Assignments (S : Finset ℕ) := S → Sign

def extend (S : Finset ℕ) (a : Assignments S) : Walsh.Group :=
  fun j => if h : j ∈ S then a ⟨j, h⟩ else 1

@[simp] theorem extend_apply (S : Finset ℕ) (a : Assignments S) (j : S) :
    extend S a j = a j := by simp [extend]

theorem cylinder_extend_iff (S : Finset ℕ) (a : Assignments S) (x : Walsh.Group) :
    x ∈ cylinder S (extend S a) ↔ a = fun j : S => x j := by
  constructor
  · intro hx
    funext j
    exact ((extend_apply S a j).symm.trans (hx j j.property).symm)
  · rintro rfl j hj
    simp [extend, hj]

theorem sum_kernel_extend (S : Finset ℕ) (x : Walsh.Group) :
    ∑ a : Assignments S, kernel S (extend S a) x = (2 : ℝ) ^ S.card := by
  classical
  rw [Finset.sum_eq_single (fun j : S => x j)]
  · rw [kernel_eq_indicator, Set.indicator_of_mem]
    exact (cylinder_extend_iff S _ x).mpr rfl
  · intro b _ hb
    rw [kernel_eq_indicator, Set.indicator_of_notMem]
    exact fun h => hb ((cylinder_extend_iff S b x).mp h)
  · simp

theorem card_assignments (S : Finset ℕ) : Fintype.card (Assignments S) = 2 ^ S.card := by
  simp only [Assignments, Fintype.card_fun, Fintype.card_coe]
  congr 1

def translatedDensity (ν : Measure Walsh.Group) (S : Finset ℕ) (s : Walsh.Group) :
    C(Walsh.Group, ℝ) :=
  ⟨fun x => density ν S (s * x), (density ν S).continuous.comp (continuous_const.mul continuous_id)⟩

theorem translatedDensity_apply (ν : Measure Walsh.Group) (S : Finset ℕ) (s x : Walsh.Group) :
    translatedDensity ν S s x = density ν S (s * x) := rfl

theorem translatedDensity_eq_sum (ν : Measure Walsh.Group) (S : Finset ℕ) (s : Walsh.Group) :
    translatedDensity ν S s =
      ∑ F ∈ S.powerset, (coefficient ν F * character F s) • characterContinuous F := by
  ext x
  simp only [translatedDensity_apply, density_apply, character_mul,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    characterContinuous, ContinuousMap.coe_mk, mul_assoc]

theorem translatedDensity_nonneg (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (S : Finset ℕ) (s x : Walsh.Group) : 0 ≤ translatedDensity ν S s x :=
  density_nonneg ν S (s * x)

theorem integral_translatedDensity (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (S : Finset ℕ) (s : Walsh.Group) : ∫ x, translatedDensity ν S s x ∂haar = 1 := by
  change (∫ x, density ν S (s * x) ∂haar) = 1
  rw [integral_mul_left_eq_self, integral_density]

theorem translatedDensity_eq_convolution (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (S : Finset ℕ) (s : Walsh.Group) :
    ContinuousMap.toLp 1 haar ℝ (translatedDensity ν S s) =
      convolutionL1 ν (kernelL1 S s) := by
  rw [translatedDensity_eq_sum, kernelL1_eq_sum]
  simp only [map_sum, map_smul, toLp_characterContinuous, convolutionL1_character,
    smul_smul, mul_comm]

theorem sum_translatedDensity (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (S : Finset ℕ) (x : Walsh.Group) :
    ∑ a : Assignments S, translatedDensity ν S (extend S a) x = (2 : ℝ) ^ S.card := by
  have heq (s y : Walsh.Group) : kernel S y (s * x) = kernel S s (y * x) := by
    simp only [kernel_apply, character_mul]
    apply Finset.sum_congr rfl
    intro F hF
    ring
  have heq2 (a : Assignments S) : translatedDensity ν S (extend S a) x =
      ∫ y, kernel S (extend S a) (y * x) ∂ν := by
    rw [translatedDensity_apply, density_eq_integral]
    exact integral_congr_ae (ae_of_all _ (heq (extend S a)))
  rw [Finset.sum_congr rfl (fun a _ => heq2 a)]
  rw [← integral_finsetSum]
  · simp [sum_kernel_extend, integral_const, measureReal_def]
  · intro a _
    exact ((kernel S (extend S a)).continuous.comp (continuous_id.mul continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem average_translatedDensity (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (S : Finset ℕ) (x : Walsh.Group) :
    (Fintype.card (Assignments S) : ℝ)⁻¹ *
      ∑ a : Assignments S, translatedDensity ν S (extend S a) x = 1 := by
  rw [sum_translatedDensity, card_assignments]
  push_cast
  exact inv_mul_cancel₀ (by positivity)

theorem density_congr (ν : Measure Walsh.Group) (S : Finset ℕ) {x y : Walsh.Group}
    (hxy : ∀ j ∈ S, x j = y j) : density ν S x = density ν S y := by
  simp only [density_apply]
  apply Finset.sum_congr rfl
  intro F hF
  congr 1
  exact Finset.prod_congr rfl (fun j hj => congrArg signValue (hxy j
    ((Finset.mem_powerset.mp hF) hj)))

theorem translatedDensity_congr (ν : Measure Walsh.Group) (S : Finset ℕ)
    (s : Walsh.Group) {x y : Walsh.Group} (hxy : ∀ j ∈ S, x j = y j) :
    translatedDensity ν S s x = translatedDensity ν S s y :=
  density_congr ν S (fun j hj => congrArg (fun z => s j * z) (hxy j hj))

def translatedSet (B : Set Walsh.Group) (s : Walsh.Group) : Set Walsh.Group :=
  (fun x => s * x) ⁻¹' B

theorem measurableSet_translatedSet {B : Set Walsh.Group} (hB : MeasurableSet B)
    (s : Walsh.Group) : MeasurableSet (translatedSet B s) :=
  hB.preimage (continuous_const.mul continuous_id).measurable

theorem measure_translatedSet {B : Set Walsh.Group} (hB : MeasurableSet B)
    (s : Walsh.Group) : haar (translatedSet B s) = haar B :=
  (measurePreserving_mul_left haar s).measure_preimage hB.nullMeasurableSet

theorem dependsOn_translatedSet (S : Finset ℕ) {B : Set Walsh.Group}
    (hB : DependsOn S B) (s : Walsh.Group) : DependsOn S (translatedSet B s) := by
  intro x y hxy
  exact hB (s * x) (s * y) (fun j hj => congrArg (fun z => s j * z) (hxy j hj))

theorem setIntegral_translatedDensity (ν : Measure Walsh.Group) [IsProbabilityMeasure ν]
    (S : Finset ℕ) {B : Set Walsh.Group} (hBm : MeasurableSet B) (hB : DependsOn S B)
    (s : Walsh.Group) :
    ∫ x in translatedSet B s, translatedDensity ν S s x ∂haar = ν.real B := by
  rw [← integral_indicator (measurableSet_translatedSet hBm s)]
  change (∫ x, B.indicator (density ν S) (s * x) ∂haar) = _
  rw [integral_mul_left_eq_self, integral_indicator hBm, setIntegral_density ν S hBm hB]

theorem norm_noise_translatedResolventDensity_sub_le (rates : ℕ → ℝ≥0)
    (t : PositiveTime) (S : Finset ℕ) (s : Walsh.Group) (u : ℝ≥0) :
    let q := ContinuousMap.toLp 1 haar ℝ (translatedDensity (resolventMeasure rates t) S s)
    ‖noiseL1 ℝ rates u q - q‖ ≤ 2 * (1 - Real.exp (-(u : ℝ) / (t : ℝ))) := by
  let := isProbabilityMeasure_resolventMeasure rates t.property
  dsimp only
  rw [translatedDensity_eq_convolution]
  change ‖noiseL1 ℝ rates u (resolventL1 ℝ rates t (kernelL1 S s)) -
    resolventL1 ℝ rates t (kernelL1 S s)‖ ≤ _
  simpa only [norm_kernelL1, mul_one] using
    norm_noise_resolvent_sub_le ℝ rates t u (kernelL1 S s)

end PL1.FiniteCoordinateKernels
