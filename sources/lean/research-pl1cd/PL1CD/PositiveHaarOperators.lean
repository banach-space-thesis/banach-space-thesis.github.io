import PL1CD.RefinementEnergy
import PL1CD.EntropyUpper

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators NNReal

namespace PL1CD.PositiveHaarOperators
open PL1.Walsh PL1.ExplicitMartingale PL1.FiniteCoordinateKernels
open PL1CD.Entropy PL1CD.CylinderRefinement

abbrev HaarL1 := Lp ℝ 1 haar

def IsPositive (B : HaarL1 →L[ℝ] HaarL1) : Prop :=
  ∀ f, (∀ᵐ x ∂haar, 0 ≤ f x) → ∀ᵐ x ∂haar, 0 ≤ B f x

def oneL1 : HaarL1 := PL1.ExplicitMartingale.kernelL1 ℝ 0 1

theorem coeFn_oneL1 : oneL1 =ᵐ[haar] fun _ => (1 : ℝ) := by
  filter_upwards [coeFn_kernelL1 ℝ 0 1] with x hx
  simpa [oneL1, kernelContinuous_apply] using hx

theorem kernel_nonneg (m : ℕ) (s : PL1.Walsh.Group) :
    ∀ᵐ x ∂haar, 0 ≤ PL1.ExplicitMartingale.kernelL1 ℝ m s x := by
  filter_upwards [coeFn_kernelL1 ℝ m s] with x hx
  rw [hx]
  exact kernelContinuous_nonneg m s x

theorem kernel_le_one (m : ℕ) (s : PL1.Walsh.Group) :
    ∀ᵐ x ∂haar, PL1.ExplicitMartingale.kernelL1 ℝ m s x ≤
      ((2 : ℝ) ^ m • oneL1) x := by
  filter_upwards [coeFn_kernelL1 ℝ m s, coeFn_oneL1,
    Lp.coeFn_smul ((2 : ℝ) ^ m) oneL1] with x hx ho hs
  rw [hx, hs, Pi.smul_apply, smul_eq_mul, ho, mul_one,
    kernelContinuous_eq_indicator]
  by_cases h : x ∈ cylinder m s <;> simp [h]

theorem IsPositive.mono {B : HaarL1 →L[ℝ] HaarL1} (hB : IsPositive B)
    {f g : HaarL1} (hfg : ∀ᵐ x ∂haar, f x ≤ g x) :
    ∀ᵐ x ∂haar, B f x ≤ B g x := by
  have hp : ∀ᵐ x ∂haar, 0 ≤ (g - f) x := by
    filter_upwards [hfg, Lp.coeFn_sub g f] with x hx he
    simpa only [he, Pi.sub_apply, sub_nonneg] using hx
  have h := hB (g - f) hp
  rw [map_sub] at h
  filter_upwards [h, Lp.coeFn_sub (B g) (B f)] with x hx he
  simpa only [he, Pi.sub_apply, sub_nonneg] using hx

theorem image_kernel_bound (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B)
    (b : ℝ) (hb : ∀ᵐ x ∂haar, B oneL1 x ≤ b) (m : ℕ) (s : PL1.Walsh.Group) :
    ∀ᵐ x ∂haar, B (PL1.ExplicitMartingale.kernelL1 ℝ m s) x ∈
      Set.Icc 0 (b * 2 ^ m) := by
  have hle := hB.mono (kernel_le_one m s)
  rw [map_smul] at hle
  filter_upwards [hB _ (kernel_nonneg m s), hle, hb,
    Lp.coeFn_smul ((2 : ℝ) ^ m) (B oneL1)] with x hp hle hb he
  refine ⟨hp, ?_⟩
  rw [he, Pi.smul_apply, smul_eq_mul] at hle
  exact hle.trans (by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m])

theorem image_kernel_mass (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B)
    (hcontract : ‖B‖ ≤ 1) (m : ℕ) (s : PL1.Walsh.Group) :
    ∫ x, B (PL1.ExplicitMartingale.kernelL1 ℝ m s) x ∂haar ≤ 1 := by
  have hn := hB _ (kernel_nonneg m s)
  have he : (∫ x, B (PL1.ExplicitMartingale.kernelL1 ℝ m s) x ∂haar) =
      ‖B (PL1.ExplicitMartingale.kernelL1 ℝ m s)‖ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    exact hn.mono (fun x hx => (Real.norm_of_nonneg hx).symm)
  rw [he]
  simpa only [PL1.ExplicitMartingale.norm_kernelL1, mul_one] using
    (B.le_opNorm (PL1.ExplicitMartingale.kernelL1 ℝ m s)).trans
      (by simpa only [PL1.ExplicitMartingale.norm_kernelL1, mul_one] using hcontract)

theorem noise_image_kernel_bound (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B)
    (b : ℝ) (hb : ∀ᵐ x ∂haar, B oneL1 x ≤ b) (m : ℕ) (s : PL1.Walsh.Group) :
    ∀ᵐ x ∂haar, PL1.Noise.noiseL1 ℝ rates u
      (B (PL1.ExplicitMartingale.kernelL1 ℝ m s)) x ∈ Set.Icc 0 (b * 2 ^ m) :=
  convolution_preserves_Icc _ _ _ (image_kernel_bound B hB b hb m s)

theorem noise_image_kernel_mass (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B) (hcontract : ‖B‖ ≤ 1)
    (m : ℕ) (s : PL1.Walsh.Group) :
    ∫ x, PL1.Noise.noiseL1 ℝ rates u
      (B (PL1.ExplicitMartingale.kernelL1 ℝ m s)) x ∂haar ≤ 1 := by
  change (∫ x, convolutionL1 _
    (B (PL1.ExplicitMartingale.kernelL1 ℝ m s)) x ∂haar) ≤ 1
  rw [integral_convolutionL1]
  exact image_kernel_mass B hB hcontract m s

theorem noise_level_energy (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B) (hcontract : ‖B‖ ≤ 1)
    (b : ℝ) (hb : 1 ≤ b) (hbound : ∀ᵐ x ∂haar, B oneL1 x ≤ b)
    (M : ℕ → ℕ) (hM : Monotone M) (n : ℕ) :
    PL1CD.Variation.levelSeminorm ℝ HaarL1 M n
      ((PL1.Noise.noiseL1 ℝ rates u).comp B) ^ 2 ≤
    4 * (levelEntropy ((PL1.Noise.noiseL1 ℝ rates u).comp B) M (n + 1) -
      levelEntropy ((PL1.Noise.noiseL1 ℝ rates u).comp B) M n) := by
  apply level_energy_le _ M n (hM (Nat.le_succ n)) (b * 2 ^ M (n + 1))
    (by positivity)
  · intro a
    exact noise_image_kernel_bound rates u B hB b hbound _ _
  · intro a
    exact noise_image_kernel_mass rates u B hB hcontract _ _

theorem noise_level_entropy_le (rates : ℕ → ℝ≥0) (u a : ℝ≥0) (d : ℕ)
    (hrates : ∀ j, d ≤ j → (a : ℝ) ≤ rates j)
    (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B) (hcontract : ‖B‖ ≤ 1)
    (b : ℝ) (hb : 1 ≤ b) (hbound : ∀ᵐ x ∂haar, B oneL1 x ≤ b)
    (M : ℕ → ℕ) (n : ℕ) :
    levelEntropy ((PL1.Noise.noiseL1 ℝ rates u).comp B) M n ≤
      (d : ℝ) * Real.log 2 + Real.exp (-(u : ℝ) * a) *
        ((M n : ℝ) * Real.log 2 + Real.log b + 1) := by
  have hC : 1 ≤ b * (2 : ℝ) ^ M n := by
    have hp : 1 ≤ (2 : ℝ) ^ M n := one_le_pow₀ (by norm_num)
    nlinarith
  unfold levelEntropy averagePhi
  apply (finiteAverage_mono _ (fun _ => _) ?_).trans_eq (finiteAverage_const _)
  intro s
  rw [kernelL1_range]
  have h := Phi_noise_le rates u a d hrates
    (B (PL1.ExplicitMartingale.kernelL1 ℝ (M n) (extend _ s)))
    (b * 2 ^ M n) hC (image_kernel_bound B hB b hbound _ _)
    (image_kernel_mass B hB hcontract _ _)
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hb)
  have hp0 : (2 : ℝ) ^ M n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Real.log_mul hb0 hp0, Real.log_pow] at h
  simpa only [ContinuousLinearMap.comp_apply,
    add_assoc, add_comm, add_left_comm] using h

end PL1CD.PositiveHaarOperators
