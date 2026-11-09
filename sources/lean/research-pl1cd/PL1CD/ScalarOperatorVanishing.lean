import PL1CD.RealOperatorVanishing
import PL1.IntrinsicRealParts

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace PL1CD.Variation
open PL1.Walsh PL1.ScalarRealification PL1.IntrinsicRealParts
open PL1.FiniteCoordinateKernels
open PL1CD.PositiveHaarOperators

variable (K : Type*) [RCLike K]

theorem ofRealL1_real (f : Variation.HaarL1 ℝ) : ofRealL1 ℝ f = f := by
  apply Lp.ext
  filter_upwards [coeFn_ofRealL1 ℝ f] with x hx
  exact hx

theorem ofRealL1_kernel (m : ℕ) (s : PL1.Walsh.Group) :
    ofRealL1 K (PL1.ExplicitMartingale.kernelL1 ℝ m s) =
      PL1.ExplicitMartingale.kernelL1 K m s := by
  rw [PL1.ExplicitMartingale.kernelL1, ofRealL1_real]
  rfl

def partOperator (A : K →L[ℝ] ℝ)
    (B : Variation.HaarL1 K →L[K] Variation.HaarL1 K) :
    Variation.HaarL1 ℝ →L[ℝ] Variation.HaarL1 ℝ :=
  (scalarPart K A).comp ((B.restrictScalars ℝ).comp (ofRealL1 K))

theorem partOperator_noise (A : K →L[ℝ] ℝ) (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    (B : Variation.HaarL1 K →L[K] Variation.HaarL1 K) :
    partOperator K A ((PL1.Noise.noiseL1 K rates u).comp B) =
      (PL1.Noise.noiseL1 ℝ rates u).comp (partOperator K A B) := by
  apply ContinuousLinearMap.ext
  intro f
  exact scalarPart_convolution K A (PL1.Noise.measure rates u) (B (ofRealL1 K f))

theorem levelSeminorm_le_parts (M : ℕ → ℕ) (n : ℕ)
    (B : Variation.HaarL1 K →L[K] Variation.HaarL1 K) :
    levelSeminorm K (Variation.HaarL1 K) M n B ≤
      levelSeminorm ℝ (Variation.HaarL1 ℝ) M n (partOperator K (@RCLike.reCLM K _) B) +
      levelSeminorm ℝ (Variation.HaarL1 ℝ) M n (partOperator K (@RCLike.imCLM K _) B) := by
  let S := Finset.range (M (n + 1))
  let e : Assignments S → Variation.HaarL1 ℝ := fun a =>
    PL1.ExplicitMartingale.kernelL1 ℝ (M (n + 1)) (extend S a) -
      PL1.ExplicitMartingale.kernelL1 ℝ (M n) (extend S a)
  have he (a : Assignments S) : ofRealL1 K (e a) =
      PL1.ExplicitMartingale.kernelL1 K (M (n + 1)) (extend S a) -
        PL1.ExplicitMartingale.kernelL1 K (M n) (extend S a) := by
    dsimp [e]
    rw [map_sub, ofRealL1_kernel, ofRealL1_kernel]
  change (Fintype.card (Assignments S) : ℝ)⁻¹ *
      ∑ a : Assignments S, ‖B (PL1.ExplicitMartingale.kernelL1 K (M (n + 1)) (extend S a) -
        PL1.ExplicitMartingale.kernelL1 K (M n) (extend S a))‖ ≤ _
  simp_rw [← he]
  calc
    _ ≤ (Fintype.card (Assignments S) : ℝ)⁻¹ * ∑ a : Assignments S,
        (‖reL1 K (B (ofRealL1 K (e a)))‖ + ‖imL1 K (B (ofRealL1 K (e a)))‖) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => norm_l1_le_parts K _))
        (by positivity)
    _ = _ := by rw [Finset.sum_add_distrib, mul_add]; rfl

theorem endpointSeminorm_le_parts (M N : ℕ → ℕ) (s : ℕ)
    (B : Variation.HaarL1 K →L[K] Variation.HaarL1 K) :
    endpointSeminorm K (Variation.HaarL1 K) M N s B ≤
      endpointSeminorm ℝ (Variation.HaarL1 ℝ) M N s (partOperator K (@RCLike.reCLM K _) B) +
      endpointSeminorm ℝ (Variation.HaarL1 ℝ) M N s (partOperator K (@RCLike.imCLM K _) B) := by
  simp only [endpointSeminorm, averageSeminorm_apply]
  calc
    _ ≤ (N s : ℝ)⁻¹ * ∑ n ∈ Finset.range (N s),
        (levelSeminorm ℝ (Variation.HaarL1 ℝ) M n (partOperator K (@RCLike.reCLM K _) B) +
          levelSeminorm ℝ (Variation.HaarL1 ℝ) M n (partOperator K (@RCLike.imCLM K _) B)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => levelSeminorm_le_parts K M n B))
        (by positivity)
    _ = _ := by rw [Finset.sum_add_distrib, mul_add]

theorem scalar_noise_vanishing
    (rates : ℕ → ℝ≥0) (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (hgrowth : GrowthCriterion rates M N H)
    (u : ℝ≥0) (hu : 0 < u) (B : Variation.HaarL1 K →L[K] Variation.HaarL1 K) :
    averagedVariation K (Variation.HaarL1 K) M N H hH
      ((PL1.Noise.noiseL1 K rates u).comp B) = 0 := by
  let T := (PL1.Noise.noiseL1 K rates u).comp B
  have hpart (A : K →L[ℝ] ℝ) : Tendsto (fun s =>
      endpointSeminorm ℝ (Variation.HaarL1 ℝ) M N s (partOperator K A T))
      (atTop ⊓ 𝓟 H) (𝓝 0) := by
    rw [show partOperator K A T = (PL1.Noise.noiseL1 ℝ rates u).comp (partOperator K A B)
      from partOperator_noise K A rates u B]
    exact endpoint_tendsto_zero_of_averagedVariation_eq_zero M N H hH _
      (real_noise_vanishing rates M N H hH hgrowth u hu _)
  have ht : Tendsto (fun s => endpointSeminorm K (Variation.HaarL1 K) M N s T)
      (atTop ⊓ 𝓟 H) (𝓝 0) :=
    squeeze_zero (fun s => apply_nonneg _ _) (fun s => endpointSeminorm_le_parts K M N s T)
      (by simpa only [add_zero] using (hpart (@RCLike.reCLM K _)).add (hpart (@RCLike.imCLM K _)))
  let := alongInfinite_neBot hH
  exact ht.limsup_eq

theorem scalar_resolvent_vanishing
    (rates : ℕ → ℝ≥0) (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (hgrowth : GrowthCriterion rates M N H)
    (t : PL1.Noise.PositiveTime) (B : Variation.HaarL1 K →L[K] Variation.HaarL1 K) :
    averagedVariation K (Variation.HaarL1 K) M N H hH
      ((PL1.Noise.resolventL1 K rates t).comp B) = 0 :=
  resolvent_vanishing_of_noise_vanishing K rates M N H hH
    (fun u hu B => scalar_noise_vanishing K rates M N H hH hgrowth u hu B) t B

end PL1CD.Variation
