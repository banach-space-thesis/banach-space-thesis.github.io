import PL1.HeadTail
import PL1.L1Multiplication

/-! # Exact noise factorization on disjoint finite coordinates -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace PL1.HeadTail
open Walsh

variable {K : Type*} [RCLike K]

theorem DependsOn.convolution {S : Finset ℕ} {f : Walsh.Group → K}
    (hf : DependsOn S f) (ν : Measure Walsh.Group) :
    DependsOn S (fun x => ∫ y, f (x * y) ∂ν) := by
  intro x z hxz
  apply integral_congr_ae
  exact ae_of_all _ (fun y => hf _ _ (fun j hj =>
    congrArg (fun a => a * y j) (hxz j hj)))

/-- The continuous representative of the actual product-noise convolution. -/
def noiseContinuous (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    (S : Finset ℕ) (f : C(Walsh.Group, K)) (hf : DependsOn S f) : C(Walsh.Group, K) :=
  ⟨fun x => ∫ y, f (x * y) ∂Noise.measure rates u, (hf.convolution _).continuous⟩

theorem noiseContinuous_apply (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    (S : Finset ℕ) (f : C(Walsh.Group, K)) (hf : DependsOn S f) (x : Walsh.Group) :
    noiseContinuous K rates u S f hf x = ∫ y, f (x * y) ∂Noise.measure rates u := rfl

theorem noiseContinuous_dependsOn (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    (S : Finset ℕ) (f : C(Walsh.Group, K)) (hf : DependsOn S f) :
    DependsOn S (noiseContinuous K rates u S f hf) := hf.convolution _

theorem noiseContinuous_toLp (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    (S : Finset ℕ) (f : C(Walsh.Group, K)) (hf : DependsOn S f) :
    ContinuousMap.toLp 1 haar K (noiseContinuous K rates u S f hf) =
      Noise.noiseL1 K rates u (ContinuousMap.toLp 1 haar K f) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := K) haar (noiseContinuous K rates u S f hf),
    convolutionL1_ae_eq_integral_of_ae_eq (Noise.measure rates u)
      (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := K) haar f)] with x hx hy
  exact hx.trans hy.symm

/-- Product-noise factorization is valid for the actual independent coordinate measures. -/
theorem integral_noise_smul (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    {S T : Finset ℕ} (hST : Disjoint S T)
    (f : C(Walsh.Group, K)) (q : C(Walsh.Group, ℝ))
    (hf : DependsOn S f) (hq : DependsOn T q) (x : Walsh.Group) :
    (∫ y, q (x * y) • f (x * y) ∂Noise.measure rates u) =
      (∫ y, q (x * y) ∂Noise.measure rates u) •
        ∫ y, f (x * y) ∂Noise.measure rates u := by
  borelize K
  exact (indepFun_noise rates u hST.symm (hq.translate x) (hf.translate x)).integral_fun_smul_eq_smul_integral
    (hq.translate x).continuous.aestronglyMeasurable (hf.translate x).continuous.aestronglyMeasurable

/-- The factorization descends to the actual Haar L1 quotient and multiplier operator. -/
theorem noiseL1_multiplier_toLp (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    {S T : Finset ℕ} (hST : Disjoint S T)
    (f : C(Walsh.Group, K)) (q : C(Walsh.Group, ℝ))
    (hf : DependsOn S f) (hq : DependsOn T q) :
    Noise.noiseL1 K rates u (L1Multiplication.multiplier K q (ContinuousMap.toLp 1 haar K f)) =
      L1Multiplication.multiplier K (noiseContinuous ℝ rates u T q hq)
        (Noise.noiseL1 K rates u (ContinuousMap.toLp 1 haar K f)) := by
  have hprod : L1Multiplication.multiplier K q (ContinuousMap.toLp 1 haar K f) =ᵐ[haar]
      fun x => q x • f x := by
    filter_upwards [L1Multiplication.coeFn_multiplier K q (ContinuousMap.toLp 1 haar K f),
      ContinuousMap.coeFn_toLp (p := 1) (𝕜 := K) haar f] with x hx hy
    rw [hx, hy]
  apply Lp.ext
  filter_upwards [convolutionL1_ae_eq_integral_of_ae_eq (Noise.measure rates u) hprod,
    L1Multiplication.coeFn_multiplier K (noiseContinuous ℝ rates u T q hq)
      (Noise.noiseL1 K rates u (ContinuousMap.toLp 1 haar K f)),
    convolutionL1_ae_eq_integral_of_ae_eq (Noise.measure rates u)
      (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := K) haar f)] with x hx hy hz
  change _ = (L1Multiplication.multiplier K (noiseContinuous ℝ rates u T q hq) _) x
  rw [hy]
  change _ = (∫ y, q (x * y) ∂Noise.measure rates u) •
    (Noise.noiseL1 K rates u (ContinuousMap.toLp 1 haar K f)) x
  rw [show (Noise.noiseL1 K rates u (ContinuousMap.toLp 1 haar K f)) x = _ from hz]
  exact hx.trans (integral_noise_smul rates u hST f q hf hq x)

#print axioms noiseL1_multiplier_toLp
end PL1.HeadTail
