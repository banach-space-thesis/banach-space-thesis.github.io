import PL1CD.CubeApproximation
import PL1CD.EntropyContinuity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace PL1CD.Entropy
open PL1.Walsh PL1.Bonami

theorem Ent_congr {f g : PL1.Walsh.Group → ℝ} (hfg : f =ᵐ[haar] g) :
    Ent f = Ent g := by
  unfold Ent Phi
  exact congrArg₂ (· - ·) (integral_congr_ae (hfg.fun_comp phi))
    (congrArg phi (integral_congr_ae hfg))

theorem Ent_liftLp (n : ℕ) (f : Cube n → ℝ) : Ent (liftLp n f) = cubeEntropy n f :=
  (Ent_congr (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar
    (liftContinuous n f))).trans (Ent_lift n f)

theorem integral_liftLp (n : ℕ) (f : Cube n → ℝ) :
    (∫ x, liftLp n f x ∂haar) = average n f :=
  (integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar
    (liftContinuous n f))).trans (integral_lift n f)

theorem Ent_tendsto_of_bounded_L1 (f : ℕ → Lp ℝ 1 haar) (g : Lp ℝ 1 haar)
    (C : ℝ) (hbound : ∀ n, ∀ᵐ x ∂haar, f n x ∈ Set.Icc 0 C)
    (hfg : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => Ent (f n)) atTop (𝓝 (Ent g)) := by
  exact (Phi_tendsto_of_bounded_L1 haar f g C hbound hfg).sub
    (Real.continuous_mul_log.tendsto _ |>.comp (continuous_integral.tendsto g |>.comp hfg))

theorem Ent_noise_le (rates : ℕ → ℝ≥0) (u a : ℝ≥0) (d : ℕ)
    (hrates : ∀ j, d ≤ j → (a : ℝ) ≤ rates j)
    (f : Lp ℝ 1 haar) (C : ℝ) (hf : ∀ᵐ x ∂haar, f x ∈ Set.Icc 0 C) :
    Ent (PL1.Noise.noiseL1 ℝ rates u f) ≤
      (d : ℝ) * Real.log 2 * (∫ x, f x ∂haar) + Real.exp (-(u : ℝ) * a) * Ent f := by
  let ef : ℕ → Lp ℝ 1 haar := fun n => PL1.WalshExpectations.expectationL1 ℝ n f
  have hef : ∀ n, ∀ᵐ x ∂haar, ef n x ∈ Set.Icc 0 C :=
    fun n => convolution_preserves_Icc _ f C hf
  have ht : Tendsto ef atTop (𝓝 f) := PL1.WalshExpectations.tendsto_expectationL1 ℝ f
  have htn := (PL1.Noise.noiseL1 ℝ rates u).continuous.tendsto f |>.comp ht
  have he := Ent_tendsto_of_bounded_L1 ef f C hef ht
  have hen := Ent_tendsto_of_bounded_L1 _ _ C
    (fun n => convolution_preserves_Icc _ (ef n) C (hef n)) htn
  have hmass (n : ℕ) : (∫ x, ef n x ∂haar) = ∫ x, f x ∂haar :=
    integral_convolutionL1 _ f
  apply le_of_tendsto_of_tendsto hen
    (tendsto_const_nhds.add (tendsto_const_nhds.mul he))
  apply Eventually.of_forall
  intro n
  change Ent (PL1.Noise.noiseL1 ℝ rates u (ef n)) ≤
    (d : ℝ) * Real.log 2 * (∫ x, f x ∂haar) +
      Real.exp (-(u : ℝ) * a) * Ent (ef n)
  rw [← hmass n]
  obtain ⟨g, hg, hgb⟩ := exists_bounded_lift_expectation n f C hf
  change liftLp n g = ef n at hg
  rw [← hg]
  change Ent (PL1.Noise.noiseL1 ℝ rates u (ContinuousMap.toLp 1 haar ℝ
    (liftContinuous n g))) ≤ _
  rw [noise_lift_toLp]
  change Ent (liftLp n (varyingNoise (PL1.Noise.bias rates u) n g)) ≤
    (d : ℝ) * Real.log 2 * (∫ x, liftLp n g x ∂haar) +
      Real.exp (-(u : ℝ) * a) * Ent (liftLp n g)
  rw [Ent_liftLp, Ent_liftLp, integral_liftLp]
  have h := Ent_noise_lift_le rates u a d n hrates g (fun x => (hgb x).1)
  simpa only [Ent_lift, integral_lift] using h

end PL1CD.Entropy
