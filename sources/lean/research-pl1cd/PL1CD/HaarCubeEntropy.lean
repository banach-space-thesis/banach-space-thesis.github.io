import PL1CD.AnisotropicCubeEntropy
import PL1.HeadTail
import PL1.SingularCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace PL1CD.Entropy
open PL1.Bonami PL1.Walsh

theorem varyingNoise_add (r : ℕ → ℝ) (n : ℕ) (f g : Cube n → ℝ) :
    varyingNoise r n (fun x => f x + g x) =
      fun x => varyingNoise r n f x + varyingNoise r n g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hp : plusSlice (r n) (fun x => f x + g x) =
          fun x => plusSlice (r n) f x + plusSlice (r n) g x := by
        funext x
        simp only [plusSlice]
        ring
      have hm : minusSlice (r n) (fun x => f x + g x) =
          fun x => minusSlice (r n) f x + minusSlice (r n) g x := by
        funext x
        simp only [minusSlice]
        ring
      funext x
      simp only [varyingNoise, hp, hm, ih]
      split_ifs <;> rfl

theorem varyingNoise_mul (r : ℕ → ℝ) (n : ℕ) (c : ℝ) (f : Cube n → ℝ) :
    varyingNoise r n (fun x => c * f x) = fun x => c * varyingNoise r n f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hp : plusSlice (r n) (fun x => c * f x) = fun x => c * plusSlice (r n) f x := by
        funext x
        simp only [plusSlice]
        ring
      have hm : minusSlice (r n) (fun x => c * f x) = fun x => c * minusSlice (r n) f x := by
        funext x
        simp only [minusSlice]
        ring
      funext x
      simp only [varyingNoise, hp, hm, ih]
      split_ifs <;> rfl

theorem varyingNoise_mean_diff (r : ℕ → ℝ) (n : ℕ) (f : Cube (n + 1) → ℝ)
    (x : Cube (n + 1)) :
    varyingNoise r (n + 1) f x = varyingNoise r n (meanSlice f) x.2 +
      (if x.1 then -r n else r n) * varyingNoise r n (diffSlice f) x.2 := by
  have hp : plusSlice (r n) f = fun y => meanSlice f y + r n * diffSlice f y := by
    funext y
    simp only [plusSlice, meanSlice, diffSlice]
    ring
  have hm : minusSlice (r n) f = fun y => meanSlice f y + (-r n) * diffSlice f y := by
    funext y
    simp only [minusSlice, meanSlice, diffSlice]
    ring
  simp only [varyingNoise, hp, hm, varyingNoise_add, varyingNoise_mul]
  split_ifs <;> rfl

theorem dependsOn_lift (n : ℕ) (f : Cube n → ℝ) :
    PL1.HeadTail.DependsOn (Finset.range n) (fun x => f (sample n x)) := by
  intro x y hxy
  exact congrArg f (sample_congr n (fun j hj => hxy j (Finset.mem_range.mpr hj)))

theorem integral_noise_lift (rates : ℕ → ℝ≥0) (u : ℝ≥0) (n : ℕ)
    (f : Cube n → ℝ) (x : PL1.Walsh.Group) :
    (∫ y, f (sample n (x * y)) ∂PL1.Noise.measure rates u) =
      varyingNoise (PL1.Noise.bias rates u) n f (sample n x) := by
  induction n with
  | zero => simp [sample, varyingNoise, integral_const, measureReal_def]
  | succ n ih =>
      have hdiff := (dependsOn_lift n (diffSlice f)).translate x
      have hcoord : PL1.HeadTail.DependsOn {n} (fun y : PL1.Walsh.Group => signValue (y n)) := by
        intro y z hyz
        exact congrArg signValue (hyz n (by simp))
      have hd : Disjoint ({n} : Finset ℕ) (Finset.range n) := by simp
      have hc : Continuous (fun y : PL1.Walsh.Group => signValue (y n)) :=
        (continuous_of_discreteTopology : Continuous signValue).comp (continuous_apply n)
      have hct : Continuous (fun y => diffSlice f (sample n (x * y))) :=
        (continuous_lift n (diffSlice f)).comp (continuous_const.mul continuous_id)
      have hind := (PL1.HeadTail.indepFun_noise rates u hd hcoord hdiff).integral_fun_mul_eq_mul_integral
        hc.aestronglyMeasurable hct.aestronglyMeasurable
      have hiM : Integrable (fun y => meanSlice f (sample n (x * y))) (PL1.Noise.measure rates u) :=
        ((continuous_lift n (meanSlice f)).comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hiD : Integrable (fun y => signValue (y n) * diffSlice f (sample n (x * y)))
          (PL1.Noise.measure rates u) :=
        (hc.mul hct).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      conv_lhs => simp only [lift_succ, Pi.mul_apply, signValue_mul, mul_assoc]
      rw [integral_add hiM (hiD.const_mul (signValue (x n))), integral_const_mul, hind]
      change (∫ y, meanSlice f (sample n (x * y)) ∂PL1.Noise.measure rates u) +
        signValue (x n) * ((∫ y, PL1.Carrier.coordinate n y ∂PL1.Noise.measure rates u) *
          ∫ y, diffSlice f (sample n (x * y)) ∂PL1.Noise.measure rates u) = _
      rw [ih, ih, PL1.Carrier.integral_coordinate_noise, varyingNoise_mean_diff]
      simp only [sample, signValue_eq_bit]
      by_cases h : signBit (x n) = true <;> simp [h] <;> ring

theorem noise_lift_toLp (rates : ℕ → ℝ≥0) (u : ℝ≥0) (n : ℕ) (f : Cube n → ℝ) :
    PL1.Noise.noiseL1 ℝ rates u (ContinuousMap.toLp 1 haar ℝ (liftContinuous n f)) =
      ContinuousMap.toLp 1 haar ℝ
        (liftContinuous n (varyingNoise (PL1.Noise.bias rates u) n f)) := by
  apply Lp.ext
  filter_upwards [convolutionL1_ae_eq_integral_of_ae_eq (PL1.Noise.measure rates u)
      (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar (liftContinuous n f)),
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar
      (liftContinuous n (varyingNoise (PL1.Noise.bias rates u) n f))] with x hx hy
  exact hx.trans ((integral_noise_lift rates u n f x).trans hy.symm)

def Ent (f : PL1.Walsh.Group → ℝ) : ℝ := Phi haar f - phi (∫ x, f x ∂haar)

theorem Ent_lift (n : ℕ) (f : Cube n → ℝ) :
    Ent (fun x => f (sample n x)) = cubeEntropy n f := by
  unfold Ent Phi cubeEntropy
  change (∫ x, (fun y => phi (f y)) (sample n x) ∂haar) -
    phi (∫ x, f (sample n x) ∂haar) = _
  rw [integral_lift n (fun y => phi (f y)), integral_lift n f]

theorem Ent_noise_lift_le (rates : ℕ → ℝ≥0) (u : ℝ≥0) (a : ℝ≥0) (d n : ℕ)
    (hrates : ∀ j, d ≤ j → (a : ℝ) ≤ rates j)
    (f : Cube n → ℝ) (hf : ∀ x, 0 ≤ f x) :
    Ent (fun x => varyingNoise (PL1.Noise.bias rates u) n f (sample n x)) ≤
      (d : ℝ) * Real.log 2 * (∫ x, f (sample n x) ∂haar) +
        Real.exp (-(u : ℝ) * a) * Ent (fun x => f (sample n x)) := by
  rw [Ent_lift, Ent_lift, integral_lift]
  apply cubeEntropy_varyingNoise_le _ _ (Real.exp_pos _).le d n _ _ f hf
  · intro j _
    exact ⟨(PL1.Noise.bias_pos rates u j).le, PL1.Noise.bias_le_one rates u j⟩
  · intro j hdj _
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (hrates j hdj) (neg_nonpos.mpr u.coe_nonneg)

end PL1CD.Entropy
