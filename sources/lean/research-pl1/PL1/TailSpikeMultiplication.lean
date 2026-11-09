import PL1.TailSpikes
import PL1.HeadTailNoise
import PL1.HeadTailNorms
import PL1.ResolventMultiplication
import PL1.IntrinsicSpikes

/-! # Actual semigroup and resolvent commutators of tail-spike multiplication -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace PL1.TailSpikes
open Walsh Noise HeadTail FiniteCoordinateKernels

variable {K : Type*} [RCLike K]

/-- The commutator norm factors exactly into its tail and head norms. -/
theorem norm_noise_multiplier_commutator_eq (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    {S T : Finset ℕ} (hST : Disjoint S T)
    (f : C(Walsh.Group, K)) (q : C(Walsh.Group, ℝ))
    (hf : HeadTail.DependsOn S f) (hq : HeadTail.DependsOn T q) :
    ‖noiseL1 K rates u (L1Multiplication.multiplier K q (ContinuousMap.toLp 1 haar K f)) -
      L1Multiplication.multiplier K q (noiseL1 K rates u (ContinuousMap.toLp 1 haar K f))‖ =
      ‖noiseL1 ℝ rates u (ContinuousMap.toLp 1 haar ℝ q) - ContinuousMap.toLp 1 haar ℝ q‖ *
        ‖noiseL1 K rates u (ContinuousMap.toLp 1 haar K f)‖ := by
  let f' := noiseContinuous K rates u S f hf
  let q' := noiseContinuous ℝ rates u T q hq - q
  have hf' : HeadTail.DependsOn S f' := noiseContinuous_dependsOn rates u S f hf
  have hq' : HeadTail.DependsOn T q' := by
    intro x y hxy
    exact congrArg₂ (fun a b : ℝ => a - b)
      (noiseContinuous_dependsOn rates u T q hq x y hxy) (hq x y hxy)
  rw [noiseL1_multiplier_toLp rates u hST f q hf hq,
    ← L1Multiplication.multiplier_sub, ← noiseContinuous_toLp rates u S f hf]
  change ‖L1Multiplication.multiplier K q' (ContinuousMap.toLp 1 haar K f')‖ = _
  rw [norm_multiplier_toLp hST f' q' hf' hq']
  simp only [q', f', map_sub, noiseContinuous_toLp]

/-- The genuine semigroup commutator estimate for every member of an actual spike family. -/
theorem RateFamily.norm_noise_commutator_le {rates : ℕ → ℝ≥0} {d : ℕ}
    {T : PositiveTime} {δ : ℝ} (Q : RateFamily rates d T δ)
    (a : Assignments Q.coordinates) (f : C(Walsh.Group, K))
    (hf : HeadTail.DependsOn (Finset.range d) f) (u : ℝ≥0) :
    ‖noiseL1 K rates u (L1Multiplication.multiplier K (Q.q a) (ContinuousMap.toLp 1 haar K f)) -
      L1Multiplication.multiplier K (Q.q a) (noiseL1 K rates u (ContinuousMap.toLp 1 haar K f))‖ ≤
      2 * (1 - Real.exp (-(u : ℝ) / (T : ℝ))) * ‖ContinuousMap.toLp 1 haar K f‖ := by
  rw [norm_noise_multiplier_commutator_eq rates u Q.beyond_prefix.symm f (Q.q a) hf (Q.q_depends a)]
  apply mul_le_mul (Q.almost_invariant a u) ?_ (norm_nonneg _) ?_
  · exact ((noiseL1 K rates u).le_opNorm _).trans
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
        (norm_noiseL1_le_one K rates u) (norm_nonneg (ContinuousMap.toLp 1 haar K f))))
  · exact (norm_nonneg _).trans (Q.almost_invariant a u)

/-- Exponential averaging yields the quantitative resolvent commutator used by the intrinsic norm. -/
theorem RateFamily.norm_resolvent_commutator_le {rates : ℕ → ℝ≥0} {d : ℕ}
    {T : PositiveTime} {δ : ℝ} (Q : RateFamily rates d T δ)
    (a : Assignments Q.coordinates) (f : C(Walsh.Group, K))
    (hf : HeadTail.DependsOn (Finset.range d) f) (t : PositiveTime) :
    ‖resolventL1 K rates t (L1Multiplication.multiplier K (Q.q a) (ContinuousMap.toLp 1 haar K f)) -
      L1Multiplication.multiplier K (Q.q a) (resolventL1 K rates t (ContinuousMap.toLp 1 haar K f))‖ ≤
      (2 * (t : ℝ) / (T : ℝ)) * ‖ContinuousMap.toLp 1 haar K f‖ :=
  Noise.norm_resolvent_commutator_le_time K rates t T _ _ (Q.norm_noise_commutator_le a f hf)

/-- The same bound for the identity-minus-resolvent coordinates. -/
theorem RateFamily.norm_id_sub_resolvent_commutator_le {rates : ℕ → ℝ≥0} {d : ℕ}
    {T : PositiveTime} {δ : ℝ} (Q : RateFamily rates d T δ)
    (a : Assignments Q.coordinates) (f : C(Walsh.Group, K))
    (hf : HeadTail.DependsOn (Finset.range d) f) (t : PositiveTime) :
    ‖(L1Multiplication.multiplier K (Q.q a) (ContinuousMap.toLp 1 haar K f) -
        resolventL1 K rates t (L1Multiplication.multiplier K (Q.q a) (ContinuousMap.toLp 1 haar K f))) -
      L1Multiplication.multiplier K (Q.q a) (ContinuousMap.toLp 1 haar K f -
        resolventL1 K rates t (ContinuousMap.toLp 1 haar K f))‖ ≤
      (2 * (t : ℝ) / (T : ℝ)) * ‖ContinuousMap.toLp 1 haar K f‖ :=
  Noise.norm_id_sub_resolvent_commutator_le_time K rates t T _ _ (Q.norm_noise_commutator_le a f hf)

#print axioms RateFamily.norm_id_sub_resolvent_commutator_le
end PL1.TailSpikes
