import PL1CD.StageBlocks
import PL1CD.DensitySeparation
import PL1CD.HaarTransport

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal NNReal

namespace PL1CD

open StageParameters Variation

def stageLowerBound (s : ℕ) : ℝ :=
  2 * (1 - 2 * errorBound s - Real.exp (-(s : ℝ)))

theorem errorBound_tendsto : Tendsto errorBound atTop (𝓝 0) := by
  have ht : Tendsto (fun s : ℕ => (s : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have heq : errorBound = fun s : ℕ => (16 : ℝ)⁻¹ * ((s : ℝ)⁻¹) ^ 2 := by
    funext s
    simp [errorBound, mul_inv_rev, inv_pow, mul_comm]
  rw [heq]
  simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using (ht.pow 2).const_mul (16 : ℝ)⁻¹

theorem stageLowerBound_tendsto : Tendsto stageLowerBound atTop (𝓝 2) := by
  change Tendsto (fun s => 2 * (1 - 2 * errorBound s - Real.exp (-(s : ℝ)))) atTop (𝓝 2)
  have hexp : Tendsto (fun s : ℕ => Real.exp (-(s : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  simpa only [mul_zero, sub_zero, mul_one] using
    (((tendsto_const_nhds (x := (1 : ℝ))).sub (errorBound_tendsto.const_mul 2)).sub hexp).const_mul 2

variable (𝕜 : Type) [RCLike 𝕜]

theorem resolvent_stage_increment_ge {s n : ℕ} (hs : 0 < s) (A : Set ℕ) (hsA : s ∈ A)
    (hlower : levels (s - 1) ≤ n) (hupper : n < levels s) (x : PL1.Walsh.Group) :
    stageLowerBound s ≤ ‖unitResolvent 𝕜 (rates A)
      (PL1.ExplicitMartingale.kernelL1 𝕜 (filtration (n + 1)) x -
        PL1.ExplicitMartingale.kernelL1 𝕜 (filtration n) x)‖ := by
  let ν := PL1.Noise.resolventMeasure (rates A) 1
  let := PL1.Noise.isProbabilityMeasure_resolventMeasure (rates A) (by norm_num : (0 : ℝ) < 1)
  let d := filtration n
  let B := blockEvent s d
  have hBm : MeasurableSet B := measurableSet_blockEvent s d
  have hhaar : PL1.Walsh.haar.real B ≤ errorBound s := by
    change (PL1.Walsh.haar (blockEvent s d)).toReal ≤ errorBound s
    have h := ENNReal.toReal_mono (by simp : ENNReal.ofReal (errorBound s) ≠ ⊤)
      (haar_blockEvent_le hs d)
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ errorBound s by unfold errorBound; positivity)] using h
  have hcompl : ν.real Bᶜ ≤ errorBound s + Real.exp (-(s : ℝ)) := by
    change (PL1.Noise.resolventMeasure (rates A) 1 (blockEvent s (filtration n))ᶜ).toReal ≤ _
    have h := resolvent_blockEvent_compl_le hs A hsA
      (filtration_block_start_ge hs hlower hupper) (filtration_block_end_le hs hlower hupper)
    have h' := ENNReal.toReal_mono
      (by simp : ENNReal.ofReal (errorBound s) + ENNReal.ofReal (Real.exp (-(s : ℝ))) ≠ ⊤) h
    rw [ENNReal.toReal_add (by simp) (by simp)] at h'
    simpa only [
      ENNReal.toReal_ofReal (show 0 ≤ errorBound s by unfold errorBound; positivity),
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using h'
  have hmass : ν.real B + ν.real Bᶜ = 1 := by
    simpa only [probReal_univ] using measureReal_add_measureReal_compl (μ := ν) hBm
  have hgap : stageLowerBound s ≤ 2 * (ν.real B - PL1.Walsh.haar.real B) := by
    unfold stageLowerBound
    linarith
  apply hgap.trans
  change 2 * (ν.real B - PL1.Walsh.haar.real B) ≤
    ‖PL1.Walsh.convolutionL1 (𝕜 := 𝕜) ν
      (PL1.ExplicitMartingale.kernelL1 𝕜 (filtration (n + 1)) x -
        PL1.ExplicitMartingale.kernelL1 𝕜 (filtration n) x)‖
  exact FiniteExpectations.norm_increment_ge_event_gap 𝕜
    (blockCoordinates d (blockSize s)) (filtration n) (filtration (n + 1))
    (blockCoordinates_subset_next hs hlower hupper)
    (blockCoordinates_disjoint_previous d (blockSize s)) ν x B hBm (dependsOn_blockEvent s d)

theorem levelSeminorm_stage_ge {s n : ℕ} (hs : 0 < s) (A : Set ℕ) (hsA : s ∈ A)
    (hlower : levels (s - 1) ≤ n) (hupper : n < levels s) :
    stageLowerBound s ≤ levelSeminorm 𝕜 (HaarL1 𝕜) filtration n (unitResolvent 𝕜 (rates A)) := by
  classical
  let ι := PL1.FiniteCoordinateKernels.Assignments (Finset.range (filtration (n + 1)))
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change stageLowerBound s ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ a : ι, _
  calc
    stageLowerBound s = (Fintype.card ι : ℝ)⁻¹ * ∑ _a : ι, stageLowerBound s := by simp [hc]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun a _ => resolvent_stage_increment_ge 𝕜 hs A hsA hlower hupper _))
      (by positivity)

theorem endpointSeminorm_stage_ge {s : ℕ} (hs : 0 < s) (A : Set ℕ) (hsA : s ∈ A) :
    ((repetitions s : ℝ) / levels s) * stageLowerBound s ≤
      endpointSeminorm 𝕜 (HaarL1 𝕜) filtration levels s (unitResolvent 𝕜 (rates A)) := by
  classical
  let f := fun n => levelSeminorm 𝕜 (HaarL1 𝕜) filtration n (unitResolvent 𝕜 (rates A))
  have hrec : levels s = levels (s - 1) + repetitions s := by
    simpa [Nat.sub_add_cancel hs] using levels_succ (s - 1)
  have hsum : (repetitions s : ℝ) * stageLowerBound s ≤ ∑ n ∈ Finset.range (levels s), f n := by
    rw [hrec, Finset.sum_range_add]
    calc
      _ = ∑ _j ∈ Finset.range (repetitions s), stageLowerBound s := by simp
      _ ≤ ∑ j ∈ Finset.range (repetitions s), f (levels (s - 1) + j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact levelSeminorm_stage_ge 𝕜 hs A hsA (by omega)
          (by have hj' := Finset.mem_range.mp hj; omega)
      _ ≤ _ := le_add_of_nonneg_left (Finset.sum_nonneg (fun n _ => apply_nonneg _ _))
  change _ ≤ averageSeminorm (levelSeminorm 𝕜 (HaarL1 𝕜) filtration) (levels s) _
  rw [averageSeminorm_apply]
  calc
    _ = (levels s : ℝ)⁻¹ * ((repetitions s : ℝ) * stageLowerBound s) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

theorem averagedVariation_unitResolvent_eq_two (A H : Set ℕ) (hH : H.Infinite)
    (hHA : H ⊆ A) :
    averagedVariation 𝕜 (HaarL1 𝕜) filtration levels H hH (unitResolvent 𝕜 (rates A)) = 2 := by
  let l := atTop ⊓ 𝓟 H
  let := alongInfinite_neBot hH
  have hupper : ∀ s, endpointSeminorm 𝕜 (HaarL1 𝕜) filtration levels s
      (unitResolvent 𝕜 (rates A)) ≤ 2 := by
    intro s
    simpa [norm_unitResolvent] using
      endpointSeminorm_le 𝕜 (HaarL1 𝕜) filtration levels s (unitResolvent 𝕜 (rates A))
  have hlower : ∀ᶠ s in l, ((repetitions s : ℝ) / levels s) * stageLowerBound s ≤
      endpointSeminorm 𝕜 (HaarL1 𝕜) filtration levels s (unitResolvent 𝕜 (rates A)) := by
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop 1] with s hs hsH
    exact endpointSeminorm_stage_ge 𝕜 hs A (hHA hsH)
  have ht : Tendsto (fun s => ((repetitions s : ℝ) / levels s) * stageLowerBound s)
      l (𝓝 2) := by
    have h := final_stage_proportion_tendsto.mul stageLowerBound_tendsto
    have h' : Tendsto (fun s => ((repetitions s : ℝ) / levels s) * stageLowerBound s)
        atTop (𝓝 2) := by simpa only [one_mul] using h
    exact h'.mono_left inf_le_left
  have hlim : Tendsto (fun s => endpointSeminorm 𝕜 (HaarL1 𝕜) filtration levels s
      (unitResolvent 𝕜 (rates A))) l (𝓝 2) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' ht tendsto_const_nhds hlower
      (Eventually.of_forall hupper)
  exact hlim.limsup_eq

end PL1CD
