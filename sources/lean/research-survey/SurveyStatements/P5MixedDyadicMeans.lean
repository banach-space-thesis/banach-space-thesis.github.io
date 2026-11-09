import SurveyStatements.P5VectorPartitionTree
import SurveyStatements.P5MixedPointwiseMultiplication
import SurveyStatements.P5Support.LpHaarNestedMeans
import SurveyStatements.P5HaarBiorthogonal

/-! Contractive dyadic means and bounded rectangular tail/level pieces on
the actual mixed space. These pieces underlie the bi-tree variation estimates. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem standard_forward_eq_dyadicMean (hp : p ≠ ∞) (n : ℕ) :
    P5Support.LpHaarPartitionTree.standard.forward 𝕜 ⟨p, Fact.out⟩ hp n =
      P5Support.lpHaarDyadicMean 𝕜 ⟨p, Fact.out⟩ hp n := by
  apply ContinuousLinearMap.ext
  intro f
  change P5Support.lpHaarPartitionTransfer hp
    (fun k : Fin (2 ^ n) => P5Support.lpHaarCell n k)
    (fun k : Fin (2 ^ n) => P5Support.lpHaarCell n k)
    (fun _ => measurableSet_Ioc) f = _
  rw [P5Support.lpHaarPartitionTransfer_apply, P5Support.lpHaarDyadicMean,
    P5Support.lpHaarPartitionMean_eq_step]

def mixedOuterDyadicMean (hp : p ≠ ∞) (n : ℕ) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  VectorPartitionTree.forward P5Support.LpHaarPartitionTree.standard hp n

def mixedInnerDyadicMean (n : ℕ) : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (P5Support.lpHaarDyadicMean 𝕜 ⟨1, le_rfl⟩ (by norm_num) n).compLpL
    p unitIntervalMeasure

theorem norm_mixedOuterDyadicMean_le (hp : p ≠ ∞) (n : ℕ) :
    ‖mixedOuterDyadicMean (𝕜 := 𝕜) hp n‖ ≤ 1 :=
  VectorPartitionTree.forward_norm_le _ hp n

theorem norm_mixedInnerDyadicMean_le (n : ℕ) :
    ‖mixedInnerDyadicMean (𝕜 := 𝕜) (p := p) n‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le _).trans
    (P5Support.lpHaarDyadicMean_norm_le 𝕜 ⟨1, le_rfl⟩ (by norm_num) n)

theorem mixedOuterDyadicMean_tensor (hp : p ≠ ∞) (n : ℕ)
    (g : Lp 𝕜 1 unitIntervalMeasure) (f : Lp 𝕜 p unitIntervalMeasure) :
    mixedOuterDyadicMean hp n (tensorWith g f) =
      tensorWith g (P5Support.lpHaarDyadicMean 𝕜 ⟨p, Fact.out⟩ hp n f) := by
  change VectorPartitionTree.forward P5Support.LpHaarPartitionTree.standard hp n
    (vectorTensor (𝕜 := 𝕜) g f) = vectorTensor (𝕜 := 𝕜) g _
  rw [VectorPartitionTree.forward_tensor, standard_forward_eq_dyadicMean]

theorem mixedInnerDyadicMean_tensor (n : ℕ)
    (g : Lp 𝕜 1 unitIntervalMeasure) (f : Lp 𝕜 p unitIntervalMeasure) :
    mixedInnerDyadicMean n (tensorWith g f) =
      tensorWith (P5Support.lpHaarDyadicMean 𝕜 ⟨1, le_rfl⟩ (by norm_num) n g) f :=
  mixedInnerMap_tensor _ _ _

theorem scalarDyadicMean_haar (hp : p ≠ ∞) (n : ℕ) (I : DyadicIndex) :
    P5Support.lpHaarDyadicMean 𝕜 ⟨p, Fact.out⟩ hp n (dyadicHaar 𝕜 p I) =
      if I.1 < n then dyadicHaar 𝕜 p I else 0 := by
  simp only [dyadicHaar_eq_support]
  change P5Support.lpHaarDyadicMean 𝕜 ⟨p, Fact.out⟩ hp n
    (P5Support.lpHaarDyadic 𝕜 ⟨p, Fact.out⟩ I.1 I.2) = _
  by_cases h : I.1 < n
  · rw [if_pos h]
    exact P5Support.lpHaarDyadicMean_fix_earlier_haar 𝕜 ⟨p, Fact.out⟩ hp
      I.1 n I.2 I.2.isLt h
  · rw [if_neg h]
    exact P5Support.lpHaarDyadicMean_kill_later_haar 𝕜 ⟨p, Fact.out⟩ hp
      I.1 n I.2 I.2.isLt (Nat.le_of_not_gt h)

def mixedLowerStrip (hp : p ≠ ∞) (n j : ℕ) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p) - mixedOuterDyadicMean hp n).comp
    (mixedInnerDyadicMean (j + 1) - mixedInnerDyadicMean j)

theorem norm_mixedLowerStrip_le (hp : p ≠ ∞) (n j : ℕ) :
    ‖mixedLowerStrip (𝕜 := 𝕜) hp n j‖ ≤ 4 := by
  have htail : ‖ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p) -
      mixedOuterDyadicMean hp n‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      have hid : ‖ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p)‖ ≤ 1 :=
        ContinuousLinearMap.norm_id_le
      linarith [norm_mixedOuterDyadicMean_le (𝕜 := 𝕜) hp n])
  have hlevel : ‖mixedInnerDyadicMean (𝕜 := 𝕜) (p := p) (j + 1) -
      mixedInnerDyadicMean j‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      have h := add_le_add (norm_mixedInnerDyadicMean_le (𝕜 := 𝕜) (p := p) (j + 1))
        (norm_mixedInnerDyadicMean_le (𝕜 := 𝕜) (p := p) j)
      simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using h)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
      mul_le_mul htail hlevel (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2))

end SurveyStatements.P5
