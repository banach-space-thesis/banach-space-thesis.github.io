import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.ContinuousOn

/-!
# Local Lipschitz maps on a compact source are globally Lipschitz

A finite open cover gives a maximum local constant and a Lebesgue number.
Close pairs lie in one chart; far pairs are controlled by the diameter of the
actual compact image. No global Lipschitz property is included as a premise.
-/

namespace BanachIsometric

open Set Metric
open scoped NNReal Topology

theorem exists_lipschitzWith_of_finite_open_cover
    {P W ι : Type*} [PseudoMetricSpace P] [CompactSpace P] [PseudoMetricSpace W]
    [Fintype ι] (f : P → W) (U : ι → Set P)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ)
    (L : ι → ℝ≥0) (hLip : ∀ i, LipschitzOnWith (L i) f (U i)) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  classical
  have hcont : Continuous f := continuous_of_continuousOn_iUnion_of_isOpen
    (fun i ↦ (hLip i).continuousOn) hU hcover
  obtain ⟨B, hB⟩ := isBounded_range_iff.mp (isCompact_range hcont).isBounded
  obtain ⟨δ, hδ, hδcover⟩ := lebesgue_number_lemma_of_metric
    (isCompact_univ : IsCompact (univ : Set P)) hU (by rw [hcover])
  let K₀ : ℝ≥0 := ∑ i, L i
  let M : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  let δn : ℝ≥0 := ⟨δ, hδ.le⟩
  refine ⟨max K₀ (M / δn), LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  by_cases hclose : dist x y < δ
  · obtain ⟨i, hi⟩ := hδcover x (mem_univ x)
    have hx : x ∈ U i := hi (mem_ball_self hδ)
    have hy : y ∈ U i := hi (by simpa only [mem_ball, dist_comm] using hclose)
    have hLi : L i ≤ K₀ := Finset.single_le_sum (fun _ _ ↦ zero_le _) (Finset.mem_univ i)
    calc
      dist (f x) (f y) ≤ (L i : ℝ) * dist x y := (hLip i).dist_le_mul x hx y hy
      _ ≤ ((max K₀ (M / δn) : ℝ≥0) : ℝ) * dist x y :=
        mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr (hLi.trans (le_max_left _ _))) dist_nonneg
  · have hfar : δ ≤ dist x y := le_of_not_gt hclose
    have hMfar : (M : ℝ) ≤ ((M / δn : ℝ≥0) : ℝ) * dist x y := by
      change max B 0 ≤ (max B 0 / δ) * dist x y
      calc
        max B 0 = (max B 0 / δ) * δ := (div_mul_cancel₀ _ hδ.ne').symm
        _ ≤ (max B 0 / δ) * dist x y :=
          mul_le_mul_of_nonneg_left hfar (div_nonneg (le_max_right _ _) hδ.le)
    calc
      dist (f x) (f y) ≤ B := hB x y
      _ ≤ (M : ℝ) := le_max_left _ _
      _ ≤ ((M / δn : ℝ≥0) : ℝ) * dist x y := hMfar
      _ ≤ ((max K₀ (M / δn) : ℝ≥0) : ℝ) * dist x y :=
        mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr (le_max_right _ _)) dist_nonneg

end BanachIsometric
