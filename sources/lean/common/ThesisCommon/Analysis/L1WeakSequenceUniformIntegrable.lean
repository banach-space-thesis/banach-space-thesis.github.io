import ThesisCommon.Analysis.ComplexL1WeakUniformIntegrable
import Mathlib.Topology.Sequences

/-! Weakly convergent real and complex L1 sequences are uniformly absolutely
continuous on arbitrary measure spaces. The proof uses actual weak compact
closures, with real coordinates for complex families. -/
noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal
namespace ThesisCommon
variable {Y I : Type*} [MeasurableSpace Y] {ν : Measure Y}

theorem isCompact_weakComplexL1_uniform_cut
    {K : Set (WeakSpace ℂ (Lp ℂ 1 ν))} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : Lp ℂ 1 ν, toWeakSpace ℂ (Lp ℂ 1 ν) f ∈ K →
      ∀ A, ∀ hA : MeasurableSet A, ν A ≤ ENNReal.ofReal δ → ‖lpCut A hA f‖ ≤ ε := by
  let j := weakSpaceRealHomeomorph (𝕜 := ℂ) (E := Lp ℂ 1 ν)
  let jr := fun x => WeakSpace.map (complexL1Re ν) (j x)
  let ji := fun x => WeakSpace.map (complexL1Im ν) (j x)
  have hjr : Continuous jr := (WeakSpace.map (complexL1Re ν)).continuous.comp j.continuous
  have hji : Continuous ji := (WeakSpace.map (complexL1Im ν)).continuous.comp j.continuous
  obtain ⟨δ, hδ, hr⟩ := isCompact_weakL1_uniform_cut (hK.image hjr) (half_pos hε)
  obtain ⟨η, hη, hi⟩ := isCompact_weakL1_uniform_cut (hK.image hji) (half_pos hε)
  refine ⟨min δ η, lt_min hδ hη, fun f hf A hA hνA => ?_⟩
  have hreal := hr (complexL1Re ν f) ⟨_, hf, rfl⟩ A hA
    (hνA.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
  have himag := hi (complexL1Im ν f) ⟨_, hf, rfl⟩ A hA
    (hνA.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  have hn := norm_complexL1_le_coordinates (lpCut A hA f)
  rw [complexL1Re_cut, complexL1Im_cut] at hn
  linarith

theorem isCompact_weakComplexL1_unifIntegrable
    (f : I → Lp ℂ 1 ν) {K : Set (WeakSpace ℂ (Lp ℂ 1 ν))} (hK : IsCompact K)
    (hf : ∀ i, toWeakSpace ℂ (Lp ℂ 1 ν) (f i) ∈ K) :
    UnifIntegrable (fun i => (f i : Y → ℂ)) 1 ν := by
  intro ε hε
  obtain ⟨δ, hδ, hcut⟩ := isCompact_weakComplexL1_uniform_cut hK hε
  refine ⟨δ, hδ, fun i A hA hνA => ?_⟩
  apply (ENNReal.toReal_le_toReal ((Lp.memLp (f i)).indicator hA).2.ne
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hε.le]
  simpa only [lpCut, Lp.norm_toLp] using hcut (f i) (hf i) A hA hνA

theorem unifIntegrable_of_real_lOne_weak_tendsto
    (f : ℕ → Lp ℝ 1 ν) {l : Lp ℝ 1 ν}
    (hf : Tendsto (fun n => toWeakSpace ℝ (Lp ℝ 1 ν) (f n)) atTop
      (𝓝 (toWeakSpace ℝ (Lp ℝ 1 ν) l))) :
    UnifIntegrable (fun n => (f n : Y → ℝ)) 1 ν :=
  isCompact_weakL1_unifIntegrable f hf.isCompact_insert_range
    (fun n => Set.mem_insert_of_mem _ (Set.mem_range_self n))

theorem unifIntegrable_of_complex_lOne_weak_tendsto
    (f : ℕ → Lp ℂ 1 ν) {l : Lp ℂ 1 ν}
    (hf : Tendsto (fun n => toWeakSpace ℂ (Lp ℂ 1 ν) (f n)) atTop
      (𝓝 (toWeakSpace ℂ (Lp ℂ 1 ν) l))) :
    UnifIntegrable (fun n => (f n : Y → ℂ)) 1 ν :=
  isCompact_weakComplexL1_unifIntegrable f hf.isCompact_insert_range
    (fun n => Set.mem_insert_of_mem _ (Set.mem_range_self n))

end ThesisCommon
