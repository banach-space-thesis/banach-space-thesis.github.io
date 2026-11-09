import SurveyStatements.P5FaithfulTreeMaps
import SurveyStatements.P5FaithfulMixedTrees

/-! Concrete faithful mixed maps retaining the strong-limit maps needed for
exact compressed Haar symbols. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure FaithfulMixedData (𝕜 : Type*) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (Ho Hi : P5Support.LpHaarPartitionTree) (hp : p ≠ ∞) where
  outer : FaithfulTreeMaps 𝕜 (Lp 𝕜 1 unitIntervalMeasure) p Ho hp
  inner : FaithfulTreeMaps 𝕜 𝕜 1 Hi (by simp)

theorem exists_faithfulMixedData (Ho Hi : P5Support.LpHaarPartitionTree)
    (hp : p ≠ ∞) (hHo : Ho.FaithfulSplits) (hHi : Hi.FaithfulSplits) :
    Nonempty (FaithfulMixedData 𝕜 p Ho Hi hp) := by
  obtain ⟨Do⟩ := exists_faithfulTreeMaps (𝕜 := 𝕜)
    (E := Lp 𝕜 1 unitIntervalMeasure) Ho hp hHo
  obtain ⟨Di⟩ := exists_faithfulTreeMaps (𝕜 := 𝕜) (E := 𝕜) (p := 1) Hi (by simp) hHi
  exact ⟨⟨Do, Di⟩⟩

namespace FaithfulMixedData
variable {Ho Hi : P5Support.LpHaarPartitionTree} {hp : p ≠ ∞}
variable (D : FaithfulMixedData 𝕜 p Ho Hi hp)

def rawA : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (D.inner.A.compLpL p unitIntervalMeasure).comp D.outer.A

def rawB : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  D.outer.B.comp (D.inner.B.compLpL p unitIntervalMeasure)

theorem norm_rawA : ‖D.rawA‖ ≤ 1 := by
  have hi : ‖D.inner.A.compLpL p unitIntervalMeasure‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans D.inner.norm_A
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hi D.outer.norm_A (norm_nonneg _) zero_le_one).trans (by simp))

theorem norm_rawB : ‖D.rawB‖ ≤ 1 := by
  have hi : ‖D.inner.B.compLpL p unitIntervalMeasure‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans D.inner.norm_B
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul D.outer.norm_B hi (norm_nonneg _) zero_le_one).trans (by simp))

theorem raw_retraction : D.rawA.comp D.rawB = ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p) :=
  compression_composition_retraction _ _ _ _ D.outer.retraction
    (lift_retraction D.inner.A D.inner.B D.inner.retraction)

theorem rawA_mem (hHo : Ho.FaithfulSplits) (hHi : Hi.FaithfulSplits)
    (f : MixedNorm 𝕜 p) (hf : f ∈ DoublyZeroMean 𝕜 p) :
    D.rawA f ∈ DoublyZeroMean 𝕜 p := by
  have hi (g : Lp 𝕜 1 unitIntervalMeasure) :
      probabilityLpIntegral (𝕜 := 𝕜) (D.inner.A g) = probabilityLpIntegral (𝕜 := 𝕜) g :=
    VectorPartitionTree.backward_limit_integral Hi (by simp) hHi
      D.inner.A D.inner.backward_limit g
  exact innerLift_mem_doublyZeroMean D.inner.A hi (D.outer.A f)
    (VectorPartitionTree.backward_limit_mem_doublyZeroMean Ho hp hHo
      D.outer.A D.outer.backward_limit f hf)

theorem rawB_mem (f : MixedNorm 𝕜 p) (hf : f ∈ DoublyZeroMean 𝕜 p) :
    D.rawB f ∈ DoublyZeroMean 𝕜 p := by
  have hi (g : Lp 𝕜 1 unitIntervalMeasure) :
      probabilityLpIntegral (𝕜 := 𝕜) (D.inner.B g) = probabilityLpIntegral (𝕜 := 𝕜) g :=
    VectorPartitionTree.forward_limit_integral Hi (by simp) D.inner.B D.inner.forward_limit g
  exact VectorPartitionTree.forward_limit_mem_doublyZeroMean Ho hp
    D.outer.B D.outer.forward_limit _
    (innerLift_mem_doublyZeroMean D.inner.B hi f hf)

def A (hHo : Ho.FaithfulSplits) (hHi : Hi.FaithfulSplits) :
    DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
  (D.rawA.comp (DoublyZeroMean 𝕜 p).subtypeL).codRestrict (DoublyZeroMean 𝕜 p)
    (fun f => D.rawA_mem hHo hHi f.val f.property)

def B : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
  (D.rawB.comp (DoublyZeroMean 𝕜 p).subtypeL).codRestrict (DoublyZeroMean 𝕜 p)
    (fun f => D.rawB_mem f.val f.property)

@[simp] theorem A_val (hHo : Ho.FaithfulSplits) (hHi : Hi.FaithfulSplits)
    (f : DoublyZeroMean 𝕜 p) : (D.A hHo hHi f).val = D.rawA f.val := rfl

@[simp] theorem B_val (f : DoublyZeroMean 𝕜 p) : (D.B f).val = D.rawB f.val := rfl

theorem norm_A (hHo : Ho.FaithfulSplits) (hHi : Hi.FaithfulSplits) : ‖D.A hHo hHi‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using D.rawA.le_of_opNorm_le D.norm_rawA f.val

theorem norm_B : ‖D.B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using D.rawB.le_of_opNorm_le D.norm_rawB f.val

theorem retraction (hHo : Ho.FaithfulSplits) (hHi : Hi.FaithfulSplits) :
    (D.A hHo hHi).comp D.B = ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact congrArg (fun L : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p => L f.val) D.raw_retraction

end FaithfulMixedData
end SurveyStatements.P5
