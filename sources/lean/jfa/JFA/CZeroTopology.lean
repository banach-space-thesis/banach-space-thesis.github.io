import JFA.DualBall
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Metrizable.Basic

/-! The topological hypothesis in Corollary 1.3 gives nonseparability of C₀(L).
Point evaluations embed L in the weak-star dual unit ball; compactly supported
Urysohn functions show that the embedding recovers the original topology. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology Filter Set
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {L : Type*} [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L]

theorem exists_czero_bump (x : L) {U : Set L} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ f : C₀(L, 𝕜), f x = 1 ∧ ∀ y ∉ U, f y = 0 := by
  obtain ⟨f, hfx, hfzero, hcompact, hbounds⟩ :=
    exists_continuous_one_zero_of_isCompact (s := {x}) (t := Uᶜ)
      isCompact_singleton hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (singleton_subset_iff.mpr hx))
  let g : C₀(L, 𝕜) := {
    toFun := fun y => RCLike.ofReal (f y)
    continuous_toFun := RCLike.continuous_ofReal.comp f.continuous
    zero_at_infty' := by
      simpa only [RCLike.ofReal_zero] using
        (RCLike.continuous_ofReal.tendsto 0).comp hcompact.is_zero_at_infty }
  refine ⟨g, ?_, ?_⟩
  · change RCLike.ofReal (f x) = 1
    rw [hfx (mem_singleton x), Pi.one_apply, RCLike.ofReal_one]
  · intro y hy
    change RCLike.ofReal (f y) = 0
    rw [hfzero hy, Pi.zero_apply, RCLike.ofReal_zero]

def czeroEvaluation (x : L) : C₀(L, 𝕜) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous (E := C₀(L, 𝕜)) (F := 𝕜) {
    toFun := fun f => f x
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
    1 (fun f => by simpa only [one_mul] using f.toBCF.norm_coe_le_norm x)

omit [LocallyCompactSpace L] [T2Space L] in
theorem norm_czeroEvaluation_le (x : L) : ‖czeroEvaluation (𝕜 := 𝕜) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using f.toBCF.norm_coe_le_norm x

def czeroDualEvaluation (x : L) : DualBall 𝕜 C₀(L, 𝕜) :=
  ⟨StrongDual.toWeakDual (czeroEvaluation (𝕜 := 𝕜) x), by
    change dist (czeroEvaluation (𝕜 := 𝕜) x) 0 ≤ 1
    rw [(inferInstance : NormedAddCommGroup (C₀(L, 𝕜) →L[𝕜] 𝕜)).dist_eq, sub_zero]
    exact norm_czeroEvaluation_le (𝕜 := 𝕜) x⟩

omit [LocallyCompactSpace L] [T2Space L] in
theorem continuous_czeroDualEvaluation :
    Continuous (czeroDualEvaluation (𝕜 := 𝕜) (L := L)) := by
  apply Continuous.subtype_mk
  apply WeakDual.continuous_of_continuous_eval
  intro f
  exact f.continuous

theorem czeroDualEvaluation_injective :
    Function.Injective (czeroDualEvaluation (𝕜 := 𝕜) (L := L)) := by
  intro x y h
  by_contra hxy
  obtain ⟨f, hfx, hfy⟩ := exists_czero_bump (𝕜 := 𝕜) x isClosed_singleton.isOpen_compl hxy
  have heq := congrArg (fun φ : DualBall 𝕜 C₀(L, 𝕜) => φ.val f) h
  change f x = f y at heq
  rw [hfx, hfy y (by simp)] at heq
  exact one_ne_zero heq

theorem czeroDualEvaluation_isInducing :
    Topology.IsInducing (czeroDualEvaluation (𝕜 := 𝕜) (L := L)) := by
  apply isInducing_iff_nhds.mpr
  intro x
  apply le_antisymm continuous_czeroDualEvaluation.continuousAt.le_comap
  intro s hs
  obtain ⟨U, hUs, hU, hxU⟩ := mem_nhds_iff.mp hs
  obtain ⟨f, hfx, hfzero⟩ := exists_czero_bump (𝕜 := 𝕜) x hU hxU
  let V : Set (DualBall 𝕜 C₀(L, 𝕜)) := {φ | φ.val f ≠ 0}
  have hVopen : IsOpen V :=
    isClosed_singleton.isOpen_compl.preimage
      ((WeakDual.eval_continuous f).comp continuous_subtype_val)
  have hxV : czeroDualEvaluation (𝕜 := 𝕜) x ∈ V := by
    change f x ≠ 0
    rw [hfx]
    exact one_ne_zero
  apply Filter.mem_comap.mpr
  refine ⟨V, hVopen.mem_nhds hxV, ?_⟩
  intro y hy
  apply hUs
  by_contra hyU
  exact hy (hfzero y hyU)

theorem czeroDualEvaluation_isEmbedding :
    Topology.IsEmbedding (czeroDualEvaluation (𝕜 := 𝕜) (L := L)) :=
  ⟨czeroDualEvaluation_isInducing, czeroDualEvaluation_injective⟩

theorem metrizable_of_czero_separable [SeparableSpace C₀(L, 𝕜)] : MetrizableSpace L := by
  have hemb := (dualBallCoordinates_isClosedEmbedding (𝕜 := 𝕜) (F := C₀(L, 𝕜))).isEmbedding.comp
    (czeroDualEvaluation_isEmbedding (𝕜 := 𝕜) (L := L))
  exact hemb.metrizableSpace

theorem czero_nonseparable_of_nonmetrizable (hL : ¬ MetrizableSpace L) :
    ¬ SeparableSpace C₀(L, 𝕜) := by
  intro hsep
  letI := hsep
  exact hL (metrizable_of_czero_separable (𝕜 := 𝕜))

end JFA
