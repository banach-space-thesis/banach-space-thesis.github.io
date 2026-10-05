import ThesisCommon.Analysis.BooleanStoneExtremallyDisconnected
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.LocallyConstant.Basic

/-! Uniform approximation of real or complex continuous functions on a
Boolean Stone space by locally constant functions, with an actual finite
decomposition over Stone clopens. No countability assumption is required. -/
noncomputable section
open Set TopologicalSpace
open scoped Classical
namespace ThesisCommon
variable {B 𝕜 : Type*} [BooleanAlgebra B] [RCLike 𝕜]

def booleanStoneLocallyConstantAlgebra : StarSubalgebra 𝕜 C(BooleanStonePoint B, 𝕜) where
  carrier := {f | IsLocallyConstant f}
  zero_mem' := IsLocallyConstant.zero
  one_mem' := IsLocallyConstant.one
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  algebraMap_mem' r := IsLocallyConstant.const r
  star_mem' hf := hf.comp star

theorem booleanStoneLocallyConstantAlgebra_separatesPoints :
    (booleanStoneLocallyConstantAlgebra (B := B) (𝕜 := 𝕜)).SeparatesPoints := by
  classical
  intro p q hpq
  obtain ⟨a, hpa, hqa⟩ := exists_booleanStoneSet_separating_points p q hpq
  let h : Bool → 𝕜 := fun b => if b then 1 else 0
  have hlc : IsLocallyConstant (fun p : BooleanStonePoint B => h (booleanStoneHom p a)) :=
    ((IsLocallyConstant.iff_continuous _).mpr (continuous_booleanStoneEval a)).comp h
  refine ⟨_, ⟨⟨_, hlc.continuous⟩, hlc, rfl⟩, ?_⟩
  change h (booleanStoneHom p a) ≠ h (booleanStoneHom q a)
  change booleanStoneHom p a = true at hpa
  change ¬ booleanStoneHom q a = true at hqa
  simp [h, hpa, Bool.eq_false_iff.mpr hqa]

theorem dense_booleanStone_locallyConstant :
    Dense {f : C(BooleanStonePoint B, 𝕜) | IsLocallyConstant f} := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (booleanStoneLocallyConstantAlgebra (B := B) (𝕜 := 𝕜))
    booleanStoneLocallyConstantAlgebra_separatesPoints
  rw [dense_iff_closure_eq]
  change closure (booleanStoneLocallyConstantAlgebra (B := B) (𝕜 := 𝕜) :
    Set C(BooleanStonePoint B, 𝕜)) = univ
  exact congrArg (fun A : StarSubalgebra 𝕜 C(BooleanStonePoint B, 𝕜) =>
    (A : Set C(BooleanStonePoint B, 𝕜))) h

theorem exists_booleanStone_locallyConstant_approximation
    (f : C(BooleanStonePoint B, 𝕜)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(BooleanStonePoint B, 𝕜), IsLocallyConstant g ∧ ‖f - g‖ < ε := by
  obtain ⟨g, hg, hdist⟩ := dense_booleanStone_locallyConstant.exists_dist_lt f hε
  exact ⟨g, hg, by simpa only [dist_eq_norm] using hdist⟩

theorem exists_booleanStone_sum_of_locallyConstant
    (g : C(BooleanStonePoint B, 𝕜)) (hg : IsLocallyConstant g) :
    ∃ s : Finset 𝕜, ∃ a : 𝕜 → B,
      ∀ p, g p = ∑ c ∈ s, if p ∈ booleanStoneSet (a c) then c else 0 := by
  classical
  choose a ha using fun c : 𝕜 => exists_booleanStoneSet_eq_of_isClopen (hg.isClopen_fiber c)
  refine ⟨hg.range_finite.toFinset, a, ?_⟩
  intro p
  simp only [ha, mem_setOf_eq]
  have hmem : g p ∈ hg.range_finite.toFinset := by simp
  rw [Finset.sum_eq_single (g p)]
  · simp
  · intro c hc hne
    simp [Ne.symm hne]
  · exact fun h => False.elim (h hmem)

end ThesisCommon
