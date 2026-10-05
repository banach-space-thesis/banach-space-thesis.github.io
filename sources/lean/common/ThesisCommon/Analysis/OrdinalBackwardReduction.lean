import ThesisCommon.Analysis.OrdinalBakerCover
import ThesisCommon.Analysis.OrdinalClosedCopies
import ThesisCommon.Analysis.ContinuousMapSmallSets

/-! LPCK Lemma 3.11 on compact ordinal intervals of characteristic (η,1).
The finite closed cover selects an actual closed copy; the scalar small-set
estimate controls the whole restricted operator, including at infinity. -/
noncomputable section
open Set Topology
open scoped ENNReal
universe u
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem ordinal_characteristic_one_subspace_cover {α η a : Ordinal.{u}}
    (hD : ordinalDerived (Icc 0 α) η = {a}) {ι : Type*} [Finite ι]
    (B : ι → Set (OrdinalInterval α)) (hB : ∀ i, IsClosed (B i))
    (hcover : ⋃ i, B i = univ) :
    ∃ i, ∃ f : OrdinalClosedCopy α α, ∀ x, f.val x ∈ B i := by
  let C : ι → Set Ordinal.{u} := fun i => Subtype.val '' B i
  have hC : ∀ i, IsClosed (C i) := fun i =>
    isClosed_Icc.isClosedEmbedding_subtypeVal.isClosedMap _ (hB i)
  have hUnion : Icc 0 α = ⋃ i, C i := by
    ext x
    constructor
    · intro hx
      have hxb : (⟨x, hx⟩ : OrdinalInterval α) ∈ ⋃ i, B i := by rw [hcover]; trivial
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxb
      exact mem_iUnion.mpr ⟨i, ⟨⟨x, hx⟩, hi, rfl⟩⟩
    · intro hx
      obtain ⟨i, y, _, hy⟩ := mem_iUnion.mp hx
      exact hy ▸ y.property
  obtain ⟨i, f, hf, hfi⟩ := ordinal_characteristic_one_closed_cover
    isCompact_Icc hD C hC hUnion
  refine ⟨i, ⟨f, hf⟩, ?_⟩
  intro x
  obtain ⟨y, hy, hyf⟩ := hfi x
  have heq : y = f x := Subtype.ext hyf
  simpa only [heq] using hy

theorem ordinal_characteristic_one_lp_backward_reduction {α η a : Ordinal.{u}}
    (hD : ordinalDerived (Icc 0 α) η = {a}) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p = ∞ ∨ 1 < p.toReal)
    (T : lp (fun _ : ℕ => X) p →L[𝕜] OrdinalContinuous 𝕜 α)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, ∃ f : OrdinalClosedCopy α α,
      ‖(ordinalCopyRead f).comp (T.comp (lpExtend p e))‖ ≤ ε := by
  have hcover : ∃ N : ℕ, ∀ t : OrdinalInterval α, ∃ i : Fin N,
      t ∈ continuousMapSmallSet (T.comp (lpExtend p (disjointCoordinateEmbedding i))) ε := by
    rcases hp with rfl | hp
    · exact infinity_continuousMap_small_sets_cover T hε
    · exact lp_continuousMap_small_sets_cover hp T hε
  obtain ⟨N, hN⟩ := hcover
  let B : Fin N → Set (OrdinalInterval α) := fun i =>
    continuousMapSmallSet (T.comp (lpExtend p (disjointCoordinateEmbedding i))) ε
  have hB : ∀ i, IsClosed (B i) := fun i => isClosed_continuousMapSmallSet _ _
  have hUnion : ⋃ i, B i = univ := by
    ext t
    simp only [mem_iUnion, mem_univ, iff_true]
    exact hN t
  obtain ⟨i, f, hf⟩ := ordinal_characteristic_one_subspace_cover hD B hB hUnion
  refine ⟨disjointCoordinateEmbedding i, f, ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro x hx
  apply (ContinuousMap.norm_le _ hε.le).2
  intro t
  exact hf t x hx.le

end ThesisCommon
