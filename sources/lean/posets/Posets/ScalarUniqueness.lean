import Posets.OperatorLemmas
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! The scalar and separable remainder in Section 6 are unique even when
the domain and range differ. These proofs work on the actual operator spaces. -/
noncomputable section
open TopologicalSpace
namespace Posets
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem isometry_not_separable_range (hE : ¬ SeparableSpace E)
    (ι : E →L[𝕜] F) (hι : Isometry ι) : ¬ HasSeparableRange 𝕜 E F ι := by
  intro hsep
  have h := hι.isEmbedding.isSeparable_preimage hsep
  have heq : ι ⁻¹' Set.range ι = Set.univ := Set.eq_univ_of_forall (fun x => ⟨x, rfl⟩)
  rw [heq] at h
  exact hE (isSeparable_univ_iff.mp h)

theorem scalar_embedding_separable_iff (hE : ¬ SeparableSpace E)
    (ι : E →L[𝕜] F) (hι : Isometry ι) (a : 𝕜) :
    HasSeparableRange 𝕜 E F (a • ι) ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    apply isometry_not_separable_range hE ι hι
    have h' := h.smul a⁻¹
    simpa [smul_smul, ha] using h'
  · rintro rfl
    simpa using (JFA.hasSeparableRange_zero (𝕜 := 𝕜) (E := E) (F := F))

theorem scalar_decomposition_unique_between (hE : ¬ SeparableSpace E)
    (ι : E →L[𝕜] F) (hι : Isometry ι)
    {T S R : E →L[𝕜] F} {a b : 𝕜}
    (hS : HasSeparableRange 𝕜 E F S) (hR : HasSeparableRange 𝕜 E F R)
    (ha : T = a • ι + S) (hb : T = b • ι + R) : a = b ∧ S = R := by
  have hsub : (a - b) • ι = R - S := by
    rw [sub_smul]
    exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa [add_comm] using ha.symm.trans hb)
  have hzero := (scalar_embedding_separable_iff hE ι hι (a - b)).mp (hsub ▸ hR.sub hS)
  have hab := sub_eq_zero.mp hzero
  refine ⟨hab, ?_⟩
  rw [hab] at ha
  exact add_left_cancel (ha.symm.trans hb)

/-- The unique decomposition actually used for the block matrix θ(T) in 6.6
and 6.21. Existence is the stated few-operator hypothesis; uniqueness is proved. -/
theorem fewOperators_unique_between {P : Type*} [PartialOrder P] {X : P → Type*}
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι)
    {s t : P} (hst : s ≤ t) (T : X s →L[𝕜] X t) :
    ∃! d : 𝕜 × (X s →L[𝕜] X t),
      HasSeparableRange 𝕜 (X s) (X t) d.2 ∧ T = d.1 • ι s t + d.2 := by
  obtain ⟨a, S, hS, ha⟩ := h.2.2.2.2.1 s t hst T
  refine ⟨(a, S), ⟨hS, ha⟩, ?_⟩
  rintro ⟨b, R⟩ ⟨hR, hb⟩
  obtain ⟨hba, hRS⟩ := scalar_decomposition_unique_between (h.1 s) (ι s t)
    (h.2.1 s t hst) hR hS hb ha
  exact Prod.ext hba hRS

end Posets
