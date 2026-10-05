import ThesisCommon.Analysis.ContinuousMapSmallSets
import ThesisCommon.Analysis.ContinuousMapPullback
import ThesisCommon.Analysis.UnitIntervalClosedCopies

/-! LPCK Lemma 3.11 for K=[0,1], both finite p>1 and infinity. The chosen
closed copy is an actual nondegenerate subinterval. The estimate is for
the whole restricted operator, including all bounded sequences at infinity. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem norm_restrict_le_of_continuousMapSmallSet
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : X →L[𝕜] C(K, 𝕜)) (A : Set K) [CompactSpace A]
    {ε : ℝ} (hε : 0 ≤ ε) (hA : A ⊆ continuousMapSmallSet T ε) :
    ‖(continuousMapRestrict A).comp T‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε
  intro x hx
  apply (ContinuousMap.norm_le _ hε).2
  intro a
  exact hA a.property x hx.le

theorem interval_lp_backward_reduction {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p = ∞ ∨ 1 < p.toReal)
    (T : lp (fun _ : ℕ => X) p →L[𝕜] C(UnitInterval, 𝕜))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (a b : UnitInterval), a < b ∧
      ‖(continuousMapRestrict (Set.Icc a b)).comp (T.comp (lpExtend p e))‖ ≤ ε := by
  have hcover : ∃ N : ℕ, ∀ t : UnitInterval, ∃ i : Fin N,
      t ∈ continuousMapSmallSet (T.comp (lpExtend p (disjointCoordinateEmbedding i))) ε := by
    rcases hp with rfl | hp
    · exact infinity_continuousMap_small_sets_cover T hε
    · exact lp_continuousMap_small_sets_cover hp T hε
  obtain ⟨N, hN⟩ := hcover
  let A : Fin N → Set UnitInterval := fun i =>
    continuousMapSmallSet (T.comp (lpExtend p (disjointCoordinateEmbedding i))) ε
  have hclosed : ∀ i, IsClosed (A i) := fun i => isClosed_continuousMapSmallSet _ _
  have hUnion : ⋃ i, A i = Set.univ := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hN t
  obtain ⟨i, a, b, hab, hsub⟩ := unitInterval_closed_cover_contains_interval A hclosed hUnion
  exact ⟨disjointCoordinateEmbedding i, a, b, hab,
    norm_restrict_le_of_continuousMapSmallSet _ _ hε.le hsub⟩

end ThesisCommon
