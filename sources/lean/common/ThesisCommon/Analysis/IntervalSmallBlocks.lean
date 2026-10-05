import ThesisCommon.Analysis.IntervalRetractions
import ThesisCommon.Analysis.CotypeUpperSelection

/-! Finite disjoint input blocks produce a small column after restriction
to a nondegenerate closed subinterval. This is the finite-cover step in
LPCK 4.1, valid for real and complex scalars. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem interval_exists_small_block {N : ℕ} (J : Fin N → X →L[𝕜] Y)
    (hJ : ∀ x : Fin N → X, (∀ i, ‖x i‖ ≤ 1) → ‖∑ i, J i (x i)‖ ≤ 1)
    (T : Y →L[𝕜] IntervalContinuous 𝕜) {M ε : ℝ} (hε : 0 ≤ ε)
    (hT : ‖T‖ ≤ M) (hlarge : M < (N : ℝ) * ε) :
    ∃ (i : Fin N) (c : NondegenerateUnitSubinterval),
      ‖((intervalRead c).comp T).comp (J i)‖ ≤ ε := by
  let A : Fin N → Set UnitInterval := fun i => continuousMapSmallSet (T.comp (J i)) ε
  have hcover : ⋃ i, A i = Set.univ := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact continuousMap_small_sets_cover J hJ T (by simpa only [mul_one] using hT.trans_lt hlarge) t
  obtain ⟨i, a, b, hab, hsub⟩ := unitInterval_closed_cover_contains_interval A
    (fun i => isClosed_continuousMapSmallSet _ _) hcover
  refine ⟨i, ⟨(a,b), hab⟩, ?_⟩
  rw [ContinuousLinearMap.comp_assoc]
  exact (norm_intervalRead_comp_le ⟨(a,b), hab⟩ (T.comp (J i))).trans
    (norm_restrict_le_of_continuousMapSmallSet _ _ hε hsub)

theorem interval_infinity_forward_reduction
    (T : EllInfinitySum X →L[𝕜] EllInfinitySum (IntervalContinuous 𝕜))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (e : ℕ ↪ ℕ) (c : ℕ → NondegenerateUnitSubinterval), ∀ k,
      ‖((intervalRead (c k)).comp ((lpCoordinate ∞ (e k)).comp T)).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) ∞ n)‖ ≤ ε := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (‖T‖ / ε)
  have hlarge : ‖T‖ < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  have hs : ∀ m : ℕ, ∃ (i : Fin N) (c : NondegenerateUnitSubinterval),
      ‖((intervalRead c).comp ((lpCoordinate ∞ m).comp T)).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) ∞ i.val)‖ ≤ ε := by
    intro m
    apply interval_exists_small_block _ ?_ _ hε.le
      (norm_comp_left_contraction _ (norm_lpCoordinate_le ∞ m) T) hlarge
    intro x hx
    simpa using infinity_single_embedding_sign_bound (𝕜 := 𝕜) Fin.valEmbedding x hx (fun _ => true)
  choose i c hs using hs
  obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber i
  have hj' : (i ⁻¹' {j}).Infinite := Set.infinite_coe_iff.mp hj
  let e : ℕ ↪ ℕ := (hj'.natEmbedding (i ⁻¹' {j})).trans (Function.Embedding.subtype _)
  refine ⟨j.val, e, (fun k => c (e k)), ?_⟩
  intro k
  have he : i (e k) = j := (hj'.natEmbedding (i ⁻¹' {j}) k).property
  simpa only [he] using hs (e k)

end ThesisCommon
