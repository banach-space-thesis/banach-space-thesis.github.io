import Posets.OrdinalLiftSequences

/-! Compact gluing of shrinking pieces and separation of their images. -/
noncomputable section
open Set Filter Topology ThesisCommon
namespace Posets
variable {X Y : Type*} [MetricSpace X]

theorem ordinalLift_isCompact_insert_iUnion (x : X) (S : ℕ → Set X)
    (hS : ∀ n, IsCompact (S n))
    (hsmall : ∀ n, S n ⊆ Metric.ball x (1 / ((n : ℝ) + 1))) :
    IsCompact (insert x (⋃ n, S n)) := by
  classical
  apply isCompact_of_finite_subcover
  intro ι U hU hcover
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_insert x _))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU i) x hi
  have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hK : IsCompact (⋃ n ∈ Iio N, S n) := (finite_lt_nat N).isCompact_biUnion (fun n _ => hS n)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU (fun y hy =>
    hcover (mem_insert_of_mem x (by
      obtain ⟨n, _, hn⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion.mpr ⟨n, hn⟩)))
  refine ⟨insert i t, ?_⟩
  intro y hy
  rcases mem_insert_iff.mp hy with rfl | hy
  · exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self _ _, hi⟩
  obtain ⟨n, hn⟩ := mem_iUnion.mp hy
  by_cases hlt : n < N
  · obtain ⟨j, hjt, hj⟩ := mem_iUnion₂.mp (ht (mem_iUnion₂.mpr ⟨n, hlt, hn⟩))
    exact mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hjt, hj⟩
  · exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self _ _,
      hball ((Metric.ball_subset_ball (hN n (Nat.le_of_not_gt hlt)).le) (hsmall n hn))⟩

theorem ordinalLift_injOn_insert_iUnion (f : X → Y) (x : X)
    (S : ℕ → Set X) (W : ℕ → Set Y)
    (hS : ∀ n, S n ⊆ f ⁻¹' W n) (hinj : ∀ n, InjOn f (S n))
    (hroot : ∀ n, f x ∉ W n) (hdisj : Pairwise fun n m => Disjoint (W n) (W m)) :
    InjOn f (insert x (⋃ n, S n)) := by
  intro a ha b hb he
  rcases mem_insert_iff.mp ha with rfl | ha
  · rcases mem_insert_iff.mp hb with rfl | hb
    · rfl
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hb
      exact False.elim (hroot n (he ▸ hS n hn))
  · obtain ⟨n, hn⟩ := mem_iUnion.mp ha
    rcases mem_insert_iff.mp hb with rfl | hb
    · exact False.elim (hroot n (he ▸ hS n hn))
    · obtain ⟨m, hm⟩ := mem_iUnion.mp hb
      by_cases hnm : n = m
      · subst m
        exact hinj n hn hm he
      · exact False.elim (Set.disjoint_left.mp (hdisj hnm) (hS n hn) (he ▸ hS m hm))

theorem ordinalLift_mem_derivedSet_of_tendsto {x : X} {S : Set X} (z : ℕ → X)
    (hz : Tendsto z atTop (𝓝 x)) (hne : ∀ n, z n ≠ x)
    (hmem : ∀ᶠ n in atTop, z n ∈ S) : x ∈ derivedSet S := by
  rw [mem_derivedSet, accPt_iff_nhds]
  intro U hU
  obtain ⟨n, hnU, hnS⟩ := ((hz.eventually hU).and hmem).exists
  exact ⟨z n, ⟨hnU, hnS⟩, hne n⟩

end Posets
