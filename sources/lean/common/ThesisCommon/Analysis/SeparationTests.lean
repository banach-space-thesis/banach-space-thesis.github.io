import ThesisCommon.Analysis.FiniteSeparation

/-! Transfer finite separation along representatives of the admissible tests. -/
noncomputable section
namespace ThesisCommon

theorem finitelySeparated_of_test_representatives {D I J : Type*} [Nonempty J]
    (ev : D → I → ℝ) (ev' : D → J → ℝ) (S : Set I) (T : Set J) (M N : Set D)
    (hrep : ∀ i ∈ S, ∃ j ∈ T, ∀ d, ev d i = ev' d j)
    (h : FinitelySeparated ev S M N) : FinitelySeparated ev' T M N := by
  classical
  let r : I → J := fun i => if hi : i ∈ S then Classical.choose (hrep i hi) else Classical.arbitrary J
  have hr (i : I) (hi : i ∈ S) : r i ∈ T ∧ ∀ d, ev d i = ev' d (r i) := by
    simpa only [r,dif_pos hi] using Classical.choose_spec (hrep i hi)
  obtain ⟨ε,hε,F,hF,hsep⟩ := h
  refine ⟨ε,hε,F.image r,?_,?_⟩
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact (hr i (hF hi)).1
  · intro m hm n hn
    obtain ⟨i,hi,he⟩ := hsep m hm n hn
    refine ⟨r i,Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
    simpa only [(hr i (hF hi)).2 m,(hr i (hF hi)).2 n] using he

end ThesisCommon
