import ThesisCommon.Analysis.FiniteAbsoluteConvexOrbit

/-! Finite absolutely convex orbits indexed by an actual finite parameter set.
The formulation makes enlargement of both the parameter set and coefficient
budget explicit, and is equivalent to the finite-type orbit used by separation. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 X ι : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def finiteParameterOrbit (v : ι → X) (s : Finset ι) (m : ℝ) : Set X :=
  {x | ∃ c : ι → 𝕜, (∑ i ∈ s, ‖c i‖) ≤ m ∧ (∑ i ∈ s, c i • v i) = x}

theorem finiteParameterOrbit_eq (v : ι → X) (s : Finset ι) (m : ℝ) :
    finiteParameterOrbit (𝕜 := 𝕜) v s m =
      finiteAbsoluteConvexOrbit (𝕜 := 𝕜) (fun i : s => v i) m := by
  classical
  ext x
  constructor
  · rintro ⟨c,hc,he⟩
    refine ⟨fun i => c i,?_,?_⟩
    · simpa only [← Finset.sum_attach s] using hc
    · simpa only [← Finset.sum_attach s] using he
  · rintro ⟨c,hc,he⟩
    let d (i : ι) : 𝕜 := if h : i ∈ s then c ⟨i,h⟩ else 0
    refine ⟨d,?_,?_⟩
    · rw [← Finset.sum_attach s]
      simpa [d] using hc
    · rw [← Finset.sum_attach s]
      simpa [d] using he

theorem finiteParameterOrbit_mono (v : ι → X) {s t : Finset ι}
    (hst : s ⊆ t) {m n : ℝ} (hmn : m ≤ n) :
    finiteParameterOrbit (𝕜 := 𝕜) v s m ⊆ finiteParameterOrbit (𝕜 := 𝕜) v t n := by
  classical
  rintro x ⟨c,hc,he⟩
  let d (i : ι) := if i ∈ s then c i else 0
  have hd (i : ι) (hi : i ∈ s) : d i = c i := if_pos hi
  have hdn : (∑ i ∈ t, ‖d i‖) = ∑ i ∈ s, ‖c i‖ := by
    rw [← Finset.sum_subset hst (fun i _ hi => by simp [d, hi])]
    exact Finset.sum_congr rfl (fun i hi => by rw [hd i hi])
  have hds : (∑ i ∈ t, d i • v i) = ∑ i ∈ s, c i • v i := by
    rw [← Finset.sum_subset hst (fun i _ hi => by simp [d, hi])]
    exact Finset.sum_congr rfl (fun i hi => by rw [hd i hi])
  exact ⟨d,hdn.trans_le (hc.trans hmn),hds.trans he⟩

theorem zero_mem_finiteParameterOrbit (v : ι → X) (s : Finset ι)
    {m : ℝ} (hm : 0 ≤ m) : (0 : X) ∈ finiteParameterOrbit (𝕜 := 𝕜) v s m := by
  refine ⟨fun _ => 0,?_,?_⟩
  · simpa using hm
  · simp

end ThesisCommon
