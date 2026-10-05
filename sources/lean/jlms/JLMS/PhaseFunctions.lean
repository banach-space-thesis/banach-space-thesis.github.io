import JLMS.NeighborhoodProjection

/-!
# Section 6: scalar phases and functions on finite neighborhood families

The paper uses unimodular coefficients to make each atomic contribution positive.
The constructions here work over both scalar fields and include zero coefficients.
The resulting function is in C₀(K), has norm at most one, reproduces the selected
phases at the finite points, and is supported inside the neighborhood union.
-/

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]

def scalarPhase (a : 𝕜) : 𝕜 := if a = 0 then 1 else (‖a‖ : 𝕜) / a

theorem norm_scalarPhase (a : 𝕜) : ‖scalarPhase a‖ = 1 := by
  by_cases ha : a = 0
  · simp [scalarPhase, ha]
  · rw [scalarPhase, if_neg ha, norm_div, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg a), div_self (norm_ne_zero_iff.mpr ha)]

theorem scalarPhase_mul (a : 𝕜) : scalarPhase a * a = (‖a‖ : 𝕜) := by
  by_cases ha : a = 0
  · simp [scalarPhase, ha]
  · rw [scalarPhase, if_neg ha, div_mul_cancel₀ _ ha]

variable {K : Type*} [TopologicalSpace K]
variable {ι : Type*} [Fintype ι] {p : ι → K}

def neighborhoodPhaseFunction (U : NeighborhoodFamily p) (a : ι → 𝕜) : CZero 𝕜 K :=
  ∑ i, scalarPhase (a i) • clopenIndicator (𝕜 := 𝕜) (U.sets i) (U.clopen i) (U.compact i)

theorem neighborhoodPhaseFunction_apply (U : NeighborhoodFamily p) (a : ι → 𝕜) (x : K) :
    neighborhoodPhaseFunction U a x = ∑ i, scalarPhase (a i) *
      clopenIndicator (𝕜 := 𝕜) (U.sets i) (U.clopen i) (U.compact i) x := by
  change evaluation (𝕜 := 𝕜) x
    (∑ i, scalarPhase (a i) • clopenIndicator (𝕜 := 𝕜)
      (U.sets i) (U.clopen i) (U.compact i)) = _
  simp only [map_sum, map_smul, evaluation_apply, smul_eq_mul]

theorem neighborhoodPhaseFunction_at_point (U : NeighborhoodFamily p) (a : ι → 𝕜) (j : ι) :
    neighborhoodPhaseFunction U a (p j) = scalarPhase (a j) := by
  rw [neighborhoodPhaseFunction_apply]
  simp_rw [indicator_at_point]
  simp

theorem neighborhoodPhaseFunction_support_subset (U : NeighborhoodFamily p) (a : ι → 𝕜) :
    Function.support (neighborhoodPhaseFunction U a) ⊆ ⋃ i, U.sets i := by
  intro x hx
  by_contra hnot
  have hzero : ∀ i, x ∉ U.sets i := by simpa only [Set.mem_iUnion, not_exists] using hnot
  exact hx (by simp [neighborhoodPhaseFunction_apply, hzero])

theorem neighborhoodPhaseFunction_norm_le (U : NeighborhoodFamily p) (a : ι → 𝕜) :
    ‖neighborhoodPhaseFunction U a‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro x
  change ‖neighborhoodPhaseFunction U a x‖ ≤ 1
  rw [neighborhoodPhaseFunction_apply]
  by_cases hx : ∃ i, x ∈ U.sets i
  · obtain ⟨i, hi⟩ := hx
    rw [Finset.sum_eq_single i]
    · simp [hi, norm_scalarPhase]
    · intro j _ hji
      have hj : x ∉ U.sets j := fun hj => Set.disjoint_left.mp (U.disjoint hji) hj hi
      simp [hj]
    · simp
  · push_neg at hx
    simp [hx]

/-- Disjoint neighborhood unions give disjoint functions, including the case
where each function uses a different finite index type. -/
theorem neighborhoodPhaseFunction_disjoint
    {κ : Type*} [Fintype κ] {q : κ → K}
    (U : NeighborhoodFamily p) (V : NeighborhoodFamily q) (a : ι → 𝕜) (b : κ → 𝕜)
    (hUV : Disjoint (⋃ i, U.sets i) (⋃ j, V.sets j)) :
    Disjoint (Function.support (neighborhoodPhaseFunction U a))
      (Function.support (neighborhoodPhaseFunction V b)) :=
  hUV.mono (neighborhoodPhaseFunction_support_subset U a)
    (neighborhoodPhaseFunction_support_subset V b)

end JLMS
