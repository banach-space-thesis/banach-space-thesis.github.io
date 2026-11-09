import BanachIsometric.SignedSimplexCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The boundary of the oriented coordinate simplex has zero ambient Haar
measure. It lies in the finite union of its coordinate and sum hyperplanes. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open MeasureTheory Set

theorem measure_linear_level_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (l : E →ₗ[ℝ] ℝ) (hl : l ≠ 0) (c : ℝ) :
    μ {x | l x = c} = 0 := by
  by_cases h : ∃ x, l x = c
  · obtain ⟨u, hu⟩ := h
    have hk : LinearMap.ker l ≠ ⊤ := fun he => hl (LinearMap.ker_eq_top.mp he)
    have he : {x | l x = c} = (fun x => u + x) '' (LinearMap.ker l : Set E) := by
      ext x
      constructor
      · intro hx
        change l x = c at hx
        refine ⟨x - u, ?_, by abel⟩
        change l (x - u) = 0
        rw [map_sub, hx, hu, sub_self]
      · rintro ⟨y, hy, rfl⟩
        change l y = 0 at hy
        change l (u + y) = c
        rw [map_add, hu, hy, add_zero]
    rw [he, image_add_left, measure_preimage_add]
    exact Measure.addHaar_submodule μ _ hk
  · have he : {x | l x = c} = (∅ : Set E) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      exact fun x hx => h ⟨x, hx⟩
    rw [he, measure_empty]

def signedSimplexCoordinateSum (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i : Fin n, LinearMap.proj (R := ℝ) i

@[simp] theorem signedSimplexCoordinateSum_apply (n : ℕ) (x : Fin n → ℝ) :
    signedSimplexCoordinateSum n x = ∑ i, x i := by
  simp [signedSimplexCoordinateSum, LinearMap.sum_apply]

theorem measure_signedSimplexDomain_diff_interior (n : ℕ) [NeZero n]
    (μ : Measure (Fin n → ℝ)) [μ.IsAddHaarMeasure] :
    μ (signedSimplexDomain n \ interior (signedSimplexDomain n)) = 0 := by
  let Z : Set (Fin n → ℝ) := ⋃ i, {x | x i = 0}
  let T : Set (Fin n → ℝ) := {x | ∑ i, x i = 1}
  have hZ : μ Z = 0 := by
    apply measure_iUnion_null
    intro i
    let l : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) i
    have hl : l ≠ 0 := by
      intro he
      have h := LinearMap.congr_fun he (Pi.single i (1 : ℝ))
      simp [l] at h
    exact measure_linear_level_eq_zero μ l hl 0
  have hT : μ T = 0 := by
    have hl : signedSimplexCoordinateSum n ≠ 0 := by
      intro he
      have h := LinearMap.congr_fun he (Pi.single (0 : Fin n) (1 : ℝ))
      simp [Pi.single_apply] at h
    simpa only [signedSimplexCoordinateSum_apply] using
      measure_linear_level_eq_zero μ (signedSimplexCoordinateSum n) hl 1
  refine measure_mono_null ?_ (measure_union_null hZ hT)
  rintro x ⟨hx, hxi⟩
  by_cases hZx : ∃ i, x i = 0
  · obtain ⟨i, hi⟩ := hZx
    exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)
  by_cases hTx : ∑ i, x i = 1
  · exact Or.inr hTx
  exact (hxi (mem_interior_signedSimplexDomain_of_pos n
    (fun i => lt_of_le_of_ne (hx.1 i) (fun he => hZx ⟨i, he.symm⟩))
    (lt_of_le_of_ne hx.2 hTx))).elim

end BanachIsometric.SingularPrism
