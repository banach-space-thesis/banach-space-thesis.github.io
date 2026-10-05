import ThesisCommon.Analysis.OrdinalBakerSingleton

/-! The full finite closed-cover theorem for compact ordinal sets of
characteristic (η,1). The rank-zero case is the one-point case and is
handled separately from the positive-power classification. -/

noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

/-- One member of a finite closed cover of a compact ordinal set with
singleton last derivative has the entire homeomorphism type of the set. -/
theorem ordinal_characteristic_one_cover_homeomorph {ι : Type*} [Finite ι]
    {A : Set Ordinal.{u}} (hA : IsCompact A) {η a : Ordinal.{u}}
    (hD : ordinalDerived A η = {a}) (B : ι → Set Ordinal.{u})
    (hB : ∀ i, IsClosed (B i)) (hcover : A = ⋃ i, B i) :
    ∃ i, Nonempty (A ≃ₜ B i) := by
  obtain ⟨i, hi⟩ := exists_ordinalDerived_eq_singleton_of_finite_cover B hB hcover η hD
  refine ⟨i, ?_⟩
  by_cases hη : η = 0
  · subst η
    simp only [ordinalDerived_zero] at hD hi
    exact ⟨Homeomorph.setCongr (hD.trans hi.symm)⟩
  · have hBi : IsCompact (B i) := hA.of_isClosed_subset (hB i) (by
      rw [hcover]
      exact subset_iUnion B i)
    obtain ⟨eA⟩ := ordinal_compact_singleton_derivative_homeomorph hA hη hD
    obtain ⟨eB⟩ := ordinal_compact_singleton_derivative_homeomorph hBi hη hi
    exact ⟨eA.symm.trans eB⟩

/-- An actual continuous injective self-map whose image lies in one member
of the finite closed cover. Compactness makes its image a closed copy. -/
theorem ordinal_characteristic_one_closed_cover {ι : Type*} [Finite ι]
    {A : Set Ordinal.{u}} (hA : IsCompact A) {η a : Ordinal.{u}}
    (hD : ordinalDerived A η = {a}) (B : ι → Set Ordinal.{u})
    (hB : ∀ i, IsClosed (B i)) (hcover : A = ⋃ i, B i) :
    ∃ i, ∃ f : C(A, A), Function.Injective f ∧ ∀ x, (f x).val ∈ B i := by
  obtain ⟨i, ⟨e⟩⟩ := ordinal_characteristic_one_cover_homeomorph hA hD B hB hcover
  have hsub : B i ⊆ A := by rw [hcover]; exact subset_iUnion B i
  let f : C(A, A) := ⟨fun x => ⟨(e x).val, hsub (e x).property⟩,
    (continuous_subtype_val.comp e.continuous).subtype_mk _⟩
  refine ⟨i, f, ?_, fun x => (e x).property⟩
  intro x y hxy
  apply e.injective
  exact Subtype.ext (congrArg (fun z : A => z.val) hxy)

end ThesisCommon
