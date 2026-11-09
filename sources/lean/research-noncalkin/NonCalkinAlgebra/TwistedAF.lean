import NonCalkinAlgebra.TwistedLocalSubalgebra
import NonCalkinAlgebra.TwistedSpanDensity

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TwistedRegular
universe u
variable {G : Type u} [AddCommGroup G] [Module (ZMod 2) G]

theorem innerSpan_mem_local (c : Cocycle G) {a : closedSubalgebra c}
    (ha : a ∈ innerSpan c) :
    ∃ P : Submodule (ZMod 2) G, FiniteDimensional (ZMod 2) P ∧ a ∈ localSpan c P := by
  change a ∈ Submodule.span ℂ _ at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨g, rfl⟩ := ha
    refine ⟨Submodule.span (ZMod 2) {g}, inferInstance, ?_⟩
    exact localShift_mem c _ g (Submodule.subset_span (Set.mem_singleton g))
  | zero => exact ⟨⊥, inferInstance, (localSpan c ⊥).zero_mem⟩
  | add a b ha hb iha ihb =>
    obtain ⟨P, hP, haP⟩ := iha
    obtain ⟨Q, hQ, hbQ⟩ := ihb
    letI := hP
    letI := hQ
    exact ⟨P ⊔ Q, inferInstance, (localSpan c (P ⊔ Q)).add_mem
      (localSpan_mono c le_sup_left haP) (localSpan_mono c le_sup_right hbQ)⟩
  | smul r a ha ih =>
    obtain ⟨P, hP, haP⟩ := ih
    exact ⟨P, hP, (localSpan c P).smul_mem r haP⟩

/-- The concrete twisted algebra of an arbitrary binary vector space is AF:
the actual finite-dimensional local *-subalgebras form a directed dense union. -/
theorem isApproximatelyFiniteDimensional (c : Cocycle G) :
    IsApproximatelyFiniteDimensional (closedSubalgebra c) := by
  let S : Set (StarSubalgebra ℂ (closedSubalgebra c)) :=
    {B | ∃ P : Submodule (ZMod 2) G, FiniteDimensional (ZMod 2) P ∧ B = localStarSubalgebra c P}
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · exact ⟨localStarSubalgebra c ⊥, ⊥, inferInstance, rfl⟩
  · intro A hA B hB
    obtain ⟨P, hP, rfl⟩ := hA
    obtain ⟨Q, hQ, rfl⟩ := hB
    letI := hP
    letI := hQ
    exact ⟨localStarSubalgebra c (P ⊔ Q), ⟨P ⊔ Q, inferInstance, rfl⟩,
      localStarSubalgebra_mono c le_sup_left, localStarSubalgebra_mono c le_sup_right⟩
  · intro B hB
    obtain ⟨P, hP, rfl⟩ := hB
    letI := hP
    exact localStarSubalgebra_finiteDimensional c P
  · apply (dense_innerSpan c).mono
    intro a ha
    obtain ⟨P, hP, haP⟩ := innerSpan_mem_local c ha
    exact Set.mem_iUnion.mpr ⟨localStarSubalgebra c P,
      Set.mem_iUnion.mpr ⟨⟨P, hP, rfl⟩, haP⟩⟩

end NonCalkinAlgebra.TwistedRegular
