import Posets.ProductQuotientRealizationData
import Posets.CombinedCountableSpaces

/-! Every admissible algebra supplies checked, nonempty component data. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon TopologicalSpace
namespace Posets

variable {𝕜 C : Type} [RCLike 𝕜] [NormedRing C] [NormedAlgebra 𝕜 C]

def zeroQuotientComponent [Subsingleton C] : ProductQuotientComponent 𝕜 C where
  Points := Fin 1
  pointOrder := inferInstance
  pointCountable := inferInstance
  Coordinates := Fin 1
  coordinateCountable := inferInstance
  coordinateNonempty := inferInstance
  origin := fun _ => none
  realizes := by
    intro 𝒜 _ ι h
    change HasContractiveSplit 𝕜 (DependentCZeroSum 𝕜 (fun _ : Fin 1 => Space 𝕜 ∅)) C
    letI := space_empty_separable (𝕜 := 𝕜)
    let e := finiteCZeroSumEquiv (𝕜 := 𝕜) (fun _ : Fin 1 => Space 𝕜 ∅)
    letI : SeparableSpace (DependentCZeroSum 𝕜 (fun _ : Fin 1 => Space 𝕜 ∅)) :=
      e.symm.surjective.denseRange.separableSpace e.symm.continuous
    refine ⟨productZeroQuotient, productZeroSection, productZero_strongSplit,
      productZeroSection_isometry, ?_⟩
    rw [productZeroQuotient_norm]
    exact zero_le_one

theorem subsingleton_of_representedBy {E : Type}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Subsingleton E]
    {S : Set (E →L[𝕜] E)} (h : RepresentedBy 𝕜 C E S) : Subsingleton C := by
  obtain ⟨f, hf, _⟩ := h
  exact ⟨fun a b => hf.injective (Subsingleton.elim (f a) (f b))⟩

theorem admissibleAlgebra_has_quotientComponent (h : AdmissibleAlgebra 𝕜 C) :
    Nonempty (ProductQuotientComponent 𝕜 C) := by
  rcases h with hzero | ⟨n, hn⟩ | ⟨P, hfin, horder, hP⟩ | ⟨P, hcount, horder, hP⟩ | hfull
  · letI := hzero
    exact ⟨zeroQuotientComponent⟩
  · exact ⟨finiteFullQuotientComponent n hn⟩
  · letI := hfin
    letI := horder
    cases isEmpty_or_nonempty P with
    | inl he =>
      letI := he
      letI := subsingleton_of_representedBy hP
      exact ⟨zeroQuotientComponent⟩
    | inr hn =>
      letI := hn
      exact ⟨finiteIncidenceQuotientComponent P hP⟩
  · letI := hcount
    letI := horder
    cases isEmpty_or_nonempty P with
    | inl he =>
      letI := he
      haveI : Subsingleton (CZeroOn 𝕜 P) := ⟨fun f g => by ext p; exact isEmptyElim p.val⟩
      letI := subsingleton_of_representedBy hP
      exact ⟨zeroQuotientComponent⟩
    | inr hn =>
      letI := hn
      exact ⟨countableIncidenceQuotientComponent P hP⟩
  · exact ⟨infiniteFullQuotientComponent hfull⟩

def quotientComponentOfAdmissible (h : AdmissibleAlgebra 𝕜 C) :
    ProductQuotientComponent 𝕜 C := Classical.choice (admissibleAlgebra_has_quotientComponent h)

end Posets
