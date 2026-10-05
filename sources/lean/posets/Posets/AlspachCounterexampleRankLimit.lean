import Posets.AlspachCounterexampleRankShift

/-! The one-point sum of compact pointed spaces with cofinal increasing
last ranks has precisely its point at infinity at the limit rank. -/

noncomputable section
open Set Filter Topology Order ThesisCommon
open scoped OnePoint
universe u v w
namespace Posets
variable {I : Type v} (X : I → Type w) [∀ i, TopologicalSpace (X i)]
  [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] (p : ∀ i, X i)

def alspachOnePointAttach (i : I) (x : X i) :
    OnePoint (Σ i, {x : X i // x ≠ p i}) :=
  OnePoint.map (Sigma.mk i) ((alspachPunctureHomeomorph (p i)).symm x)

@[simp] theorem alspachOnePointAttach_root (i : I) :
    alspachOnePointAttach X p i (p i) = ∞ := by
  simp [alspachOnePointAttach]

theorem alspachOnePointAttach_isClosedEmbedding (i : I) :
    IsClosedEmbedding (alspachOnePointAttach X p i) := by
  have hc : Continuous (OnePoint.map (@Sigma.mk I (fun i => {x : X i // x ≠ p i}) i)) :=
    OnePoint.continuous_map continuous_sigmaMk (by
      rw [Filter.coclosedCompact_eq_cocompact, Filter.coclosedCompact_eq_cocompact]
      exact IsClosedEmbedding.sigmaMk.tendsto_cocompact)
  apply (hc.comp (alspachPunctureHomeomorph (p i)).symm.continuous).isClosedEmbedding
  intro x y h
  apply (alspachPunctureHomeomorph (p i)).symm.injective
  generalize hx : (alspachPunctureHomeomorph (p i)).symm x = a at h ⊢
  generalize hy : (alspachPunctureHomeomorph (p i)).symm y = b at h ⊢
  cases a <;> cases b <;> simp_all

theorem alspachOnePoint_ordinalDerived_limit
    (β : I → Ordinal.{u}) (η : Ordinal.{u}) (hη : IsSuccLimit η)
    (hlt : ∀ i, β i < η) (hcof : ∀ γ < η, ∃ i, γ ≤ β i)
    (hβ : ∀ i, ordinalDerived (univ : Set (X i)) (β i) = {p i}) :
    ordinalDerived (univ : Set (OnePoint (Σ i, {x : X i // x ≠ p i}))) η = {∞} := by
  apply Subset.antisymm
  · intro z hz
    cases z with
    | infty => exact mem_singleton _
    | coe z =>
        rcases z with ⟨i, x⟩
        have hzβ := ordinalDerived_antitone isClosed_univ (hlt i).le hz
        have hopen := (OnePoint.isOpenEmbedding_coe
          (X := Σ j, {x : X j // x ≠ p j})).comp (IsOpenEmbedding.sigmaMk (i := i))
        have hx := (alspach_ordinalDerived_openEmbedding_mem hopen (β i) x).mp hzβ
        have hsub : IsOpenEmbedding (Subtype.val : {x : X i // x ≠ p i} → X i) :=
          (isOpen_compl_singleton : IsOpen ({p i}ᶜ : Set (X i))).isOpenEmbedding_subtypeVal
        have hx' := (alspach_ordinalDerived_openEmbedding_mem hsub (β i) x).mpr hx
        rw [hβ i, mem_singleton_iff] at hx'
        exact (x.property hx').elim
  · rintro z rfl
    rw [ordinalDerived_limit _ hη]
    apply mem_iInter₂.mpr
    intro γ hγ
    obtain ⟨i, hi⟩ := hcof γ hγ
    apply ordinalDerived_antitone isClosed_univ hi
    have he := ordinalDerived_image_closedEmbedding
      (alspachOnePointAttach_isClosedEmbedding X p i) univ (β i)
    have hm : alspachOnePointAttach X p i (p i) ∈
        ordinalDerived (alspachOnePointAttach X p i '' univ) (β i) := by
      rw [he, hβ i]
      exact mem_image_of_mem _ (mem_singleton _)
    simpa only [alspachOnePointAttach_root] using
      ordinalDerived_mono (subset_univ _) (β i) hm

end Posets
