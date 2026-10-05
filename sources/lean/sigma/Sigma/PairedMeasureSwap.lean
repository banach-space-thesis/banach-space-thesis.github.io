import Sigma.MeasureSeparation

/-! Interchanging the two countable bases in the separation arguments. -/
noncomputable section
open Set ThesisCommon
namespace SigmaNonprimarity

def swapMeasure (μ : PairedMeasure) : PairedMeasure :=
  μ.comapEmbedding (Equiv.sumComm ℕ ℕ).toEmbedding

@[simp] theorem swapMeasure_left (μ : PairedMeasure) (A : Set ℕ) :
    swapMeasure μ (Sum.inl '' A) = μ (Sum.inr '' A) := by
  change μ ((Equiv.sumComm ℕ ℕ) '' (Sum.inl '' A)) = _
  rw [Set.image_image]
  rfl

@[simp] theorem swapMeasure_right (μ : PairedMeasure) (A : Set ℕ) :
    swapMeasure μ (Sum.inr '' A) = μ (Sum.inl '' A) := by
  change μ ((Equiv.sumComm ℕ ℕ) '' (Sum.inr '' A)) = _
  rw [Set.image_image]
  rfl

@[simp] theorem swapMeasure_swap (μ : PairedMeasure) : swapMeasure (swapMeasure μ) = μ := by
  have hfun : (swapMeasure (swapMeasure μ)).toFun = μ.toFun := by
    funext A
    change μ ((Equiv.sumComm ℕ ℕ) '' ((Equiv.sumComm ℕ ℕ) '' A)) = μ A
    rw [Set.image_image]
    have heq : (fun x : ℕ ⊕ ℕ => (Equiv.sumComm ℕ ℕ) ((Equiv.sumComm ℕ ℕ) x)) = id := by
      funext x
      cases x <;> rfl
    rw [heq, Set.image_id]
  exact UnitCharge.ext hfun

theorem pairedSeparated_swap (B Btilde : BooleanSubalgebra (Set ℕ))
    (M N : Set PairedMeasure) (h : PairedSeparated B Btilde M N) :
    PairedSeparated Btilde B (swapMeasure '' M) (swapMeasure '' N) := by
  classical
  obtain ⟨ε, hε, F, _, hsep⟩ := h
  refine ⟨ε, hε, F.image Sum.swap, Set.subset_univ _, ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩ _ ⟨ν, hν, rfl⟩
  obtain ⟨t, ht, hgap⟩ := hsep μ hμ ν hν
  refine ⟨Sum.swap t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
  cases t <;> simpa [pairedTest] using hgap

theorem pairedSeparated_swap_iff (B Btilde : BooleanSubalgebra (Set ℕ))
    (M N : Set PairedMeasure) :
    PairedSeparated Btilde B (swapMeasure '' M) (swapMeasure '' N) ↔
      PairedSeparated B Btilde M N := by
  constructor
  · intro h
    have hh := pairedSeparated_swap Btilde B (swapMeasure '' M) (swapMeasure '' N) h
    simpa [Set.image_image] using hh
  · exact pairedSeparated_swap B Btilde M N

end SigmaNonprimarity
