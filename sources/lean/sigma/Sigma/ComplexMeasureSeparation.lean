import Sigma.MeasureSeparation
import Sigma.ComplexSeparation
import ThesisCommon.Analysis.SigmaComplexUnitCharge

/-! Two-base complex charges and separation, retaining joint finite variation.
The underlying Boolean tests are exactly those of the real construction. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

abbrev ComplexPairedMeasure := ComplexUnitCharge (ℕ ⊕ ℕ)

def ComplexPairedSeparated (B Btilde : BooleanSubalgebra (Set ℕ))
    (M N : Set ComplexPairedMeasure) : Prop :=
  ComplexFinitelySeparated (fun μ t => μ (pairedTest B Btilde t)) Set.univ M N

theorem complexFinitelySeparated_image_iff {D E I : Type*} (ev : E → I → ℂ)
    (f : D → E) (T : Set I) (M N : Set D) :
    ComplexFinitelySeparated ev T (f '' M) (f '' N) ↔
      ComplexFinitelySeparated (fun d i => ev (f d) i) T M N := by
  constructor
  · rintro ⟨ε,hε,F,hF,hsep⟩
    exact ⟨ε,hε,F,hF,fun m hm n hn =>
      hsep (f m) (Set.mem_image_of_mem f hm) (f n) (Set.mem_image_of_mem f hn)⟩
  · rintro ⟨ε,hε,F,hF,hsep⟩
    refine ⟨ε,hε,F,hF,?_⟩
    rintro _ ⟨m,hm,rfl⟩ _ ⟨n,hn,rfl⟩
    exact hsep m hm n hn

theorem complex_separated_measure_cuts_lt_continuum (B Btilde : BooleanSubalgebra (Set ℕ))
    (hB : #B < 𝔠) (hBtilde : #Btilde < 𝔠) (M : Set ComplexPairedMeasure) :
    #{A : Set ComplexPairedMeasure // A ⊆ M ∧ ComplexPairedSeparated B Btilde A (M \ A)} < 𝔠 := by
  apply complex_separated_cuts_lt_continuum (fun μ t => μ (pairedTest B Btilde t))
    (fun μ t => μ.norm_apply_le_one (pairedTest B Btilde t)) M
  rw [Cardinal.mk_sum]
  simpa only [Cardinal.lift_id] using
    Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum hB hBtilde

def complexLeftMeasure (μ : ComplexPairedMeasure) : ComplexUnitCharge ℕ :=
  μ.comapEmbedding ⟨Sum.inl,Sum.inl_injective⟩

@[simp] theorem complexLeftMeasure_apply (μ : ComplexPairedMeasure) (A : Set ℕ) :
    complexLeftMeasure μ A = μ (Sum.inl '' A) := rfl

def complexSwapMeasure (μ : ComplexPairedMeasure) : ComplexPairedMeasure :=
  μ.comapEmbedding (Equiv.sumComm ℕ ℕ).toEmbedding

@[simp] theorem complexSwapMeasure_left (μ : ComplexPairedMeasure) (A : Set ℕ) :
    complexSwapMeasure μ (Sum.inl '' A) = μ (Sum.inr '' A) := by
  change μ ((Equiv.sumComm ℕ ℕ) '' (Sum.inl '' A)) = _
  rw [Set.image_image]
  rfl

@[simp] theorem complexSwapMeasure_right (μ : ComplexPairedMeasure) (A : Set ℕ) :
    complexSwapMeasure μ (Sum.inr '' A) = μ (Sum.inl '' A) := by
  change μ ((Equiv.sumComm ℕ ℕ) '' (Sum.inr '' A)) = _
  rw [Set.image_image]
  rfl

@[simp] theorem complexSwapMeasure_swap (μ : ComplexPairedMeasure) :
    complexSwapMeasure (complexSwapMeasure μ) = μ := by
  apply ComplexUnitCharge.ext
  funext A
  change μ ((Equiv.sumComm ℕ ℕ) '' ((Equiv.sumComm ℕ ℕ) '' A)) = μ A
  rw [Set.image_image]
  have heq : (fun x : ℕ ⊕ ℕ => (Equiv.sumComm ℕ ℕ) ((Equiv.sumComm ℕ ℕ) x)) = id := by
    funext x
    cases x <;> rfl
  rw [heq,Set.image_id]

theorem complexPairedSeparated_swap (B Btilde : BooleanSubalgebra (Set ℕ))
    (M N : Set ComplexPairedMeasure) (h : ComplexPairedSeparated B Btilde M N) :
    ComplexPairedSeparated Btilde B (complexSwapMeasure '' M) (complexSwapMeasure '' N) := by
  classical
  obtain ⟨ε,hε,F,_,hsep⟩ := h
  refine ⟨ε,hε,F.image Sum.swap,Set.subset_univ _,?_⟩
  rintro _ ⟨μ,hμ,rfl⟩ _ ⟨ν,hν,rfl⟩
  obtain ⟨t,ht,hgap⟩ := hsep μ hμ ν hν
  refine ⟨Sum.swap t,Finset.mem_image.mpr ⟨t,ht,rfl⟩,?_⟩
  cases t <;> simpa [pairedTest] using hgap

theorem complexPairedSeparated_swap_iff (B Btilde : BooleanSubalgebra (Set ℕ))
    (M N : Set ComplexPairedMeasure) :
    ComplexPairedSeparated Btilde B (complexSwapMeasure '' M) (complexSwapMeasure '' N) ↔
      ComplexPairedSeparated B Btilde M N := by
  constructor
  · intro h
    have hh := complexPairedSeparated_swap Btilde B (complexSwapMeasure '' M) (complexSwapMeasure '' N) h
    simpa [Set.image_image] using hh
  · exact complexPairedSeparated_swap B Btilde M N

end SigmaNonprimarity
