import Sigma.ComplexConstructionLimit
import Sigma.ComplexConstructionSuccessor
import ThesisCommon.Analysis.SigmaComplexChargeSeries

/-! Store each stage's charge sequences along with its chosen splitting sets.
Future stages may compute new charges from this history; old charges remain fixed. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

abbrev ComplexChargeSequences := (ℕ → ComplexPairedMeasure) × (ℕ → ComplexPairedMeasure)

structure ComplexCodedStage (μ μtilde : ComplexAtomicRows) (R Rtilde : Set ℕ) where
  choices : ComplexThreeLevelChoice μ R × ComplexThreeLevelChoice μtilde Rtilde
  measures : ComplexChargeSequences

abbrev ComplexCodedConstruction {I : Type} (μ μtilde : I → ComplexAtomicRows) (R Rtilde : I → Set ℕ) :=
  ∀ i, ComplexCodedStage (μ i) (μtilde i) (R i) (Rtilde i)

def ComplexCodedConstruction.choices {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (d : ComplexCodedConstruction μ μtilde R Rtilde) : ComplexConstructionData μ μtilde R Rtilde :=
  fun i => (d i).choices

def ComplexCodedConstruction.Good {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (d : ComplexCodedConstruction μ μtilde R Rtilde) (V : Set I) : Prop :=
  GoodComplexConstruction (fun i => (d i).measures.1) (fun i => (d i).measures.2) d.choices V

theorem goodComplexConstruction_congr_measures {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (ρ σ ρ' σ' : I → ℕ → ComplexPairedMeasure) (d : ComplexConstructionData μ μtilde R Rtilde) (V : Set I)
    (hρ : ∀ i ∈ V, ρ i = ρ' i) (hσ : ∀ i ∈ V, σ i = σ' i) :
    GoodComplexConstruction ρ σ d V ↔ GoodComplexConstruction ρ' σ' d V := by
  unfold GoodComplexConstruction
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [hρ i hi, hσ i hi]

theorem ComplexCodedConstruction.good_congr {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (d e : ComplexCodedConstruction μ μtilde R Rtilde) (V : Set I)
    (h : ∀ i ∈ V, d i = e i) : d.Good V ↔ e.Good V := by
  unfold ComplexCodedConstruction.Good
  rw [goodComplexConstruction_congr _ _ d.choices e.choices V (fun i hi => congrArg ComplexCodedStage.choices (h i hi))]
  exact goodComplexConstruction_congr_measures _ _ _ _ e.choices V
    (fun i hi => congrArg (fun x => x.measures.1) (h i hi))
    (fun i hi => congrArg (fun x => x.measures.2) (h i hi))

theorem ComplexCodedConstruction.good_directed_union {I K : Type}
    {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (d : ComplexCodedConstruction μ μtilde R Rtilde) (V : K → Set I) (hdir : Directed (· ⊆ ·) V)
    (hgood : ∀ k, d.Good (V k)) : d.Good (⋃ k, V k) :=
  goodComplexConstruction_directed_union _ _ d.choices V hdir hgood

theorem complex_exists_codedConstruction_insert {I : Type} [DecidableEq I]
    {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (d : ComplexCodedConstruction μ μtilde R Rtilde) (V : Set I) (a : I)
    (ha : a ∉ V) (hV : #V < 𝔠) (hgood : d.Good V)
    (hR : (R a).Infinite) (hRt : (Rtilde a).Infinite)
    (hμ : ComplexAdmissible (μ a)) (hμt : ComplexAdmissible (μtilde a)) (q : ComplexChargeSequences) :
    ∃ x : ComplexCodedStage (μ a) (μtilde a) (R a) (Rtilde a),
      x.measures = q ∧ ComplexCodedConstruction.Good (Function.update d a x) (insert a V) := by
  classical
  let ρ := Function.update (fun i => (d i).measures.1) a q.1
  let σ := Function.update (fun i => (d i).measures.2) a q.2
  have hgood' : GoodComplexConstruction ρ σ d.choices V := by
    apply (goodComplexConstruction_congr_measures _ _ ρ σ d.choices V ?_ ?_).mp hgood
    · intro i hi
      exact (Function.update_of_ne (show i ≠ a from fun h => ha (h ▸ hi)) q.1
        (fun j => (d j).measures.1)).symm
    · intro i hi
      exact (Function.update_of_ne (show i ≠ a from fun h => ha (h ▸ hi)) q.2
        (fun j => (d j).measures.2)).symm
  obtain ⟨c,hc⟩ := exists_goodComplexConstruction_insert ρ σ d.choices V a ha hV hgood' hR hRt hμ hμt
  let x : ComplexCodedStage (μ a) (μtilde a) (R a) (Rtilde a) := ⟨c,q⟩
  let e : ComplexCodedConstruction μ μtilde R Rtilde := Function.update d a x
  have hchoices : e.choices = Function.update d.choices a c := by
    funext i
    by_cases hi : i = a
    · subst i
      simp [e, ComplexCodedConstruction.choices, x]
    · simp [e, ComplexCodedConstruction.choices, Function.update_of_ne hi]
  have hρ : (fun i => (e i).measures.1) = ρ := by
    funext i
    by_cases hi : i = a
    · subst i
      simp [e, ρ, x]
    · simp [e, ρ, Function.update_of_ne hi]
  have hσ : (fun i => (e i).measures.2) = σ := by
    funext i
    by_cases hi : i = a
    · subst i
      simp [e, σ, x]
    · simp [e, σ, Function.update_of_ne hi]
  refine ⟨x,rfl,?_⟩
  change e.Good (insert a V)
  unfold ComplexCodedConstruction.Good
  rw [hchoices,hρ,hσ]
  exact hc

end SigmaNonprimarity
