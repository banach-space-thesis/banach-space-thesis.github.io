import Sigma.ConstructionLimit
import Sigma.ConstructionSuccessor
import ThesisCommon.Analysis.ChargeBasics

/-! Store each stage's charge sequences along with its chosen splitting sets.
Future stages may compute new charges from this history; old charges remain fixed. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

abbrev ChargeSequences := (ℕ → PairedMeasure) × (ℕ → PairedMeasure)

structure CodedStage (μ μtilde : AtomicRows) (R Rtilde : Set ℕ) where
  choices : ThreeLevelChoice μ R × ThreeLevelChoice μtilde Rtilde
  measures : ChargeSequences

abbrev CodedConstruction {I : Type} (μ μtilde : I → AtomicRows) (R Rtilde : I → Set ℕ) :=
  ∀ i, CodedStage (μ i) (μtilde i) (R i) (Rtilde i)

def CodedConstruction.choices {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (d : CodedConstruction μ μtilde R Rtilde) : ConstructionData μ μtilde R Rtilde :=
  fun i => (d i).choices

def CodedConstruction.Good {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (d : CodedConstruction μ μtilde R Rtilde) (V : Set I) : Prop :=
  GoodConstruction (fun i => (d i).measures.1) (fun i => (d i).measures.2) d.choices V

theorem goodConstruction_congr_measures {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (ρ σ ρ' σ' : I → ℕ → PairedMeasure) (d : ConstructionData μ μtilde R Rtilde) (V : Set I)
    (hρ : ∀ i ∈ V, ρ i = ρ' i) (hσ : ∀ i ∈ V, σ i = σ' i) :
    GoodConstruction ρ σ d V ↔ GoodConstruction ρ' σ' d V := by
  unfold GoodConstruction
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [hρ i hi, hσ i hi]

theorem CodedConstruction.good_congr {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (d e : CodedConstruction μ μtilde R Rtilde) (V : Set I)
    (h : ∀ i ∈ V, d i = e i) : d.Good V ↔ e.Good V := by
  unfold CodedConstruction.Good
  rw [goodConstruction_congr _ _ d.choices e.choices V (fun i hi => congrArg CodedStage.choices (h i hi))]
  exact goodConstruction_congr_measures _ _ _ _ e.choices V
    (fun i hi => congrArg (fun x => x.measures.1) (h i hi))
    (fun i hi => congrArg (fun x => x.measures.2) (h i hi))

theorem CodedConstruction.good_directed_union {I K : Type}
    {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (d : CodedConstruction μ μtilde R Rtilde) (V : K → Set I) (hdir : Directed (· ⊆ ·) V)
    (hgood : ∀ k, d.Good (V k)) : d.Good (⋃ k, V k) :=
  goodConstruction_directed_union _ _ d.choices V hdir hgood

theorem exists_codedConstruction_insert {I : Type} [DecidableEq I]
    {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (d : CodedConstruction μ μtilde R Rtilde) (V : Set I) (a : I)
    (ha : a ∉ V) (hV : #V < 𝔠) (hgood : d.Good V)
    (hR : (R a).Infinite) (hRt : (Rtilde a).Infinite)
    (hμ : Admissible (μ a)) (hμt : Admissible (μtilde a)) (q : ChargeSequences) :
    ∃ x : CodedStage (μ a) (μtilde a) (R a) (Rtilde a),
      x.measures = q ∧ CodedConstruction.Good (Function.update d a x) (insert a V) := by
  classical
  let ρ := Function.update (fun i => (d i).measures.1) a q.1
  let σ := Function.update (fun i => (d i).measures.2) a q.2
  have hgood' : GoodConstruction ρ σ d.choices V := by
    apply (goodConstruction_congr_measures _ _ ρ σ d.choices V ?_ ?_).mp hgood
    · intro i hi
      exact (Function.update_of_ne (show i ≠ a from fun h => ha (h ▸ hi)) q.1
        (fun j => (d j).measures.1)).symm
    · intro i hi
      exact (Function.update_of_ne (show i ≠ a from fun h => ha (h ▸ hi)) q.2
        (fun j => (d j).measures.2)).symm
  obtain ⟨c,hc⟩ := exists_goodConstruction_insert ρ σ d.choices V a ha hV hgood' hR hRt hμ hμt
  let x : CodedStage (μ a) (μtilde a) (R a) (Rtilde a) := ⟨c,q⟩
  let e : CodedConstruction μ μtilde R Rtilde := Function.update d a x
  have hchoices : e.choices = Function.update d.choices a c := by
    funext i
    by_cases hi : i = a
    · subst i
      simp [e, CodedConstruction.choices, x]
    · simp [e, CodedConstruction.choices, Function.update_of_ne hi]
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
  unfold CodedConstruction.Good
  rw [hchoices,hρ,hσ]
  exact hc

end SigmaNonprimarity
