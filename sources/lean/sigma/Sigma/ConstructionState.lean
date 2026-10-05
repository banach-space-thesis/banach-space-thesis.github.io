import Sigma.StageAlgebra
import Sigma.TwoSidedSuccessor

/-! The four nonseparation invariants for genuine choices of splitting sets. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

abbrev AtomicRows := ℕ → lp (fun _ : Point => ℝ) 1

def ThreeLevelChoice.generator {μ : AtomicRows} {C : Set ℕ}
    (d : ThreeLevelChoice μ C) : Bool → Set ℕ
  | false => codedSet d.Z
  | true => codedSet (cylinder d.J₁ \ d.Z)

def ThreeLevelChoice.cutLeft {μ : AtomicRows} {C : Set ℕ}
    (d : ThreeLevelChoice μ C) : Bool → Set ℕ
  | false => d.J₂
  | true => d.J₁

def ThreeLevelChoice.cutRight {μ : AtomicRows} {C : Set ℕ}
    (d : ThreeLevelChoice μ C) : Bool → Set ℕ
  | false => d.J₁ \ d.J₂
  | true => d.J₀ \ d.J₁

theorem ThreeLevelChoice.nonseparated_iff_cuts {μ : AtomicRows} {C : Set ℕ}
    (d : ThreeLevelChoice μ C) (ρ : ℕ → PairedMeasure) (B Btilde : BooleanSubalgebra (Set ℕ)) :
    d.Nonseparated ρ B Btilde ↔ ∀ b : Bool,
      ¬ PairedSeparated B Btilde (ρ '' d.cutLeft b) (ρ '' d.cutRight b) := by
  constructor
  · rintro ⟨h₀,h₁⟩ b
    cases b
    · exact h₀
    · exact h₁
  · intro h
    exact ⟨h false,h true⟩

abbrev ConstructionData {I : Type} (μ μtilde : I → AtomicRows) (R Rtilde : I → Set ℕ) :=
  ∀ i, ThreeLevelChoice (μ i) (R i) × ThreeLevelChoice (μtilde i) (Rtilde i)

def constructionAlgebra {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (d : ConstructionData μ μtilde R Rtilde) (side : Bool) (V : Set I) : BooleanSubalgebra (Set ℕ) :=
  stageAlgebra (fun i => if side then (d i).2.generator else (d i).1.generator) V

def GoodConstruction {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (ρ σ : I → ℕ → PairedMeasure) (d : ConstructionData μ μtilde R Rtilde) (V : Set I) : Prop :=
  ∀ i ∈ V,
    (d i).1.Nonseparated (ρ i) (constructionAlgebra d false (V \ {i})) (constructionAlgebra d true V) ∧
    (d i).2.Nonseparated (σ i) (constructionAlgebra d false V) (constructionAlgebra d true (V \ {i}))

theorem constructionAlgebra_congr {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (d e : ConstructionData μ μtilde R Rtilde) (side : Bool) (V : Set I)
    (h : ∀ i ∈ V, d i = e i) : constructionAlgebra d side V = constructionAlgebra e side V := by
  apply stageAlgebra_congr
  intro i hi
  rw [h i hi]

theorem goodConstruction_congr {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (ρ σ : I → ℕ → PairedMeasure) (d e : ConstructionData μ μtilde R Rtilde) (V : Set I)
    (h : ∀ i ∈ V, d i = e i) : GoodConstruction ρ σ d V ↔ GoodConstruction ρ σ e V := by
  have halg (side : Bool) : constructionAlgebra d side V = constructionAlgebra e side V :=
    constructionAlgebra_congr d e side V h
  have hrem (side : Bool) (i : I) :
      constructionAlgebra d side (V \ {i}) = constructionAlgebra e side (V \ {i}) :=
    constructionAlgebra_congr d e side (V \ {i}) (fun j hj => h j hj.1)
  unfold GoodConstruction
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [h i hi, halg, halg, hrem, hrem]

theorem constructionAlgebra_mono {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (d : ConstructionData μ μtilde R Rtilde) (side : Bool) {V W : Set I} (h : V ⊆ W) :
    constructionAlgebra d side V ≤ constructionAlgebra d side W := stageAlgebra_mono _ h

theorem constructionAlgebra_cardinal_le {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (d : ConstructionData μ μtilde R Rtilde) (side : Bool) (V : Set I)
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hV : #V ≤ κ) : #(constructionAlgebra d side V) ≤ κ :=
  stageAlgebra_cardinal_le _ V κ hκ hV

theorem constructionAlgebra_finite_mem {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (d : ConstructionData μ μtilde R Rtilde) (side : Bool) (V : Set I)
    {A : Set ℕ} (hA : A.Finite) : A ∈ constructionAlgebra d side V := stageAlgebra_finite_mem _ V hA

theorem constructionAlgebra_insert_left {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (d : ConstructionData μ μtilde R Rtilde) (V : Set I) (i : I) :
    constructionAlgebra d false (insert i V) = (d i).1.adjoin (constructionAlgebra d false V) := by
  unfold constructionAlgebra
  rw [stageAlgebra_insert]
  rfl

theorem constructionAlgebra_insert_right {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (d : ConstructionData μ μtilde R Rtilde) (V : Set I) (i : I) :
    constructionAlgebra d true (insert i V) = (d i).2.adjoin (constructionAlgebra d true V) := by
  unfold constructionAlgebra
  rw [stageAlgebra_insert]
  rfl

theorem goodConstruction_empty {I : Type} {μ μtilde : I → AtomicRows} {R Rtilde : I → Set ℕ}
    (ρ σ : I → ℕ → PairedMeasure) (d : ConstructionData μ μtilde R Rtilde) :
    GoodConstruction ρ σ d ∅ := by
  intro i hi
  exact False.elim hi

end SigmaNonprimarity
