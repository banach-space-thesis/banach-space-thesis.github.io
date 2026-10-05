import Sigma.StageAlgebra
import Sigma.ComplexTwoSidedSuccessor

/-! The four nonseparation invariants for genuine choices of splitting sets. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

abbrev ComplexAtomicRows := ℕ → lp (fun _ : Point => ℂ) 1

def ComplexThreeLevelChoice.generator {μ : ComplexAtomicRows} {C : Set ℕ}
    (d : ComplexThreeLevelChoice μ C) : Bool → Set ℕ
  | false => codedSet d.Z
  | true => codedSet (cylinder d.J₁ \ d.Z)

def ComplexThreeLevelChoice.cutLeft {μ : ComplexAtomicRows} {C : Set ℕ}
    (d : ComplexThreeLevelChoice μ C) : Bool → Set ℕ
  | false => d.J₂
  | true => d.J₁

def ComplexThreeLevelChoice.cutRight {μ : ComplexAtomicRows} {C : Set ℕ}
    (d : ComplexThreeLevelChoice μ C) : Bool → Set ℕ
  | false => d.J₁ \ d.J₂
  | true => d.J₀ \ d.J₁

theorem ComplexThreeLevelChoice.pairedNonseparated_iff_cuts {μ : ComplexAtomicRows} {C : Set ℕ}
    (d : ComplexThreeLevelChoice μ C) (ρ : ℕ → ComplexPairedMeasure) (B Btilde : BooleanSubalgebra (Set ℕ)) :
    d.PairedNonseparated ρ B Btilde ↔ ∀ b : Bool,
      ¬ ComplexPairedSeparated B Btilde (ρ '' d.cutLeft b) (ρ '' d.cutRight b) := by
  constructor
  · rintro ⟨h₀,h₁⟩ b
    cases b
    · exact h₀
    · exact h₁
  · intro h
    exact ⟨h false,h true⟩

abbrev ComplexConstructionData {I : Type} (μ μtilde : I → ComplexAtomicRows) (R Rtilde : I → Set ℕ) :=
  ∀ i, ComplexThreeLevelChoice (μ i) (R i) × ComplexThreeLevelChoice (μtilde i) (Rtilde i)

def complexConstructionAlgebra {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (d : ComplexConstructionData μ μtilde R Rtilde) (side : Bool) (V : Set I) : BooleanSubalgebra (Set ℕ) :=
  stageAlgebra (fun i => if side then (d i).2.generator else (d i).1.generator) V

def GoodComplexConstruction {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (ρ σ : I → ℕ → ComplexPairedMeasure) (d : ComplexConstructionData μ μtilde R Rtilde) (V : Set I) : Prop :=
  ∀ i ∈ V,
    (d i).1.PairedNonseparated (ρ i) (complexConstructionAlgebra d false (V \ {i})) (complexConstructionAlgebra d true V) ∧
    (d i).2.PairedNonseparated (σ i) (complexConstructionAlgebra d false V) (complexConstructionAlgebra d true (V \ {i}))

theorem complexConstructionAlgebra_congr {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (d e : ComplexConstructionData μ μtilde R Rtilde) (side : Bool) (V : Set I)
    (h : ∀ i ∈ V, d i = e i) : complexConstructionAlgebra d side V = complexConstructionAlgebra e side V := by
  apply stageAlgebra_congr
  intro i hi
  rw [h i hi]

theorem goodComplexConstruction_congr {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (ρ σ : I → ℕ → ComplexPairedMeasure) (d e : ComplexConstructionData μ μtilde R Rtilde) (V : Set I)
    (h : ∀ i ∈ V, d i = e i) : GoodComplexConstruction ρ σ d V ↔ GoodComplexConstruction ρ σ e V := by
  have halg (side : Bool) : complexConstructionAlgebra d side V = complexConstructionAlgebra e side V :=
    complexConstructionAlgebra_congr d e side V h
  have hrem (side : Bool) (i : I) :
      complexConstructionAlgebra d side (V \ {i}) = complexConstructionAlgebra e side (V \ {i}) :=
    complexConstructionAlgebra_congr d e side (V \ {i}) (fun j hj => h j hj.1)
  unfold GoodComplexConstruction
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [h i hi, halg, halg, hrem, hrem]

theorem complexConstructionAlgebra_mono {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (d : ComplexConstructionData μ μtilde R Rtilde) (side : Bool) {V W : Set I} (h : V ⊆ W) :
    complexConstructionAlgebra d side V ≤ complexConstructionAlgebra d side W := stageAlgebra_mono _ h

theorem complexConstructionAlgebra_cardinal_le {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (d : ComplexConstructionData μ μtilde R Rtilde) (side : Bool) (V : Set I)
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hV : #V ≤ κ) : #(complexConstructionAlgebra d side V) ≤ κ :=
  stageAlgebra_cardinal_le _ V κ hκ hV

theorem complexConstructionAlgebra_finite_mem {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (d : ComplexConstructionData μ μtilde R Rtilde) (side : Bool) (V : Set I)
    {A : Set ℕ} (hA : A.Finite) : A ∈ complexConstructionAlgebra d side V := stageAlgebra_finite_mem _ V hA

theorem complexConstructionAlgebra_insert_left {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (d : ComplexConstructionData μ μtilde R Rtilde) (V : Set I) (i : I) :
    complexConstructionAlgebra d false (insert i V) = (d i).1.adjoin (complexConstructionAlgebra d false V) := by
  unfold complexConstructionAlgebra
  rw [stageAlgebra_insert]
  rfl

theorem complexConstructionAlgebra_insert_right {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (d : ComplexConstructionData μ μtilde R Rtilde) (V : Set I) (i : I) :
    complexConstructionAlgebra d true (insert i V) = (d i).2.adjoin (complexConstructionAlgebra d true V) := by
  unfold complexConstructionAlgebra
  rw [stageAlgebra_insert]
  rfl

theorem goodComplexConstruction_empty {I : Type} {μ μtilde : I → ComplexAtomicRows} {R Rtilde : I → Set ℕ}
    (ρ σ : I → ℕ → ComplexPairedMeasure) (d : ComplexConstructionData μ μtilde R Rtilde) :
    GoodComplexConstruction ρ σ d ∅ := by
  intro i hi
  exact False.elim hi

end SigmaNonprimarity
