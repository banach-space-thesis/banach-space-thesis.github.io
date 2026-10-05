import Posets.ProductQuotientRealizationData
import Posets.ProductQuotient
import Posets.MainTheorem
import Posets.PosetFamilyEmbedding

/-! One global poset family realizes all the chosen quotient components. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon TopologicalSpace
namespace Posets

def HasQuantitativeSplit (𝕜 : Type) [RCLike 𝕜] (Y C : Type)
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C] : Prop :=
  ∃ θ : BoundedHom 𝕜 (Y →L[𝕜] Y) C,
  ∃ ρ : BoundedHom 𝕜 C (Y →L[𝕜] Y),
    StrongSplit 𝕜 Y C θ ρ ∧ Isometry ρ ∧ ‖θ.toContinuousLinearMap‖ ≤ 1 ∧
      (Nontrivial C → ‖θ.toContinuousLinearMap‖ = 1)

theorem product_hasQuantitativeSplit {𝕜 : Type} [RCLike 𝕜]
    {Y C : ℕ → Type} [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace 𝕜 (Y n)]
    [∀ n, NormedRing (C n)] [∀ n, NormedAlgebra 𝕜 (C n)]
    (hc : ∀ n, HasContractiveSplit 𝕜 (Y n) (C n))
    (hoff : ∀ s t, s ≠ t → ∀ T : Y t →L[𝕜] Y s, HasSeparableRange 𝕜 (Y t) (Y s) T) :
    HasQuantitativeSplit 𝕜 (DependentCZeroSum 𝕜 Y) (NormedProduct C) := by
  choose θ ρ hs hρ hθ using hc
  exact exists_product_strongSplit θ ρ hs hθ hρ hoff

variable {𝕜 : Type} [RCLike 𝕜] {C : ℕ → Type}
  [∀ n, NormedRing (C n)] [∀ n, NormedAlgebra 𝕜 (C n)]
  (d : ∀ n, ProductQuotientComponent 𝕜 (C n))

abbrev ProductPointPoset := Σ n, (d n).Points

def productLeafFamily (𝒜 : BoundedExtension (ProductPointPoset d) → Set (Set ℕ))
    (n : ℕ) : (d n).Coordinates → Set (Set ℕ) :=
  quotientLeafFamily (d n).origin (fun p => 𝒜 (middle ⟨n, p⟩))

abbrev ProductLeafSum (B : ∀ n, (d n).Coordinates → Set (Set ℕ)) (n : ℕ) : Type :=
  DependentCZeroSum 𝕜 (fun q => Space 𝕜 (B n q))

theorem productLeafFamily_almostDisjoint
    (𝒜 : BoundedExtension (ProductPointPoset d) → Set (Set ℕ))
    (had : ∀ p, IsAlmostDisjoint (𝒜 p)) (n : ℕ) (q : (d n).Coordinates) :
    IsAlmostDisjoint (productLeafFamily d 𝒜 n q) := by
  unfold productLeafFamily quotientLeafFamily
  cases hq : (d n).origin q with
  | none => exact ⟨fun _ h => False.elim h, fun _ h => False.elim h⟩
  | some p => exact had (middle ⟨n, p⟩)

theorem productLeafFamily_componentSplit
    (𝒜 : BoundedExtension (ProductPointPoset d) → Set (Set ℕ))
    (had : ∀ p, IsAlmostDisjoint (𝒜 p))
    (ι : ∀ s t, Space 𝕜 (𝒜 s) →L[𝕜] Space 𝕜 (𝒜 t))
    (h : FewOperators 𝕜 (fun p => Space 𝕜 (𝒜 p)) ι) (n : ℕ) :
    HasContractiveSplit 𝕜 (ProductLeafSum d (productLeafFamily d 𝒜) n) (C n) := by
  let e := boundedFiberEmbedding (fun n => (d n).Points) n
  exact (d n).realizes (fun p => 𝒜 (e p)) (fun p => had (e p))
    (fun s t => ι (e s) (e t)) (h.restrict e)

theorem productLeafFamily_offDiagonal [SeparableSpace (Space 𝕜 ∅)]
    (𝒜 : BoundedExtension (ProductPointPoset d) → Set (Set ℕ))
    (ι : ∀ s t, Space 𝕜 (𝒜 s) →L[𝕜] Space 𝕜 (𝒜 t))
    (h : FewOperators 𝕜 (fun p => Space 𝕜 (𝒜 p)) ι)
    (s t : ℕ) (hst : s ≠ t)
    (T : ProductLeafSum d (productLeafFamily d 𝒜) t →L[𝕜]
      ProductLeafSum d (productLeafFamily d 𝒜) s) :
    HasSeparableRange 𝕜 (ProductLeafSum d (productLeafFamily d 𝒜) t)
      (ProductLeafSum d (productLeafFamily d 𝒜) s) T := by
  apply productSums_hasSeparableRange_of_blocks _ _ T
  intro q p
  generalize hU : operatorBlock 𝕜 _ _ T q p = U
  clear hU
  change Space 𝕜 (((d t).origin p).elim ∅ (fun a => 𝒜 (middle ⟨t, a⟩))) →L[𝕜]
    Space 𝕜 (((d s).origin q).elim ∅ (fun a => 𝒜 (middle ⟨s, a⟩))) at U
  change HasSeparableRange 𝕜
    (Space 𝕜 (((d t).origin p).elim ∅ (fun a => 𝒜 (middle ⟨t, a⟩))))
    (Space 𝕜 (((d s).origin q).elim ∅ (fun a => 𝒜 (middle ⟨s, a⟩)))) U
  revert U
  cases hp : (d t).origin p with
  | none =>
    dsimp only [Option.elim]
    intro U
    exact isSeparable_range U.continuous
  | some a =>
    cases hq : (d s).origin q with
    | none =>
      dsimp only [Option.elim]
      intro U
      exact IsSeparable.of_separableSpace _
    | some b =>
      dsimp only [Option.elim]
      intro U
      exact h.2.2.2.2.2 (middle ⟨t, a⟩) (middle ⟨s, b⟩)
        (middle_sigma_not_le_of_ne (P := fun n => (d n).Points) hst.symm a b) U

theorem productLeafFamily_hasQuantitativeSplit [SeparableSpace (Space 𝕜 ∅)]
    (𝒜 : BoundedExtension (ProductPointPoset d) → Set (Set ℕ))
    (had : ∀ p, IsAlmostDisjoint (𝒜 p))
    (ι : ∀ s t, Space 𝕜 (𝒜 s) →L[𝕜] Space 𝕜 (𝒜 t))
    (h : FewOperators 𝕜 (fun p => Space 𝕜 (𝒜 p)) ι) :
    HasQuantitativeSplit 𝕜 (DependentCZeroSum 𝕜 (ProductLeafSum d (productLeafFamily d 𝒜)))
      (NormedProduct C) := by
  exact product_hasQuantitativeSplit
    (𝕜 := 𝕜) (Y := ProductLeafSum d (productLeafFamily d 𝒜)) (C := C)
    (productLeafFamily_componentSplit d 𝒜 had ι h)
    (productLeafFamily_offDiagonal d 𝒜 ι h)

theorem exists_product_leaf_realization [SeparableSpace (Space 𝕜 ∅)] :
    ∃ B : ∀ n, (d n).Coordinates → Set (Set ℕ),
      (∀ n q, IsAlmostDisjoint (B n q)) ∧
      HasQuantitativeSplit 𝕜 (DependentCZeroSum 𝕜 (ProductLeafSum d B)) (NormedProduct C) := by
  obtain ⟨𝒜, had, ι, h⟩ := continuum_fewOperators 𝕜
    (countablePosetSetEmbedding (BoundedExtension (ProductPointPoset d)))
  exact ⟨productLeafFamily d 𝒜, productLeafFamily_almostDisjoint d 𝒜 (fun p => (had p).1),
    productLeafFamily_hasQuantitativeSplit d 𝒜 (fun p => (had p).1) ι h⟩

end Posets
