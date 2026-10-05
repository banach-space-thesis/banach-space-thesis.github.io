import ThesisCommon.Analysis.FilterConvergenceSpace
import ThesisCommon.Analysis.QuantitativePrimary

/-! The distinct set-theoretic and operator hypotheses from Section 6.
These definitions refer to the actual filter-null space and actual bounded
operators. They do not put the desired factorisation conclusion into any
underlying space, filter, or measure definition. -/
noncomputable section
open Filter Topology
open scoped ENNReal Cardinal BigOperators
namespace ThesisCommon
universe u
variable {𝕜 : Type*} [RCLike 𝕜] {Γ : Type u} (F : Filter Γ)

/-- Definition 6.1: an actual coordinate subspace is K-isomorphic to X_F. -/
def IsFilterCopyingSet (K : ℝ) (A : Set Γ) : Prop :=
  1 ≤ K ∧ IsomorphicWithBound 𝕜 (FilterNullSpace 𝕜 F)
    (FilterSupportedSpace (𝕜 := 𝕜) F A) K

/-- Definition 6.2: one side of every two-colouring contains a copying set.
Using A and its complement quantifies exactly all two-piece partitions. -/
def IsFilterPrimaryUnderSums (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ A : Set Γ,
    (∃ C ⊆ A, IsFilterCopyingSet (𝕜 := 𝕜) F K C) ∨
    (∃ C ⊆ Aᶜ, IsFilterCopyingSet (𝕜 := 𝕜) F K C)

/-- The compressed operator R P_A T J, with the coordinate-subspace
inclusion explicitly supplied at the input. -/
def filterCompression (A : Set Γ)
    (J : FilterNullSpace 𝕜 F ≃L[𝕜] FilterSupportedSpace (𝕜 := 𝕜) F A)
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) :
    FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F :=
  J.symm.toContinuousLinearMap.comp ((filterProjectionTo F A).comp
    (T.comp ((filterSupportedSubmodule F A).subtypeL.comp J.toContinuousLinearMap)))

/-- Definition 6.3, including the norm product of the actual isomorphism
and its inverse. The approximating multiplier acts on the original X_F. -/
def IsFilterDiagonalisable (D : ℝ) : Prop :=
  1 ≤ D ∧ ∀ (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F)
    (η : ℝ), 0 < η → ∃ (A : Set Γ)
      (J : FilterNullSpace 𝕜 F ≃L[𝕜] FilterSupportedSpace (𝕜 := 𝕜) F A),
      ‖J.toContinuousLinearMap‖ * ‖J.symm.toContinuousLinearMap‖ ≤ D ∧
      ∃ a : lp (fun _ : Γ => 𝕜) ∞,
        ‖filterCompression F A J T - filterMultiplier F a‖ < η

/-- Definition 6.4: the two independent hypotheses of the abstract criterion. -/
def IsFilterPrimaryForFactorisation (K D : ℝ) : Prop :=
  IsFilterPrimaryUnderSums (𝕜 := 𝕜) F K ∧ IsFilterDiagonalisable (𝕜 := 𝕜) F D

/-- The explicit filter-isomorphism identity in Definition 6.6. The map
θ is an actual bijection onto the indicated subset. -/
def IsFilterCoordinateCopy (C : Set Γ) (θ : Γ ≃ C) : Prop :=
  ∀ A : Set Γ, A ∈ F ↔ ((fun γ => (θ γ).val) '' A) ∪ Cᶜ ∈ F

/-- Definition 6.6: containing a coordinate copy is purely set-theoretic. -/
def ContainsFilterCoordinateCopy (B : Set Γ) : Prop :=
  ∃ C ⊆ B, ∃ θ : Γ ≃ C, IsFilterCoordinateCopy F C θ

/-- Definition 6.7: every full-cardinality set contains a coordinate copy.
There are no analytic or diagonalisation hypotheses in this predicate. -/
def IsLargeSetSelfSimilarFilter : Prop :=
  ∀ B : Set Γ, Cardinal.mk B = Cardinal.mk Γ → ContainsFilterCoordinateCopy F B

/-- A finitely additive scalar measure on the full power set, of bounded
variation. No countable-additivity assumption is imposed. -/
structure BoundedScalarCharge (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u) where
  toFun : Set Γ → 𝕜
  map_empty : toFun ∅ = 0
  map_union : ∀ A B, Disjoint A B → toFun (A ∪ B) = toFun A + toFun B
  bounded_variation : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (A : Fin n → Set Γ),
    Pairwise (fun i j => Disjoint (A i) (A j)) → ∑ i, ‖toFun (A i)‖ ≤ C

namespace BoundedScalarCharge
instance : CoeFun (BoundedScalarCharge 𝕜 Γ) (fun _ => Set Γ → 𝕜) := ⟨toFun⟩

/-- Actual finite disjoint-family variation sums inside A. Taking arbitrary
disjoint subfamilies gives the same variation as finite partitions of A. -/
def variationValues (μ : BoundedScalarCharge 𝕜 Γ) (A : Set Γ) : Set ℝ :=
  {r | ∃ (n : ℕ) (B : Fin n → Set Γ),
    Pairwise (fun i j => Disjoint (B i) (B j)) ∧
    (∀ i, B i ⊆ A) ∧ r = ∑ i, ‖μ (B i)‖}

theorem variationValues_nonempty (μ : BoundedScalarCharge 𝕜 Γ) (A : Set Γ) :
    (variationValues μ A).Nonempty := by
  refine ⟨0, 0, fun _ => ∅, ?_, ?_, ?_⟩ <;> simp

theorem variationValues_bddAbove (μ : BoundedScalarCharge 𝕜 Γ) (A : Set Γ) :
    BddAbove (variationValues μ A) := by
  obtain ⟨C, _, hC⟩ := μ.bounded_variation
  refine ⟨C, ?_⟩
  rintro r ⟨n, B, hB, _, rfl⟩
  exact hC n B hB

/-- Total variation |μ|(A), constructed as the actual supremum of finite
disjoint-family sums, rather than supplied as uninterpreted data. -/
def variation (μ : BoundedScalarCharge 𝕜 Γ) (A : Set Γ) : ℝ := sSup (variationValues μ A)

theorem variation_nonneg (μ : BoundedScalarCharge 𝕜 Γ) (A : Set Γ) :
    0 ≤ μ.variation A :=
  le_csSup (μ.variationValues_bddAbove A) (by
    refine ⟨0, fun _ => ∅, ?_, ?_, ?_⟩ <;> simp)

theorem variation_mono (μ : BoundedScalarCharge 𝕜 Γ) {A B : Set Γ} (hAB : A ⊆ B) :
    μ.variation A ≤ μ.variation B := by
  apply csSup_le (μ.variationValues_nonempty A)
  rintro r ⟨n, C, hC, hCA, hr⟩
  exact le_csSup (μ.variationValues_bddAbove B) ⟨n, C, hC, fun i => (hCA i).trans hAB, hr⟩

/-- Uniform boundedness of the variation norms of a family of charges. -/
def UniformlyBounded (μ : Γ → BoundedScalarCharge 𝕜 Γ) : Prop :=
  ∃ C : ℝ, ∀ γ, (μ γ).variation Set.univ ≤ C

end BoundedScalarCharge
end ThesisCommon
