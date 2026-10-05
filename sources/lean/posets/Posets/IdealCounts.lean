import Posets.QuotientStatements

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open ThesisCommon
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜]

/-- Upward closed subsets of Int(P), where intervals are ordered by containment. -/
def IntervalUpsets (P : Type*) [PartialOrder P] :=
  {W : Set {st : P × P // st.1 ≤ st.2} //
    ∀ i ∈ W, ∀ j, j.val.1 ≤ i.val.1 → i.val.2 ≤ j.val.2 → j ∈ W}

/-- Nat.card is used only with a finite P, so an infinite-cardinality collapse
cannot falsify a counting assertion. -/
def idealCount (P : Type*) [PartialOrder P] [Finite P] : ℕ := Nat.card (IntervalUpsets P)

def BipartiteLE {L R : Type*} (E : L → R → Prop) : L ⊕ R → L ⊕ R → Prop
  | .inl l, .inl l' => l = l'
  | .inl l, .inr r => E l r
  | .inr _, .inl _ => False
  | .inr r, .inr r' => r = r'

def bipartiteOrder {L R : Type*} (E : L → R → Prop) : PartialOrder (L ⊕ R) where
  le := BipartiteLE E
  le_refl x := by cases x <;> rfl
  le_trans x y z := by
    cases x <;> cases y <;> cases z <;> simp_all [BipartiteLE]
    intro h h'
    simpa [← h'] using h
  le_antisymm x y := by
    cases x <;> cases y <;> simp_all [BipartiteLE]

/-- Proposition 8.5, the double sum over all choices of missing diagonals. -/
def Proposition_8_5 (L R : Type) [Fintype L] [Fintype R] (E : L → R → Prop) : Prop :=
  letI := bipartiteOrder E
  idealCount (L ⊕ R) =
    ∑ I : Finset L, ∑ J : Finset R, 2 ^ ((I.product J).filter (fun e => E e.1 e.2)).card

/-- The exact realization supplied by Theorem 1.5, used to delimit the scope
of 'furnished by the construction' in Proposition 8.4. -/
def RealizesProduct (𝒜 : Set (Set ℕ)) (C : ℕ → Type) [∀ n, NormedRing (C n)]
    [∀ n, NormedAlgebra 𝕜 (C n)] : Prop :=
  ∃ θ : BoundedHom 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) (NormedProduct C),
  ∃ ρ : BoundedHom 𝕜 (NormedProduct C) (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜),
    StrongSplit 𝕜 (Space 𝕜 𝒜) (NormedProduct C) θ ρ ∧ Isometry ρ ∧
    (Nontrivial (NormedProduct C) → ‖θ.toContinuousLinearMap‖ = 1)

def FurnishedIdealCount (n : ℕ) : Prop :=
  ∃ (C : ℕ → Type) (_ : ∀ n, NormedRing (C n)) (_ : ∀ n, NormedAlgebra 𝕜 (C n))
    (_ : ∀ n, CompleteSpace (C n)),
    (∀ n, AdmissibleAlgebra 𝕜 (C n)) ∧
    ∃ 𝒜 : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧ RealizesProduct 𝕜 𝒜 C ∧
      Nonempty (NontrivialClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) ≃ Fin n)

/-- Proposition 8.4 AS PRINTED, including converse, maximal-ideal count and
the exceptional all-zero case. Empty finite P_i remain allowed; see discrepancies. -/
def Proposition_8_4_printed : Prop :=
  (∀ n, FurnishedIdealCount 𝕜 n ↔
    ∃ r k : ℕ, ∃ (P : Fin k → Type) (_ : ∀ i, Fintype (P i)) (_ : ∀ i, PartialOrder (P i)),
      n = 3 ^ r * ∏ i, idealCount (P i)) ∧
  (∀ r k : ℕ, ∀ (P : Fin k → Type) [∀ i, Fintype (P i)] [∀ i, PartialOrder (P i)],
    1 ≤ r + k → ∃ 𝒜 : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧
      Nonempty (NontrivialClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) ≃
        Fin (3 ^ r * ∏ i, idealCount (P i))) ∧
      Nonempty (MaximalClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) ≃
        Fin (r + ∑ i, Fintype.card (P i)))) ∧
  Nonempty (NontrivialClosedIdeals 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜) ≃ Fin 1) ∧
  HasUniqueMaximalClosedIdeal 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜)

/-- The usual nonempty-poset convention, confirmed by the author. Zero factors
remain represented separately, and the exceptional empty product remains. -/
def Proposition_8_4 : Prop :=
  (∀ n, FurnishedIdealCount 𝕜 n ↔
    ∃ r k : ℕ, ∃ (P : Fin k → Type) (_ : ∀ i, Fintype (P i)) (_ : ∀ i, PartialOrder (P i))
      (_ : ∀ i, Nonempty (P i)), n = 3 ^ r * ∏ i, idealCount (P i)) ∧
  (∀ r k : ℕ, ∀ (P : Fin k → Type) [∀ i, Fintype (P i)] [∀ i, PartialOrder (P i)]
    [∀ i, Nonempty (P i)],
    1 ≤ r + k → ∃ 𝒜 : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧
      Nonempty (NontrivialClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) ≃
        Fin (3 ^ r * ∏ i, idealCount (P i))) ∧
      Nonempty (MaximalClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) ≃
        Fin (r + ∑ i, Fintype.card (P i)))) ∧
  Nonempty (NontrivialClosedIdeals 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜) ≃ Fin 1) ∧
  HasUniqueMaximalClosedIdeal 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜)

end Posets
