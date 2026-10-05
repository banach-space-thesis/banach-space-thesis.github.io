import Posets.QuotientStatements
import Posets.Multipliers
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open ThesisCommon Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜]

/-- The explicit finite sets I_k with the permitted minimal cardinality.
Lean k=0 is the paper's k=1, and n=0 is the paper's f₁. -/
abbrev Block (k : ℕ) := Fin ((k + 1) * 2 ^ (k + 1))
abbrev RowDomain := Σ k : ℕ, Fin (k + 1) ↪ Block k
abbrev ColumnDomain := Σ k : ℕ, Block k

def selector (n : ℕ) (x : RowDomain) : ColumnDomain :=
  ⟨x.1, x.2 (if h : n < x.1 + 1 then ⟨n, h⟩ else ⟨0, Nat.zero_lt_succ _⟩)⟩

def Synchronized (U : Ultrafilter RowDomain) (V : Ultrafilter ColumnDomain) : Prop :=
  (U : Filter RowDomain) ≤ cofinite ∧ (V : Filter ColumnDomain) ≤ cofinite ∧
  (∀ n, Ultrafilter.map (selector n) U = V) ∧
  ∀ n m, n ≠ m → {x | selector n x = selector m x} ∉ U

def Lemma_8_1 : Prop := ∃ U V, Synchronized U V

abbrev OffDiagonal := CZeroOn 𝕜 ColumnDomain →L[𝕜] CZeroOn 𝕜 RowDomain

/-- Lemma 8.2, using the constructed bounded multiplication operators.
The ultrafilter limits are those of bounded scalar functions. -/
def Lemma_8_2 (U : Ultrafilter RowDomain) (V : Ultrafilter ColumnDomain) : Prop :=
  Synchronized U V →
  ∃ L : OffDiagonal 𝕜 →ₗ[𝕜] 𝕜, ¬ Continuous L ∧
    (∀ (a : Discrete RowDomain →ᵇ 𝕜) (T : OffDiagonal 𝕜),
      L ((multiplicationOperator a).comp T) =
        limUnder (U : Filter RowDomain) (fun x => a ⟨x⟩) * L T) ∧
    (∀ (b : Discrete ColumnDomain →ᵇ 𝕜) (T : OffDiagonal 𝕜),
      L (T.comp (multiplicationOperator b)) =
        L T * limUnder (V : Filter ColumnDomain) (fun x => b ⟨x⟩))

/-- Lemma 8.3. The linear homomorphism may be discontinuous. Finite-rank
annihilation, same range, both continuity implications, and both compactness
implications are retained. -/
def Lemma_8_3 (K₀ : Type) [TopologicalSpace K₀] [LocallyCompactSpace K₀] [T2Space K₀]
    (C : Type) [NormedRing C] [NormedAlgebra 𝕜 C] [CompleteSpace C]
    (Ψ : (C₀(K₀, 𝕜) →L[𝕜] C₀(K₀, 𝕜)) →ₗ[𝕜] C) : Prop :=
  IsMultiplicative 𝕜 Ψ →
  (∀ T, FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap) → Ψ T = 0) →
  ∃ Φ : (C(OnePoint K₀, 𝕜) →L[𝕜] C(OnePoint K₀, 𝕜)) →ₗ[𝕜] C,
    IsMultiplicative 𝕜 Φ ∧ Set.range Φ = Set.range Ψ ∧
    (Continuous Φ ↔ Continuous Ψ) ∧ (IsCompactOperator Φ ↔ IsCompactOperator Ψ) ∧
    (Function.Surjective Ψ → Function.Surjective Φ) ∧ (¬ Continuous Ψ → ¬ Continuous Φ)

end Posets
