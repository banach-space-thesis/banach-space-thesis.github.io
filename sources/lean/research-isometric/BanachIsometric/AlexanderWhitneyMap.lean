import BanachIsometric.AlexanderWhitneyGeometry
import BanachIsometric.RawTensorBicomplex
import Mathlib.Data.Finset.NatAntidiagonal

/-! The concrete Alexander--Whitney linear map on actual rational singular
chains. Every summand is the front restriction in X tensored with the back
restriction in Y. This file defines the map; its chain identity is a separate
proof, and no Kunneth or shuffle equivalence is asserted. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped Topology TensorProduct DirectSum

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def simplexFrontProjection {n : ℕ} (σ : RawSingularSimplex (X × Y) n)
    (p : ℕ) (hp : p ≤ n) : RawSingularSimplex X p :=
  (⟨Prod.fst, continuous_fst⟩ : C(X × Y, X)).comp (σ.comp (frontSimplex p n hp))

def simplexBackProjection {n : ℕ} (σ : RawSingularSimplex (X × Y) n)
    (p q : ℕ) (h : p + q = n) : RawSingularSimplex Y q :=
  (⟨Prod.snd, continuous_snd⟩ : C(X × Y, Y)).comp (σ.comp (backSimplex p q n h))

def awPureTerm {n : ℕ} (σ : RawSingularSimplex (X × Y) n)
    (p q : ℕ) (h : p + q = n) : RawTensorChains X Y p q :=
  Finsupp.single (simplexFrontProjection σ p (by omega)) 1 ⊗ₜ[ℚ]
    Finsupp.single (simplexBackProjection σ p q h) 1

def awSummand (n p q : ℕ) (h : p + q = n) :
    RawRationalChains (X × Y) n →ₗ[ℚ] RawBigradedTensorChains X Y :=
  Finsupp.linearCombination ℚ (fun σ => rawTensorInclusion X Y p q (awPureTerm σ p q h))

@[simp] theorem awSummand_single (n p q : ℕ) (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) n) (a : ℚ) :
    awSummand n p q h (Finsupp.single σ a) =
      a • rawTensorInclusion X Y p q (awPureTerm σ p q h) := by
  simp only [awSummand, Finsupp.linearCombination_single]

def rawAlexanderWhitney (n : ℕ) :
    RawRationalChains (X × Y) n →ₗ[ℚ] RawBigradedTensorChains X Y :=
  ∑ ij ∈ (Finset.antidiagonal n).attach,
    awSummand n ij.val.1 ij.val.2 (Finset.mem_antidiagonal.mp ij.property)

theorem rawAlexanderWhitney_single (n : ℕ) (σ : RawSingularSimplex (X × Y) n) (a : ℚ) :
    rawAlexanderWhitney n (Finsupp.single σ a) =
      ∑ ij ∈ (Finset.antidiagonal n).attach,
        a • rawTensorInclusion X Y ij.val.1 ij.val.2
          (awPureTerm σ ij.val.1 ij.val.2 (Finset.mem_antidiagonal.mp ij.property)) := by
  simp only [rawAlexanderWhitney, LinearMap.sum_apply, awSummand_single]

def rawAlexanderWhitneyDiagonal (n : ℕ) :
    RawRationalChains X n →ₗ[ℚ] RawBigradedTensorChains X X :=
  (rawAlexanderWhitney (X := X) (Y := X) n).comp
    (rawChainMap (⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩ : C(X, X × X)) n)

theorem rawAlexanderWhitneyDiagonal_single (n : ℕ) (σ : RawSingularSimplex X n) (a : ℚ) :
    rawAlexanderWhitneyDiagonal n (Finsupp.single σ a) =
      rawAlexanderWhitney n
        (Finsupp.single ((⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩ :
          C(X, X × X)).comp σ) a) := by
  simp only [rawAlexanderWhitneyDiagonal, LinearMap.comp_apply, rawChainMap,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

end BanachIsometric.SingularAW
