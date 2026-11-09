import BanachIsometric.FiniteAlexanderWhitneyGeometry
import BanachIsometric.FiniteTensorComparison

/-! The actual finite ordered-face Alexander–Whitney diagonal agrees
EXACTLY with the proved raw singular diagonal under the actual barycentric
chain comparison. This module defines finite tensor values and proves their
correspondence; it does not assume or assert a homology comparison inverse. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open SingularPrism SingularAW
open scoped Topology TensorProduct DirectSum

variable {ι : Type} [LinearOrder ι] [Fintype ι]

def finiteAWPureTerm (K : Complex ι) {n : ℕ} (v : StrictOrderedSimplex K n)
    (p q : ℕ) (h : p + q = n) : FiniteTensorChains K p q :=
  Finsupp.single (strictFrontFace K v p (by omega)) 1 ⊗ₜ[ℚ]
    Finsupp.single (strictBackFace K v p q h) 1

def finiteAWDiagonal (K : Complex ι) (n : ℕ) :
    FiniteRationalChains K n →ₗ[ℚ] FiniteBigradedTensorChains K :=
  Finsupp.linearCombination ℚ (fun v =>
    ∑ ij ∈ (Finset.antidiagonal n).attach,
      finiteTensorInclusion K ij.val.1 ij.val.2
        (finiteAWPureTerm K v ij.val.1 ij.val.2 (Finset.mem_antidiagonal.mp ij.property)))

theorem finiteAWDiagonal_single_one (K : Complex ι) (n : ℕ) (v : StrictOrderedSimplex K n) :
    finiteAWDiagonal K n (Finsupp.single v 1) =
      ∑ ij ∈ (Finset.antidiagonal n).attach,
        finiteTensorInclusion K ij.val.1 ij.val.2
          (finiteAWPureTerm K v ij.val.1 ij.val.2 (Finset.mem_antidiagonal.mp ij.property)) := by
  simp only [finiteAWDiagonal, Finsupp.linearCombination_single, one_smul]

theorem finiteAWFront_barycentric (K : Complex ι) {n : ℕ} (v : StrictOrderedSimplex K n)
    (p : ℕ) (hp : p ≤ n) :
    simplexFrontProjection
      ((⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩ : C(K.space, K.space × K.space)).comp
        (barycentricSingularSimplex K n v)) p hp =
      barycentricSingularSimplex K p (strictFrontFace K v p hp) := by
  rw [barycentricSingularSimplex_frontFace]
  apply ContinuousMap.ext
  intro t
  rfl

theorem finiteAWBack_barycentric (K : Complex ι) {n : ℕ} (v : StrictOrderedSimplex K n)
    (p q : ℕ) (h : p + q = n) :
    simplexBackProjection
      ((⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩ : C(K.space, K.space × K.space)).comp
        (barycentricSingularSimplex K n v)) p q h =
      barycentricSingularSimplex K q (strictBackFace K v p q h) := by
  rw [barycentricSingularSimplex_backFace]
  apply ContinuousMap.ext
  intro t
  rfl

theorem finiteAWPureTerm_barycentric (K : Complex ι) {n : ℕ} (v : StrictOrderedSimplex K n)
    (p q : ℕ) (h : p + q = n) :
    awPureTerm
      ((⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩ : C(K.space, K.space × K.space)).comp
        (barycentricSingularSimplex K n v)) p q h =
      TensorProduct.map (finiteToRawSingularChain K p) (finiteToRawSingularChain K q)
        (finiteAWPureTerm K v p q h) := by
  simp only [awPureTerm, finiteAWPureTerm, TensorProduct.map_tmul,
    finiteToRawSingularChain_single, finiteAWFront_barycentric, finiteAWBack_barycentric]

theorem finiteAWDiagonal_barycentric (K : Complex ι) (n : ℕ) :
    (rawAlexanderWhitneyDiagonal n).comp (finiteToRawSingularChain K n) =
      (finiteTensorToRaw K).comp (finiteAWDiagonal K n) := by
  apply Finsupp.lhom_ext
  intro v a
  have ha : Finsupp.single v a = a • Finsupp.single v 1 := by simp
  rw [ha]
  simp only [map_smul]
  congr 1
  simp only [LinearMap.comp_apply, finiteToRawSingularChain_single,
    rawAlexanderWhitneyDiagonal_single, rawAlexanderWhitney_single, one_smul,
    finiteAWDiagonal_single_one, map_sum, finiteTensorToRaw_inclusion]
  apply Finset.sum_congr rfl
  intro ij _
  rw [finiteAWPureTerm_barycentric]

end BanachIsometric.FiniteNerve
