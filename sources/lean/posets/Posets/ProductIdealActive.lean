import Posets.ProductIdealClosed
import Posets.Models

/-! Active coordinates of a bounded product give distinct closed kernel
ideals. In particular finitely many closed ideals force finitely many
nonzero factors, without any uniform bound on the norms of their units. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set ThesisCommon
open scoped ENNReal
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} (C : ι → Type*) [∀ i, NormedRing (C i)]
  [∀ i, NormedAlgebra 𝕜 (C i)]

def lpCoordinateKernel (i : ι) : ClosedIdeal 𝕜 (lp C ∞) := by
  refine ⟨{x | x i = 0}, ?_, rfl, ?_, ?_, ?_⟩
  · exact isClosed_singleton.preimage
      ((continuous_apply i).comp lp.uniformContinuous_coe.continuous)
  · intro x hx y hy
    change x i + y i = 0
    rw [hx, hy, add_zero]
  · intro c x hx
    change c • x i = 0
    rw [hx, smul_zero]
  · intro x y hy
    change y i = 0 at hy
    change x i * y i = 0 ∧ y i * x i = 0
    simp only [hy, mul_zero, zero_mul, and_self]

def activeCoordinateKernelEmbedding :
    {i : ι // Nontrivial (C i)} ↪ ClosedIdeal 𝕜 (lp C ∞) where
  toFun i := lpCoordinateKernel (𝕜 := 𝕜) C i.val
  inj' := by
    intro i j hij
    change lpCoordinateKernel (𝕜 := 𝕜) C i.val = lpCoordinateKernel (𝕜 := 𝕜) C j.val at hij
    apply Subtype.ext
    by_contra hne
    letI : Nontrivial (C i.val) := i.property
    obtain ⟨a, ha⟩ := exists_ne (0 : C i.val)
    have hj : lp.single ∞ i.val a ∈ (lpCoordinateKernel (𝕜 := 𝕜) C j.val).val := by
      change lp.single ∞ i.val a j.val = 0
      simp [lp.single_apply, Pi.single_eq_of_ne (Ne.symm hne)]
    rw [← hij] at hj
    change lp.single ∞ i.val a i.val = 0 at hj
    exact ha (by simpa using hj)

theorem finite_activeCoordinates_of_finite_closedIdeals
    [Finite (ClosedIdeal 𝕜 (lp C ∞))] : Finite {i : ι // Nontrivial (C i)} :=
  Finite.of_injective (activeCoordinateKernelEmbedding (𝕜 := 𝕜) C)
    (activeCoordinateKernelEmbedding (𝕜 := 𝕜) C).injective

theorem infinite_closedIdeals_of_infinite_activeCoordinates
    [Infinite {i : ι // Nontrivial (C i)}] : Infinite (ClosedIdeal 𝕜 (lp C ∞)) :=
  Infinite.of_injective (activeCoordinateKernelEmbedding (𝕜 := 𝕜) C)
    (activeCoordinateKernelEmbedding (𝕜 := 𝕜) C).injective

/-- For a sequence of factors, a finite ideal set forces every sufficiently
late coordinate algebra to be zero. -/
theorem normedProduct_eventually_subsingleton_of_finite_closedIdeals
    (D : ℕ → Type*) [∀ n, NormedRing (D n)] [∀ n, NormedAlgebra 𝕜 (D n)]
    [Finite (ClosedIdeal 𝕜 (lp D ∞))] :
    ∃ N : ℕ, ∀ n, N ≤ n → Subsingleton (D n) := by
  have hfin : {n : ℕ | Nontrivial (D n)}.Finite :=
    finite_activeCoordinates_of_finite_closedIdeals (𝕜 := 𝕜) D
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N + 1, fun n hn => ?_⟩
  by_contra h
  have hnt : Nontrivial (D n) := not_subsingleton_iff_nontrivial.mp h
  have hle := hN hnt
  omega

end Posets
