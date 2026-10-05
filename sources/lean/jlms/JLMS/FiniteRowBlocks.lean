import JLMS.BlockStabilization

/-!
# Normalized blocks specified by finite injective rows

Finite labelled coefficient rows are often easier to construct than functions
on all natural indices. This adapter records their image supports and transports
the coefficient normalization and order, with an exact finite-sum formula.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} [Fintype ι]
attribute [local instance] Classical.decEq Classical.propDecidable

def finiteRowCoefficient (h : ι → ℕ) (a : ι → 𝕜) (k : ℕ) : 𝕜 :=
  if hk : ∃ i, h i = k then a (Classical.choose hk) else 0

theorem finiteRowCoefficient_at (h : ι → ℕ) (hh : Function.Injective h)
    (a : ι → 𝕜) (i : ι) : finiteRowCoefficient h a (h i) = a i := by
  rw [finiteRowCoefficient, dif_pos ⟨i, rfl⟩]
  congr 1
  exact hh (Classical.choose_spec (show ∃ j, h j = h i from ⟨i, rfl⟩))

def NormalizedBlockSystem.ofFiniteRows (h : ℕ → ι → ℕ)
    (hh : ∀ n, Function.Injective (h n))
    (ho : ∀ n m, n < m → ∀ i j, h n i < h m j)
    (a : ℕ → ι → 𝕜) (ha : ∀ n, ∑ i, ‖a n i‖ = 1) :
    NormalizedBlockSystem 𝕜 where
  support n := Finset.univ.image (h n)
  coefficient n := finiteRowCoefficient (h n) (a n)
  mass_one n := by
    rw [Finset.sum_image (fun i _ j _ hij => hh n hij)]
    simp_rw [finiteRowCoefficient_at _ (hh n)]
    exact ha n
  ordered := by
    intro n m hnm i hi j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hj
    exact ho n m hnm i j

theorem NormalizedBlockSystem.ofFiniteRows_applyDual {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (h : ℕ → ι → ℕ) (hh : ∀ n, Function.Injective (h n))
    (ho : ∀ n m, n < m → ∀ i j, h n i < h m j)
    (a : ℕ → ι → 𝕜) (ha : ∀ n, ∑ i, ‖a n i‖ = 1)
    (f : ℕ → (X →L[𝕜] 𝕜)) (n : ℕ) :
    (NormalizedBlockSystem.ofFiniteRows h hh ho a ha).applyDual f n =
      ∑ i, a n i • f (h n i) := by
  change (∑ k ∈ Finset.univ.image (h n), finiteRowCoefficient (h n) (a n) k • f k) = _
  rw [Finset.sum_image (fun i _ j _ hij => hh n hij)]
  simp_rw [finiteRowCoefficient_at _ (hh n)]

end JLMS
