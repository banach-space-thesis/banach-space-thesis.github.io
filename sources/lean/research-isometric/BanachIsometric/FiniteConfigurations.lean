import BanachIsometric.LocalToGlobal

/-!
# Finite configurations in exact finite-dimensional subspaces

This extends the paper's two-vector reduction to the three-vector configurations
needed to glue local Hermitian forms without assuming a norm on the ambient
algebraic vector space.
-/

namespace BanachIsometric

open Module Submodule

variable {K X : Type*} [DivisionRing K] [AddCommGroup X] [Module K X]

theorem exists_subspace_containing_finset (s : Finset X) (m : ℕ)
    (hs : s.card ≤ m) (hm : (m : Cardinal) ≤ Module.rank K X) :
    ∃ Y : Submodule K X, (s : Set X) ⊆ Y ∧
      ∃ (_ : FiniteDimensional K Y), finrank K Y = m := by
  classical
  let Z : Submodule K X := span K (s : Set X)
  letI : FiniteDimensional K Z := FiniteDimensional.span_of_finite K s.finite_toSet
  have hZ : finrank K Z ≤ m := (finrank_span_finset_le_card s).trans hs
  obtain ⟨Y, hZY, hYfinite, hYdim⟩ := exists_extension_of_finrank_le m hm Z hZ
  exact ⟨Y, fun _ hx ↦ hZY (subset_span hx), hYfinite, hYdim⟩

theorem exists_subspace_containing_triple (m : ℕ) (hm3 : 3 ≤ m)
    (hm : (m : Cardinal) ≤ Module.rank K X) (x y z : X) :
    ∃ Y : Submodule K X, x ∈ Y ∧ y ∈ Y ∧ z ∈ Y ∧
      ∃ (_ : FiniteDimensional K Y), finrank K Y = m := by
  classical
  obtain ⟨Y, hY, hfinite, hdim⟩ :=
    exists_subspace_containing_finset (K := K) ({x, y, z} : Finset X) m
      ((Finset.card_le_three).trans hm3) hm
  exact ⟨Y, hY (by simp), hY (by simp), hY (by simp), hfinite, hdim⟩

end BanachIsometric
