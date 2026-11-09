import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite-dimensional detection of the parallelogram identity

These are dimension and polarization reductions used in the paper. They do not
assert that equivalent sections are ellipsoids.
-/

namespace BanachIsometric

open Module Submodule

section Dimension

variable {K X : Type*} [DivisionRing K] [AddCommGroup X] [Module K X]

/-- Enlarge a finite-dimensional subspace to any prescribed finite dimension
available in the ambient space. The ambient space may be infinite-dimensional. -/
theorem exists_extension_of_finrank_le (m : ℕ) (hm : (m : Cardinal) ≤ Module.rank K X)
    (Z : Submodule K X) [FiniteDimensional K Z] (hZ : finrank K Z ≤ m) :
    ∃ Y : Submodule K X, Z ≤ Y ∧ ∃ (_ : FiniteDimensional K Y), finrank K Y = m := by
  classical
  induction m generalizing Z with
  | zero =>
      have hzero : Z = ⊥ := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hZ)
      exact ⟨⊥, hzero.le, inferInstance, finrank_bot K X⟩
  | succ m ih =>
      by_cases hZm : finrank K Z ≤ m
      · have hnat : (m : Cardinal) ≤ ((m + 1 : ℕ) : Cardinal) := by
          exact_mod_cast Nat.le_succ m
        have hm' : (m : Cardinal) ≤ Module.rank K X := hnat.trans hm
        obtain ⟨Y, hZY, hYfinite, hYdim⟩ := ih hm' Z hZm
        letI : FiniteDimensional K Y := hYfinite
        have hYrank : Module.rank K Y = (m : Cardinal) := by
          rw [← finrank_eq_rank, hYdim]
        have hlt : Module.rank K Y < Module.rank K X := by
          rw [hYrank]
          exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hm
        obtain ⟨v, hv⟩ := Submodule.exists_smul_notMem_of_rank_lt hlt
        have hvY : v ∉ Y := by simpa using hv 1 one_ne_zero
        have hv0 : v ≠ 0 := by
          intro h
          subst v
          exact hvY Y.zero_mem
        refine ⟨Y ⊔ K ∙ v, hZY.trans le_sup_left, inferInstance, ?_⟩
        have hdis := Submodule.disjoint_span_singleton_of_notMem hvY
        have hdim := Y.finrank_sup_add_finrank_inf_eq (K ∙ v)
        rw [hdis.eq_bot, finrank_bot, add_zero, hYdim, finrank_span_singleton hv0] at hdim
        exact hdim
      · exact ⟨Z, le_rfl, inferInstance, by omega⟩

/-- Every pair is contained in a subspace of a fixed available finite dimension. -/
theorem exists_subspace_containing_pair (m : ℕ) (hm2 : 2 ≤ m)
    (hm : (m : Cardinal) ≤ Module.rank K X) (x y : X) :
    ∃ Y : Submodule K X, x ∈ Y ∧ y ∈ Y ∧
      ∃ (_ : FiniteDimensional K Y), finrank K Y = m := by
  classical
  let Z : Submodule K X := span K ({x, y} : Set X)
  letI : FiniteDimensional K Z := FiniteDimensional.span_of_finite K (by simp)
  have hZ : finrank K Z ≤ m := by
    have hdim := finrank_span_finset_le_card (R := K) ({x, y} : Finset X)
    have hcard : ({x, y} : Finset X).card ≤ 2 := Finset.card_le_two
    exact (show finrank K Z ≤ ({x, y} : Finset X).card by simpa [Z] using hdim).trans
      (hcard.trans hm2)
  obtain ⟨Y, hZY, hYfinite, hYdim⟩ := exists_extension_of_finrank_le m hm Z hZ
  exact ⟨Y, hZY (subset_span (by simp)), hZY (subset_span (by simp)), hYfinite, hYdim⟩

end Dimension

section Normed

variable {K X : Type*} [RCLike K] [NormedAddCommGroup X] [NormedSpace K X]

/-- If every subspace of one available dimension at least two has an inner
product inducing its inherited norm, the ambient given norm is induced by an
inner product as well. This uses no completeness assumption. -/
theorem innerProductSpace_of_local (m : ℕ) (hm2 : 2 ≤ m)
    (hm : (m : Cardinal) ≤ Module.rank K X)
    (hlocal : ∀ Y : Submodule K X, FiniteDimensional K Y → finrank K Y = m →
      Nonempty (InnerProductSpace K Y)) : Nonempty (InnerProductSpace K X) := by
  refine ⟨InnerProductSpace.ofNorm (𝕜 := K) ?_⟩
  intro x y
  obtain ⟨Y, hx, hy, hYfinite, hYdim⟩ := exists_subspace_containing_pair m hm2 hm x y
  letI : FiniteDimensional K Y := hYfinite
  obtain ⟨hinner⟩ := hlocal Y hYfinite hYdim
  letI : InnerProductSpace K Y := hinner
  exact parallelogram_law_with_norm K (⟨x, hx⟩ : Y) (⟨y, hy⟩ : Y)

end Normed

end BanachIsometric
