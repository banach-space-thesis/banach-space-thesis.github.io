import BanachIsometric.LocalToGlobal
import BanachIsometric.HyperplanePairCoverage
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Uniform intersection dimensions force a trivial kernel

This is the linear-algebra kernel step in Theorem D. The uniform dimension
premise is explicit here; its derivation from simultaneous similarities belongs
to a later application. The argument works over any division ring and allows
an infinite-dimensional ambient space.
-/

namespace BanachIsometric

variable {𝕜 X : Type*} [DivisionRing 𝕜] [AddCommGroup X] [Module 𝕜 X]

private theorem functional_kernel_finrank [FiniteDimensional 𝕜 X]
    (f : X →ₗ[𝕜] 𝕜) (hf : f ≠ 0) :
    Module.finrank 𝕜 (LinearMap.ker f) + 1 = Module.finrank 𝕜 X := by
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (nonzero_functional_surjective hf),
    finrank_top, Module.finrank_self] at h
  omega

/-- In dimension `n+1`, a nonzero proper subspace meets two hyperplanes in
different dimensions. Consequently uniform hyperplane intersection dimension
forces the subspace to be zero or the entire space. -/
theorem submodule_bot_or_top_of_uniform_hyperplane_intersection
    [FiniteDimensional 𝕜 X] (N : Submodule 𝕜 X) (n : ℕ)
    (hdim : Module.finrank 𝕜 X = n + 1)
    (huniform : ∀ E F : Submodule 𝕜 X,
      Module.finrank 𝕜 E = n → Module.finrank 𝕜 F = n →
        Module.finrank 𝕜 ↥(E ⊓ N) = Module.finrank 𝕜 ↥(F ⊓ N)) :
    N = ⊥ ∨ N = ⊤ := by
  classical
  by_contra htrivial
  have hN0 : N ≠ ⊥ := fun h => htrivial (Or.inl h)
  have hNtop : N ≠ ⊤ := fun h => htrivial (Or.inr h)
  obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  obtain ⟨g, hg, hNg⟩ := N.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hNtop)
  obtain ⟨f, hfx, _⟩ := Submodule.exists_le_ker_of_notMem
    (p := (⊥ : Submodule 𝕜 X)) (v := x) (by simpa using hx0)
  have hf : f ≠ 0 := by intro h; simp [h] at hfx
  let E := LinearMap.ker g
  let F := LinearMap.ker f
  have hE : Module.finrank 𝕜 E = n := by
    have h := functional_kernel_finrank g hg
    dsimp [E]
    omega
  have hF : Module.finrank 𝕜 F = n := by
    have h := functional_kernel_finrank f hf
    dsimp [F]
    omega
  have hEN : E ⊓ N = N := inf_eq_right.mpr hNg
  have hFNtop : F ⊔ N = ⊤ := by
    apply top_unique
    intro y _
    let c : 𝕜 := f y * (f x)⁻¹
    have hker : y - c • x ∈ F := by
      change f (y - c • x) = 0
      rw [map_sub, map_smul, smul_eq_mul]
      dsimp [c]
      rw [mul_assoc, inv_mul_cancel₀ hfx, mul_one, sub_self]
    exact Submodule.mem_sup.mpr
      ⟨y - c • x, hker, c • x, N.smul_mem c hxN, sub_add_cancel y (c • x)⟩
  have heq := huniform E F hE hF
  rw [hEN] at heq
  have hdimInf := F.finrank_sup_add_finrank_inf_eq N
  rw [hFNtop, finrank_top, hdim, hF, ← heq] at hdimInf
  omega

/-- Uniform intersection dimensions with all `n`-dimensional subspaces force
a kernel to be zero or total. This does not assume finite ambient dimension.
The strict cardinal dimension bound prevents a vacuous family of subspaces. -/
theorem submodule_bot_or_top_of_uniform_intersection_finrank
    (N : Submodule 𝕜 X) (n : ℕ) (hn : 1 ≤ n)
    (hdim : (n : Cardinal) < Module.rank 𝕜 X)
    (huniform : ∀ E F : Submodule 𝕜 X,
      Module.finrank 𝕜 E = n → Module.finrank 𝕜 F = n →
        Module.finrank 𝕜 ↥(E ⊓ N) = Module.finrank 𝕜 ↥(F ⊓ N)) :
    N = ⊥ ∨ N = ⊤ := by
  classical
  by_contra htrivial
  have hN0 : N ≠ ⊥ := fun h => htrivial (Or.inl h)
  have hNtop : N ≠ ⊤ := fun h => htrivial (Or.inr h)
  obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  obtain ⟨y, hyN⟩ : ∃ y : X, y ∉ N := by
    by_contra h
    exact hNtop (Submodule.eq_top_iff'.mpr (by simpa using h))
  have hroom : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank 𝕜 X := by
    simpa only [Nat.cast_add, Nat.cast_one] using Cardinal.natCast_add_one_le_iff.mpr hdim
  obtain ⟨Y, hxY, hyY, hfinite, hYdim⟩ :=
    exists_subspace_containing_pair (n + 1) (by omega) hroom x y
  letI : FiniteDimensional 𝕜 Y := hfinite
  let L : Submodule 𝕜 Y := N.comap Y.subtype
  have hmapdim (A : Submodule 𝕜 Y) :
      Module.finrank 𝕜 (A.map Y.subtype) = Module.finrank 𝕜 A :=
    (Submodule.equivMapOfInjective Y.subtype Y.subtype_injective A).finrank_eq.symm
  have hmapinter (A : Submodule 𝕜 Y) :
      Module.finrank 𝕜 ↥(A.map Y.subtype ⊓ N) = Module.finrank 𝕜 ↥(A ⊓ L) := by
    rw [Submodule.map_inf_eq_map_inf_comap]
    exact hmapdim (A ⊓ L)
  have hlocal : ∀ A B : Submodule 𝕜 Y,
      Module.finrank 𝕜 A = n → Module.finrank 𝕜 B = n →
        Module.finrank 𝕜 ↥(A ⊓ L) = Module.finrank 𝕜 ↥(B ⊓ L) := by
    intro A B hA hB
    have h := huniform (A.map Y.subtype) (B.map Y.subtype)
      ((hmapdim A).trans hA) ((hmapdim B).trans hB)
    simpa only [hmapinter] using h
  rcases submodule_bot_or_top_of_uniform_hyperplane_intersection L n hYdim hlocal with
    hL0 | hLtop
  · have hxL : (⟨x, hxY⟩ : Y) ∈ L := hxN
    rw [hL0] at hxL
    exact hx0 (congrArg Subtype.val hxL)
  · have hyL : (⟨y, hyY⟩ : Y) ∈ L := by rw [hLtop]; trivial
    exact hyN hyL

end BanachIsometric

