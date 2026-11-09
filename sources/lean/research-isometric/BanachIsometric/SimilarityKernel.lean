import BanachIsometric.KernelRigidity
import Mathlib.Data.Real.Basic

/-!
# Positive similarities preserve kernels and force kernel rigidity

This discharges the uniform-intersection-dimension premise of `KernelRigidity`
from the actual scalar-linear positive similarities in Theorem D. No norm,
topology, scalar homogeneity of the real-valued function, or Hilbertianity is
needed for this kernel argument.
-/

noncomputable section

namespace BanachIsometric

variable {𝕜 X : Type*} [DivisionRing 𝕜] [AddCommGroup X] [Module 𝕜 X]

private theorem similarity_preserves_kernel_iff
    (p : X → ℝ) (N : Submodule 𝕜 X) (hN : ∀ x, x ∈ N ↔ p x = 0)
    {E F : Submodule 𝕜 X} (T : E ≃ₗ[𝕜] F) {c : ℝ} (hc : 0 < c)
    (hT : ∀ x : E, p (T x : X) = c * p (x : X)) (x : E) :
    (T x : X) ∈ N ↔ (x : X) ∈ N := by
  constructor
  · intro hx
    apply (hN x.val).mpr
    have hz : c * p (x : X) = 0 := (hT x).symm.trans ((hN _).mp hx)
    exact (mul_eq_zero.mp hz).resolve_left hc.ne'
  · intro hx
    apply (hN _).mpr
    rw [hT x, (hN _).mp hx, mul_zero]

/-- An actual positive `p`-similarity restricts to an actual linear equivalence
between the intersections with its zero kernel. Both intersections are
submodules of the original ambient module. -/
def similarityKernelEquiv
    (p : X → ℝ) (N : Submodule 𝕜 X) (hN : ∀ x, x ∈ N ↔ p x = 0)
    (E F : Submodule 𝕜 X) (T : E ≃ₗ[𝕜] F) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x : E, p (T x : X) = c * p (x : X)) :
    ↥(E ⊓ N) ≃ₗ[𝕜] ↥(F ⊓ N) := by
  let f : ↥(E ⊓ N) →ₗ[𝕜] ↥(F ⊓ N) :=
    { toFun := fun x =>
        ⟨(T (⟨x.val, x.property.1⟩ : E)).val,
          (T (⟨x.val, x.property.1⟩ : E)).property,
          (similarity_preserves_kernel_iff p N hN T hc hT
            (⟨x.val, x.property.1⟩ : E)).mpr x.property.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact congrArg (fun z : F => (z : X)) (T.map_add
          (⟨x.val, x.property.1⟩ : E) (⟨y.val, y.property.1⟩ : E))
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact congrArg (fun z : F => (z : X)) (T.map_smul a (⟨x.val, x.property.1⟩ : E)) }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hTxy : T (⟨x.val, x.property.1⟩ : E) = T (⟨y.val, y.property.1⟩ : E) := by
      apply Subtype.ext
      exact congrArg (fun z : ↥(F ⊓ N) => (z : X)) hxy
    exact congrArg (fun z : E => (z : X)) (T.injective hTxy)
  · intro y
    let z : F := ⟨y.val, y.property.1⟩
    let x : E := T.symm z
    have hxN : x.val ∈ N := by
      apply (similarity_preserves_kernel_iff p N hN T hc hT x).mp
      simpa only [x, T.apply_symm_apply] using y.property.2
    refine ⟨⟨x.val, x.property, hxN⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun w : F => (w : X)) (T.apply_symm_apply z)

theorem similarity_kernel_finrank_eq
    (p : X → ℝ) (N : Submodule 𝕜 X) (hN : ∀ x, x ∈ N ↔ p x = 0)
    (E F : Submodule 𝕜 X) (T : E ≃ₗ[𝕜] F) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x : E, p (T x : X) = c * p (x : X)) :
    Module.finrank 𝕜 ↥(E ⊓ N) = Module.finrank 𝕜 ↥(F ⊓ N) :=
  (similarityKernelEquiv p N hN E F T c hc hT).finrank_eq

/-- The kernel assertion in Theorem D, with the actual similarity hypothesis.
Uniform intersection dimensions are derived here, not assumed. The ambient
module and the division ring may have arbitrary dimension. -/
theorem submodule_bot_or_top_of_subspace_similarities
    (p : X → ℝ) (N : Submodule 𝕜 X) (hN : ∀ x, x ∈ N ↔ p x = 0)
    (n : ℕ) (hn : 1 ≤ n) (hdim : (n : Cardinal) < Module.rank 𝕜 X)
    (hsim : ∀ E F : Submodule 𝕜 X,
      Module.finrank 𝕜 E = n → Module.finrank 𝕜 F = n →
        ∃ T : E ≃ₗ[𝕜] F, ∃ c : ℝ, 0 < c ∧
          ∀ x : E, p (T x : X) = c * p (x : X)) :
    N = ⊥ ∨ N = ⊤ := by
  apply submodule_bot_or_top_of_uniform_intersection_finrank N n hn hdim
  intro E F hE hF
  obtain ⟨T, c, hc, hT⟩ := hsim E F hE hF
  exact similarity_kernel_finrank_eq p N hN E F T c hc hT

/-- A function with a scalar-submodule zero kernel, and mutually similar
fixed-dimensional sections, is either identically zero or definite. This is
the function-level consequence used for seminorms in Theorem D. -/
theorem zero_or_definite_of_subspace_similarities
    (p : X → ℝ) (N : Submodule 𝕜 X) (hN : ∀ x, x ∈ N ↔ p x = 0)
    (n : ℕ) (hn : 1 ≤ n) (hdim : (n : Cardinal) < Module.rank 𝕜 X)
    (hsim : ∀ E F : Submodule 𝕜 X,
      Module.finrank 𝕜 E = n → Module.finrank 𝕜 F = n →
        ∃ T : E ≃ₗ[𝕜] F, ∃ c : ℝ, 0 < c ∧
          ∀ x : E, p (T x : X) = c * p (x : X)) :
    (∀ x, p x = 0) ∨ (∀ x, p x = 0 ↔ x = 0) := by
  rcases submodule_bot_or_top_of_subspace_similarities p N hN n hn hdim hsim with
    hbot | htop
  · right
    intro x
    rw [← hN x, hbot]
    rfl
  · left
    intro x
    apply (hN x).mp
    rw [htop]
    trivial

end BanachIsometric
