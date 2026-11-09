import BanachIsometric.ComplexPolarization
import BanachIsometric.FiniteConfigurations

/-!
# Gluing local complex Hermitian forms without an ambient norm

This completes the algebraic local-to-global step of Theorem A, conditional on
the local geometric conclusion. The same polarization formula identifies all
local forms on their overlaps. Three-vector containment then gives additivity.
No triangle inequality or norm on the ambient space is assumed or constructed.

This is an alternative to the paper's global algebraic Jordan--von Neumann and
Cauchy--Schwarz argument. The finite-dimensional geometric theorem remains an
explicit premise; it is not inferred by this gluing lemma.
-/

namespace BanachIsometric

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[simp] theorem complexPolar_submodule (p : X → ℝ) (Y : Submodule ℂ X) (x y : Y) :
    complexPolar (fun z : Y => p z.val) x y = complexPolar p x.val y.val := rfl

/-- Each local Hermitian form agrees with the ambient algebraic polarization
formula on all pairs of vectors in its domain. -/
theorem PositiveHermitianForm.form_eq_ambient_complexPolar
    {p : X → ℝ} (Y : Submodule ℂ X) (h : PositiveHermitianForm Y)
    (hp : ∀ y : Y, h.form y y = ((p y.val ^ 2 : ℝ) : ℂ)) (x y : Y) :
    h.form x y = complexPolar p x.val y.val := by
  simpa only [complexPolar_submodule] using h.form_eq_complexPolar hp x y

/-- Local Hermitian squares in every available fixed dimension at least three
glue into a positive-definite Hermitian square on the original algebraic module.
All local existence hypotheses are explicit. The ambient dimension may be
infinite and no completeness or topology is required. -/
theorem hasHermitianSquare_of_local {p : X → ℝ} (m : ℕ) (hm3 : 3 ≤ m)
    (hm : (m : Cardinal) ≤ Module.rank ℂ X)
    (hlocal : ∀ Y : Submodule ℂ X, FiniteDimensional ℂ Y → Module.finrank ℂ Y = m →
      HasHermitianSquare (fun y : Y => p y.val)) : HasHermitianSquare p := by
  have hdiag (x : X) : complexPolar p x x = ((p x ^ 2 : ℝ) : ℂ) := by
    obtain ⟨Y, hx, _, _, hfinite, hdim⟩ :=
      exists_subspace_containing_triple m hm3 hm x 0 0
    obtain ⟨h, hp⟩ := hlocal Y hfinite hdim
    rw [← h.form_eq_ambient_complexPolar Y hp (⟨x, hx⟩ : Y) (⟨x, hx⟩ : Y)]
    exact hp ⟨x, hx⟩
  have hconj (x y : X) : star (complexPolar p x y) = complexPolar p y x := by
    obtain ⟨Y, hx, hy, _, hfinite, hdim⟩ :=
      exists_subspace_containing_triple m hm3 hm x y 0
    obtain ⟨h, hp⟩ := hlocal Y hfinite hdim
    have hform := h.form_eq_ambient_complexPolar Y hp
    simpa only [hform] using h.conj_symm (⟨x, hx⟩ : Y) (⟨y, hy⟩ : Y)
  have hadd (x y z : X) :
      complexPolar p x (y + z) = complexPolar p x y + complexPolar p x z := by
    obtain ⟨Y, hx, hy, hz, hfinite, hdim⟩ :=
      exists_subspace_containing_triple m hm3 hm x y z
    obtain ⟨h, hp⟩ := hlocal Y hfinite hdim
    have hform := h.form_eq_ambient_complexPolar Y hp
    simpa only [hform] using
      h.add_right (⟨x, hx⟩ : Y) (⟨y, hy⟩ : Y) (⟨z, hz⟩ : Y)
  have hsmul (x y : X) (a : ℂ) :
      complexPolar p x (a • y) = a * complexPolar p x y := by
    obtain ⟨Y, hx, hy, _, hfinite, hdim⟩ :=
      exists_subspace_containing_triple m hm3 hm x y 0
    obtain ⟨h, hp⟩ := hlocal Y hfinite hdim
    have hform := h.form_eq_ambient_complexPolar Y hp
    simpa only [hform] using h.smul_right (⟨x, hx⟩ : Y) (⟨y, hy⟩ : Y) a
  have hpos (x : X) (hx0 : x ≠ 0) : 0 < (complexPolar p x x).re := by
    obtain ⟨Y, hx, _, _, hfinite, hdim⟩ :=
      exists_subspace_containing_triple m hm3 hm x 0 0
    obtain ⟨h, hp⟩ := hlocal Y hfinite hdim
    have hform := h.form_eq_ambient_complexPolar Y hp
    have hnonzero : (⟨x, hx⟩ : Y) ≠ 0 := fun heq => hx0 (congrArg Subtype.val heq)
    simpa only [hform] using h.self_pos (⟨x, hx⟩ : Y) hnonzero
  refine ⟨{
    form := complexPolar p
    conj_symm := hconj
    add_right := hadd
    smul_right := hsmul
    self_im := ?_
    self_nonneg := ?_
    self_pos := hpos
  }, hdiag⟩
  · intro x
    rw [hdiag]
    rfl
  · intro x
    rw [hdiag]
    exact sq_nonneg (p x)

end BanachIsometric
