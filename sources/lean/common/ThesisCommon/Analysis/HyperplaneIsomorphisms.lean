import ThesisCommon.Analysis.QuasiReflexiveDefinitions

/-! Actual hyperplane isomorphisms for Appendix B.1. The maps are projections
along a common transverse vector, exactly as in the manuscript's proof.
-/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A closed codimension-one subspace is the kernel of a nonzero bounded
functional, obtained from its actual one-dimensional quotient. -/
theorem IsClosedHyperplane.exists_functional {H : Submodule 𝕜 X}
    (hH : IsClosedHyperplane 𝕜 X H) :
    ∃ f : X →L[𝕜] 𝕜, f ≠ 0 ∧ LinearMap.ker f.toLinearMap = H := by
  letI : IsClosed (H : Set X) := hH.1
  letI : FiniteDimensional 𝕜 (X ⧸ H) := FiniteDimensional.of_rank_eq_one hH.2
  let e : (X ⧸ H) ≃L[𝕜] 𝕜 := ContinuousLinearEquiv.ofFinrankEq (by
    rw [Module.finrank_self]
    exact Module.rank_eq_one_iff_finrank_eq_one.mp hH.2)
  let q : X →L[𝕜] (X ⧸ H) := ⟨H.mkQ, continuous_quot_mk⟩
  let f : X →L[𝕜] 𝕜 := e.toContinuousLinearMap.comp q
  refine ⟨f, ?_, ?_⟩
  · intro hf
    obtain ⟨y, hy⟩ := e.surjective 1
    obtain ⟨x, hx⟩ := H.mkQ_surjective y
    have hh : f x = 1 := by
      change e (H.mkQ x) = 1
      rw [hx, hy]
    rw [hf] at hh
    simp at hh
  · ext x
    change e (H.mkQ x) = 0 ↔ x ∈ H
    rw [e.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero H

/-- Two nonzero scalar functionals admit a common transverse vector. -/
theorem exists_common_transverse (f g : X →L[𝕜] 𝕜) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ u : X, f u ≠ 0 ∧ g u ≠ 0 := by
  classical
  have hex (h : X →L[𝕜] 𝕜) (hh : h ≠ 0) : ∃ x, h x ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hh (ContinuousLinearMap.ext hn)
  obtain ⟨u, hu⟩ := hex f hf
  by_cases hgu : g u = 0
  · obtain ⟨v, hv⟩ := hex g hg
    by_cases hfv : f v = 0
    · exact ⟨u + v, by simpa [hfv] using hu, by simpa [hgu] using hv⟩
    · exact ⟨v, hfv, hv⟩
  · exact ⟨u, hu, hgu⟩

/-- Projection along u onto the kernel of f, when f(u) is nonzero. -/
def scalarKernelProjection (f : X →L[𝕜] 𝕜) (u : X) : X →L[𝕜] X :=
  ContinuousLinearMap.id 𝕜 X - f.smulRight ((f u)⁻¹ • u)

@[simp] theorem scalarKernelProjection_apply (f : X →L[𝕜] 𝕜) (u x : X) :
    scalarKernelProjection f u x = x - f x • ((f u)⁻¹ • u) := rfl

theorem scalarKernelProjection_mem (f : X →L[𝕜] 𝕜) (u : X) (hu : f u ≠ 0) (x : X) :
    f (scalarKernelProjection f u x) = 0 := by
  simp [map_smul, hu]

@[simp] theorem scalarKernelProjection_self (f : X →L[𝕜] 𝕜) (u : X) (hu : f u ≠ 0) :
    scalarKernelProjection f u u = 0 := by
  simp [smul_smul, hu]

theorem scalarKernelProjection_fixed (f : X →L[𝕜] 𝕜) (u x : X) (hx : f x = 0) :
    scalarKernelProjection f u x = x := by simp [hx]

def scalarKernelTransfer (f g : X →L[𝕜] 𝕜) (u : X) (hg : g u ≠ 0) :
    LinearMap.ker f.toLinearMap →L[𝕜] LinearMap.ker g.toLinearMap :=
  ((scalarKernelProjection g u).comp (LinearMap.ker f.toLinearMap).subtypeL).codRestrict
    (LinearMap.ker g.toLinearMap) (fun x => scalarKernelProjection_mem g u hg x)

@[simp] theorem scalarKernelTransfer_apply (f g : X →L[𝕜] 𝕜) (u : X) (hg : g u ≠ 0)
    (x : LinearMap.ker f.toLinearMap) :
    (scalarKernelTransfer f g u hg x : X) = scalarKernelProjection g u x := rfl

theorem scalarKernelTransfer_inverse (f g : X →L[𝕜] 𝕜) (u : X)
    (hf : f u ≠ 0) (hg : g u ≠ 0) (x : LinearMap.ker f.toLinearMap) :
    scalarKernelTransfer g f u hf (scalarKernelTransfer f g u hg x) = x := by
  apply Subtype.ext
  change scalarKernelProjection f u (scalarKernelProjection g u x) = x
  rw [scalarKernelProjection_apply g, map_sub, map_smul, map_smul,
    scalarKernelProjection_self f u hf, smul_zero, smul_zero, sub_zero]
  exact scalarKernelProjection_fixed f u x x.property

/-- The bounded isomorphism between two functional kernels. -/
def scalarKernelEquiv (f g : X →L[𝕜] 𝕜) (u : X)
    (hf : f u ≠ 0) (hg : g u ≠ 0) :
    LinearMap.ker f.toLinearMap ≃L[𝕜] LinearMap.ker g.toLinearMap :=
  ContinuousLinearEquiv.equivOfInverse (scalarKernelTransfer f g u hg)
    (scalarKernelTransfer g f u hf)
    (scalarKernelTransfer_inverse f g u hf hg) (scalarKernelTransfer_inverse g f u hg hf)

/-- All nonzero bounded scalar functionals have isomorphic kernels. -/
theorem nonempty_scalarKernelEquiv (f g : X →L[𝕜] 𝕜) (hf : f ≠ 0) (hg : g ≠ 0) :
    Nonempty (LinearMap.ker f.toLinearMap ≃L[𝕜] LinearMap.ker g.toLinearMap) := by
  obtain ⟨u, hfu, hgu⟩ := exists_common_transverse f g hf hg
  exact ⟨scalarKernelEquiv f g u hfu hgu⟩

end ThesisCommon
