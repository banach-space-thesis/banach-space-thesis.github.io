import BanachIsometric.SignedFacetRayOnSphere
import BanachIsometric.SignedSimplexStrictInterior

/-! Every regular boundary preimage lies on a unique open facet. The fiber
equivalence uses the actual face inclusions and their actual coordinate charts. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric SphereGenerator
open scoped NNReal Topology

def removeSimplexVertex {d : ℕ} (w : Simplex (d + 1)) (i : Fin (d + 2)) (h : w i = 0) : Simplex d :=
  ⟨fun j => w (i.succAbove j), fun j => stdSimplex.zero_le w _, by
    have hs := stdSimplex.sum_eq_one w
    rw [Fin.sum_univ_succAbove _ i, h, zero_add] at hs
    exact hs⟩

theorem face_removeSimplexVertex {d : ℕ} (w : Simplex (d + 1)) (i : Fin (d + 2))
    (h : w i = 0) : face i (removeSimplexVertex w i h) = w := by
  apply Subtype.ext
  rw [signedFace_barycentric]
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · rw [Fin.insertNth_apply_same]
    exact h.symm
  · rw [Fin.insertNth_apply_succAbove]
    rfl

theorem face_injective {d : ℕ} (i : Fin (d + 2)) : Function.Injective (face i) := by
  intro x y h
  apply Subtype.ext
  funext j
  have he := congrArg (fun v : Simplex (d + 1) => v (i.succAbove j)) h
  change (face i x).val (i.succAbove j) = (face i y).val (i.succAbove j) at he
  simpa only [signedFace_barycentric, Fin.insertNth_apply_succAbove] using he

abbrev SignedFacetFiber (n : ℕ) (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2))
    (i : Fin (n + 3)) (y : Fin (n + 1) → ℝ) :=
  {x : signedSimplexDomain (n + 1) // signedFacetFunction n σ i x.val = y}

abbrev SignedBoundaryFiber (n : ℕ) (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2))
    (y : Fin (n + 1) → ℝ) := {w : SimplexBoundary n // σ w.val = y}

def signedFacetToBoundaryFiber (n : ℕ) (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2))
    {L : ℝ≥0} (hσ : LipschitzWith L σ) (y : Fin (n + 1) → ℝ) :
    (Σ i : Fin (n + 3), SignedFacetFiber n σ i y) → SignedBoundaryFiber n σ y := fun a =>
  ⟨boundarySimplexFaceInclusion n a.1 ((signedSimplexCoordinates (n + 1)).symm a.2.val), by
    change σ (face a.1 ((signedSimplexCoordinates (n + 1)).symm a.2.val)) = y
    rw [← signedFacetFunction_eq n σ hσ]
    exact a.2.property⟩

theorem signedFacetToBoundaryFiber_surjective (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) {L : ℝ≥0} (hσ : LipschitzWith L σ)
    (y : Fin (n + 1) → ℝ) : Function.Surjective (signedFacetToBoundaryFiber n σ hσ y) := by
  intro w
  obtain ⟨i, hi⟩ := w.val.property
  let u := removeSimplexVertex w.val.val i hi
  let x := signedSimplexCoordinates (n + 1) u
  have hf : signedFacetFunction n σ i x.val = y := by
    rw [signedFacetFunction_eq n σ hσ, Homeomorph.symm_apply_apply, face_removeSimplexVertex]
    exact w.property
  refine ⟨⟨i, ⟨x, hf⟩⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change face i ((signedSimplexCoordinates (n + 1)).symm x) = w.val.val
  rw [Homeomorph.symm_apply_apply, face_removeSimplexVertex]

theorem signedFacetToBoundaryFiber_injective (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) {L : ℝ≥0} (hσ : LipschitzWith L σ)
    (y : Fin (n + 1) → ℝ)
    (hinter : ∀ i (x : SignedFacetFiber n σ i y), x.val.val ∈ interior (signedSimplexDomain (n + 1))) :
    Function.Injective (signedFacetToBoundaryFiber n σ hσ y) := by
  rintro ⟨i, x⟩ ⟨j, z⟩ he
  let s := signedSimplexCoordinates (n + 1)
  have hfaces : face i (s.symm x.val) = face j (s.symm z.val) :=
    congrArg (fun b : SignedBoundaryFiber n σ y => b.val.val) he
  have hij : i = j := by
    by_contra hne
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hne
    have hz : (face j (s.symm z.val)) i = 0 := by
      have h0 := congrArg (fun b : Simplex (n + 2) => b i) hfaces
      change (face i (s.symm x.val)) i = (face j (s.symm z.val)) i at h0
      rw [simplex_face_missing] at h0
      exact h0.symm
    have hp : 0 < (face j (s.symm z.val)) i := by
      rw [← hk]
      change 0 < (face j (s.symm z.val)).val (j.succAbove k)
      rw [signedFace_barycentric, Fin.insertNth_apply_succAbove]
      exact signedSimplexBarycentric_pos_of_interior (n + 1) (hinter j z) k
    exact hp.ne' hz
  subst j
  have hxz : x = z := Subtype.ext (s.symm.injective (face_injective i hfaces))
  rw [hxz]

def signedFacetBoundaryFiberEquiv (n : ℕ)
    (σ : RawSingularSimplex (Fin (n + 1) → ℝ) (n + 2)) {L : ℝ≥0} (hσ : LipschitzWith L σ)
    (y : Fin (n + 1) → ℝ)
    (hinter : ∀ i (x : SignedFacetFiber n σ i y), x.val.val ∈ interior (signedSimplexDomain (n + 1))) :
    (Σ i : Fin (n + 3), SignedFacetFiber n σ i y) ≃ SignedBoundaryFiber n σ y :=
  Equiv.ofBijective (signedFacetToBoundaryFiber n σ hσ y)
    ⟨signedFacetToBoundaryFiber_injective n σ hσ y hinter,
      signedFacetToBoundaryFiber_surjective n σ hσ y⟩

end BanachIsometric.SingularPrism
