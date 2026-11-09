import BanachIsometric.AffineSubdivisionHomotopy
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! The explicit subdivision and its explicit homotopy remain in the same
convex carrier. These are support theorems about their actual finite chains. -/

noncomputable section
namespace BanachIsometric.SingularPrism

def affineCarrier {E : Type*} (s : Set E) (n : ℕ) : Submodule ℚ (AffineRationalChains E n) :=
  Finsupp.supported ℚ ℚ {v | ∀ i, v i ∈ s}

theorem affineBoundary_carrier {E : Type*} (s : Set E) (n : ℕ) :
    affineCarrier s (n + 1) ≤ (affineCarrier s n).comap (affineBoundary n) := by
  rw [affineCarrier, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  change affineBoundary n (Finsupp.single v 1) ∈ affineCarrier s n
  rw [affineBoundary_single]
  apply Submodule.sum_mem
  intro i _
  exact (affineCarrier s n).toAddSubgroup.zsmul_mem
    (Finsupp.single_mem_supported ℚ 1 (fun j => hv (i.succAbove j))) _

theorem affineCone_carrier {E : Type*} (s : Set E) (b : E) (hb : b ∈ s) (n : ℕ) :
    affineCarrier s n ≤ (affineCarrier s (n + 1)).comap (affineCone b n) := by
  rw [affineCarrier, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  change affineCone b n (Finsupp.single v 1) ∈ affineCarrier s (n + 1)
  rw [affineCone_single]
  apply Finsupp.single_mem_supported ℚ 1
  intro j
  induction j using Fin.cases with
  | zero => exact hb
  | succ j => exact hv j

def simplexBarycenter (n : ℕ) : Simplex n :=
  ⟨fun _ => 1 / (n + 1 : ℝ), (fun _ => by positivity), by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simpa [one_div] using (mul_inv_cancel₀ (show (n + 1 : ℝ) ≠ 0 by positivity))⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineBarycenter_eq_affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    affineBarycenter v = affineSingularSimplex v (simplexBarycenter n) := by
  change (n + 1 : ℝ)⁻¹ • ∑ i, v i = ∑ i, (1 / (n + 1 : ℝ)) • v i
  simp only [one_div, Finset.smul_sum]

theorem affineBarycenter_mem_convex {n : ℕ} {s : Set E} (hs : Convex ℝ s)
    (v : Fin (n + 1) → E) (hv : ∀ i, v i ∈ s) : affineBarycenter v ∈ s := by
  rw [affineBarycenter_eq_affineSingularSimplex]
  exact affineSingularSimplex_mem_convex hs v hv _

theorem affineSubdivision_carrier {s : Set E} (hs : Convex ℝ s) (n : ℕ) :
    affineCarrier s n ≤ (affineCarrier s n).comap (affineSubdivision n) := by
  induction n with
  | zero => exact fun _ hc => hc
  | succ n ih =>
    rw [affineCarrier, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    rw [← Finsupp.supported_eq_span_single]
    change affineSubdivision (n + 1) (Finsupp.single v 1) ∈ affineCarrier s (n + 1)
    rw [affineSubdivision_single]
    apply affineCone_carrier s (affineBarycenter v) (affineBarycenter_mem_convex hs v hv) n
    apply ih
    exact affineBoundary_carrier s n (Finsupp.single_mem_supported ℚ 1 hv)

theorem affineSubdivisionHomotopy_carrier {s : Set E} (hs : Convex ℝ s) (n : ℕ) :
    affineCarrier s n ≤ (affineCarrier s (n + 1)).comap (affineSubdivisionHomotopy n) := by
  induction n with
  | zero => exact fun _ _ => (affineCarrier s 1).zero_mem
  | succ n ih =>
    rw [affineCarrier, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    change affineSubdivisionHomotopy (n + 1) (Finsupp.single v 1) ∈ affineCarrier s (n + 2)
    rw [affineSubdivisionHomotopy_single]
    apply affineCone_carrier s (affineBarycenter v) (affineBarycenter_mem_convex hs v hv) (n + 1)
    have hv' : Finsupp.single v 1 ∈ affineCarrier s (n + 1) :=
      Finsupp.single_mem_supported ℚ 1 hv
    exact (affineCarrier s (n + 1)).sub_mem
      ((affineCarrier s (n + 1)).sub_mem hv' (affineSubdivision_carrier hs (n + 1) hv'))
      (ih (affineBoundary_carrier s n hv'))

end BanachIsometric.SingularPrism
