import BanachIsometric.ExactSectionTransitionLipschitz

/-!
# The exact-section principal bundle constructed from the paper's geometry

This final interface packages the derived reference section and atlas. Its
methods expose the actual Mathlib bundle core, the homeomorphism to actual
section operators with their inherited topology, and equivariant local
trivializations. Compact parameter spaces have a finite Lipschitz atlas.
-/

namespace BanachIsometric

open Set MeasureTheory
open scoped Topology NNReal

noncomputable section

variable {P F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Constructed data for the actual principal body-automorphism bundle.
The model is a genuine fixed section in Euclidean coordinates. -/
structure ExactSectionPrincipalData (m : ℕ) (p : F → ℝ)
    (H : P → Submodule ℝ F) (a₀ : P) where
  reference : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] F
  range_reference : LinearMap.range reference.toLinearMap = H a₀
  atlas : ExactSectionAtlas (pulledBackGaugeBody p reference) {y : F | p y ≤ 1} H

namespace ExactSectionPrincipalData

variable {m : ℕ} {p : F → ℝ} {H : P → Submodule ℝ F} {a₀ : P}
    (D : ExactSectionPrincipalData m p H a₀)

abbrev ModelBody : Set (EuclideanSpace ℝ (Fin m)) := pulledBackGaugeBody p D.reference

abbrev StructureGroup := bodyAutomorphismGroup D.ModelBody

def core : FiberBundleCore P P D.StructureGroup := D.atlas.fiberBundleCore

def totalSpaceHomeomorph : D.core.TotalSpace ≃ₜ
    ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H := D.atlas.actualHomeomorph

def trivialization (i : P) : Trivialization D.StructureGroup
    (fun t : ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H => t.val.1) :=
  D.atlas.actualTrivialization i

theorem trivialization_covers (a : P) : a ∈ (D.trivialization a).baseSet := D.atlas.mem_baseSet a

theorem trivialization_equivariant (i : P)
    (t : ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H)
    (hi : t.val.1 ∈ (D.trivialization i).baseSet) (g : D.StructureGroup) :
    (D.trivialization i (exactSectionRight t g)).2 = (D.trivialization i t).2 * g :=
  D.atlas.actualTrivialization_right_equivariant i t hi g

theorem finite_lipschitz_atlas [CompactSpace P] :
    ∃ I : Finset P, ∃ L : ℝ≥0,
      (∀ a : P, ∃ i ∈ I, a ∈ (D.trivialization i).baseSet) ∧
      (∀ i ∈ I, LipschitzOnWith L (D.atlas.forward i) (D.atlas.baseSet i) ∧
        LipschitzOnWith L (D.atlas.inverse i) (D.atlas.baseSet i)) ∧
      ∀ i ∈ I, ∀ j ∈ I, ∃ C : ℝ≥0, LipschitzOnWith C
        (fun a => ((D.atlas.transition i j a).val : EuclideanSpace ℝ (Fin m) →L[ℝ]
          EuclideanSpace ℝ (Fin m))) (D.atlas.baseSet i ∩ D.atlas.baseSet j) :=
  D.atlas.exists_finite_lipschitz_principal_atlas

end ExactSectionPrincipalData

variable [FiniteDimensional ℝ F]

/-- The actual principal exact-section bundle follows from the original
definite homogeneous gauge, its sphere regularity, the prescribed projections
and genuine real-linear equivalences of sections. Local exact maps, torsor
charts, covariance normalizers and moment regularity are all derived. -/
theorem nonempty_exactSectionPrincipalData {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    {p : F → ℝ} (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (H : P → Submodule ℝ F) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun a => (H a).starProjection))
    (hrank : ∀ a, Module.finrank ℝ (H a) = Module.finrank ℝ (EuclideanSpace ℝ (Fin m)))
    (a₀ : P) (hequiv : ∀ a, RealSectionEquivalent p (H a₀) (H a)) :
    Nonempty (ExactSectionPrincipalData m p H a₀) := by
  obtain ⟨R, hR, ⟨Z⟩⟩ := exists_exact_section_atlas μ hp hC H hLip hrank a₀ hequiv
  exact ⟨⟨R, hR, Z⟩⟩

end
end BanachIsometric
