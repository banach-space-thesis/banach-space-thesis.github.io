import BanachIsometric.BodyIdentityAllSingularHomologyRetract
import BanachIsometric.FiniteNerveSingularHomologyBound

/-! The actual identity body group has finite-dimensional rational singular
homology in every degree, with a uniform degree bound. The bound comes from
its actual finite-polyhedron domination and the vertex-star good cover. -/

noncomputable section
namespace BanachIsometric

open Set MeasureTheory SingularPrism

theorem bodyIdentityComponent_rawDegreeHomologyBounded {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    ∃ n : ℕ, RawDegreeHomologyBounded
      (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) n := by
  obtain ⟨n, K, f, g, hz, hp⟩ :=
    bodyIdentityComponent_actual_singular_homology_retract_all_degrees μ S hS hreg h0
  have hi (q : ℕ) : Function.Injective (rawDegreeHomologyMap f q) := by
    apply Function.LeftInverse.injective (g := rawDegreeHomologyMap g q)
    intro x
    cases q with
    | zero => exact LinearMap.congr_fun hz x
    | succ q => exact LinearMap.congr_fun (hp q) x
  have hK : RawDegreeHomologyBounded K.space n := by
    simpa only [Fintype.card_fin] using K.rawDegreeHomologyBounded_vertexOpenStar
  refine ⟨n, ?_, ?_⟩
  · intro q
    letI := hK.1 q
    exact FiniteDimensional.of_injective (rawDegreeHomologyMap f q) (hi q)
  · intro q hq
    letI := hK.2 q hq
    exact (hi q).subsingleton

end BanachIsometric
