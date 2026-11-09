import BanachIsometric.ExactSectionCanonicalHomologicalLift
import BanachIsometric.CanonicalHemisphereLipschitz
import BanachIsometric.ExactSectionAmbientLipschitzRetract
import BanachIsometric.LipschitzEmbeddedRetraction
import BanachIsometric.LipschitzChainTransport
import BanachIsometric.SphereLipschitzNeighborhoodRetraction

/-! The actual projected homology equality can be witnessed by a Lipschitz
cycle upstairs and a Lipschitz boundary filling on the original sphere. -/

noncomputable section
namespace BanachIsometric.ExactSectionPrincipalData
open Set Metric MeasureTheory SphereGenerator SingularPrism
open scoped Topology NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m : ℕ} {p : F → ℝ} {H : sphere (0 : F) 1 → Submodule ℝ F} {a₀ : sphere (0 : F) 1}

omit [FiniteDimensional ℝ F] in
theorem homologicalProjection_lipschitz (D : ExactSectionPrincipalData m p H a₀) :
    LipschitzWith 1 D.homologicalProjection := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  exact LipschitzWith.prod_fst.dist_le_mul a.val b.val

theorem exists_lipschitz_homological_lift_of_class
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C L : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : LipschitzWith L (fun a => (H a).starProjection))
    (n : ℕ) (base : rawCycles (sphere (0 : F) 1) n)
    (hBase : base.val ∈ rawLipschitzCarrier (sphere (0 : F) 1) (n + 1))
    (c : rawCycles (ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H) n)
    (hc : rawHomologyMap D.homologicalProjection n (Submodule.Quotient.mk c) = Submodule.Quotient.mk base) :
    ∃ d : rawCycles (ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H) n,
      d.val ∈ rawLipschitzCarrier _ (n + 1) ∧
      ∃ b : RawRationalChains (sphere (0 : F) 1) (n + 2),
        b ∈ rawLipschitzCarrier _ (n + 2) ∧
        rawBoundary (n + 1) b = rawChainMap D.homologicalProjection (n + 1) d.val - base.val := by
  obtain ⟨A, _hA, r, ⟨K, hK⟩, hFix⟩ := D.exists_lipschitz_ambient_neighborhood_retraction μ hp hSphere hProj
  let hi := D.ambientExactSectionInclusion_isometry
  let R := LipschitzNeighborhoodRetraction.of_isometric_embedding hi r hK hFix
  let e := hi.isometryEquivOnRange
  obtain ⟨d, hd, hd0, a, ha⟩ := R.exists_lipschitz_cycle_representative_homeomorph
    e.toHomeomorph e.symm.isometry.lipschitz n c.val c.property
  let d' : RawRationalChains (ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H) (n + 1) := d
  let P := D.homologicalProjection
  rw [rawHomologyMap_mk] at hc
  obtain ⟨w, hw⟩ := (Submodule.Quotient.eq (rawBoundaries (sphere (0 : F) 1) n)).mp hc
  have hw' : rawBoundary (n + 1) w = rawChainMap P (n + 1) c.val - base.val :=
    congrArg (fun x : rawCycles (sphere (0 : F) 1) n => x.val) hw
  have ha' := LinearMap.congr_fun (rawChainMap_boundary P (n + 1)) a
  change rawBoundary (n + 1) (rawChainMap P (n + 2) a) =
    rawChainMap P (n + 1) (rawBoundary (n + 1) a) at ha'
  have hImage : rawBoundary (n + 1) (rawChainMap P (n + 2) a) =
      rawChainMap P (n + 1) c.val - rawChainMap P (n + 1) d' := by
    calc
      _ = rawChainMap P (n + 1) (rawBoundary (n + 1) a) := ha'
      _ = rawChainMap P (n + 1) (c.val - d') := congrArg (rawChainMap P (n + 1)) ha
      _ = _ := map_sub _ _ _
  have hboundary : rawBoundary (n + 1) (w - rawChainMap P (n + 2) a) =
      rawChainMap P (n + 1) d' - base.val := by
    rw [map_sub, hw', hImage]
    abel
  have hSupport : rawChainMap P (n + 1) d' - base.val ∈ rawLipschitzCarrier (sphere (0 : F) 1) (n + 1) :=
    Submodule.sub_mem _ (rawChainMap_preserves_lipschitz P D.homologicalProjection_lipschitz (n + 1) hd) hBase
  obtain ⟨b, hb, hb'⟩ := (sphereLipschitzNeighborhoodRetraction F).exists_lipschitz_boundary_filling
    n _ hSupport _ hboundary
  exact ⟨⟨d', hd0⟩, hd, b, hb, hb'⟩

theorem exists_lipschitz_canonical_homological_lift
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C L : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : LipschitzWith L (fun a => (H a).starProjection))
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hVanishing : ∀ g : C(EquatorSphere v, Subgroup.connectedComponentOfOne D.StructureGroup),
      g ((equatorStandardSphereHomeomorph v (n + 1) hdim).symm (sphereBasepoint (n + 1))) = 1 →
      rawHomologyMap g n (Submodule.Quotient.mk (canonicalEquatorCycle v n hdim)) = 0) :
    ∃ d : rawCycles (ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H) (n + 1),
      d.val ∈ rawLipschitzCarrier _ (n + 2) ∧
      ∃ b : RawRationalChains (sphere (0 : F) 1) (n + 3),
        b ∈ rawLipschitzCarrier _ (n + 3) ∧
        rawBoundary (n + 2) b = rawChainMap D.homologicalProjection (n + 2) d.val -
          (canonicalSuspensionCycle v n hdim).val := by
  obtain ⟨c, hc⟩ := D.exists_canonical_homological_lift_of_zero_clutching_class μ hp hSphere
    hProj.continuous v n hdim hVanishing
  exact D.exists_lipschitz_homological_lift_of_class μ hp hSphere hProj (n + 1)
    (canonicalSuspensionCycle v n hdim) (canonicalSuspensionCycle_mem_lipschitz v n hdim) c hc

end BanachIsometric.ExactSectionPrincipalData
