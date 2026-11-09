import BanachIsometric.ConnectedHemisphereClutching
import BanachIsometric.EquatorIsometricCoordinates
import BanachIsometric.SphericalGraphHomology
import BanachIsometric.HemisphericalBaseCycle

/-! The actual exact-section bundle lifts the hemispherical cycle when its
based clutching map kills the equator class in rational singular homology.
The lift projects to exactly the prescribed sphere homology class. -/

noncomputable section
namespace BanachIsometric.ExactSectionPrincipalData
open Set Metric MeasureTheory SphereGenerator SingularPrism
open scoped Topology NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m : ℕ} {p : F → ℝ} {H : sphere (0 : F) 1 → Submodule ℝ F} {a₀ : sphere (0 : F) 1}

omit [FiniteDimensional ℝ F] in
def homologicalProjection (D : ExactSectionPrincipalData m p H a₀) :
    C(ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H, sphere (0 : F) 1) :=
  ⟨fun t => t.val.1, continuous_fst.comp continuous_subtype_val⟩

theorem exists_homological_lift_of_zero_clutching_class
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : Continuous (fun a => (H a).starProjection))
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (z : rawCycles (EquatorSphere v) n)
    (bN : RawRationalChains (closedHemisphere v) (n + 2))
    (bS : RawRationalChains (closedHemisphere (-v)) (n + 2))
    (hbN : rawBoundary (n + 1) bN = rawChainMap (equatorNorth v) (n + 1) z.val)
    (hbS : rawBoundary (n + 1) bS = rawChainMap (equatorSouth v) (n + 1) z.val)
    (hVanishing : ∀ g : C(EquatorSphere v, Subgroup.connectedComponentOfOne D.StructureGroup),
      g ((equatorStandardSphereHomeomorph v (n + 1) hdim).symm (sphereBasepoint (n + 1))) = 1 →
      rawHomologyMap g n (Submodule.Quotient.mk z) = 0) :
    ∃ c : rawCycles (ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H) (n + 1),
      rawHomologyMap D.homologicalProjection (n + 1) (Submodule.Quotient.mk c) =
        Submodule.Quotient.mk (hemisphericalBaseCycle v n z bN bS hbN hbS) := by
  let L := equatorStandardLinearIsometry v (n + 1) hdim
  have horth : Module.finrank ℝ (ℝ ∙ v.val)ᗮ = n + 2 := by
    simpa only [finrank_euclideanSpace_fin] using L.toLinearEquiv.finrank_eq
  have hrank : 1 < Module.rank ℝ (ℝ ∙ v.val)ᗮ := by
    rw [← Module.finrank_eq_rank, horth]
    exact_mod_cast (by omega : 1 < n + 2)
  let eQ := equatorStandardSphereHomeomorph v (n + 1) hdim
  obtain ⟨north, south, g, hnorth, hsouth, hg, hglue⟩ :=
    D.exists_connected_hemisphere_clutching μ hp hSphere hProj v hrank
      (eQ.symm (sphereBasepoint (n + 1)))
  let T := ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H
  let G₀ := Subgroup.connectedComponentOfOne D.StructureGroup
  let liftN : C(closedHemisphere v, T) :=
    ⟨fun x => ⟨(x.val, north x), hnorth x⟩,
      (continuous_subtype_val.prodMk north.continuous).subtype_mk _⟩
  let liftS : C(closedHemisphere (-v), T) :=
    ⟨fun x => ⟨(x.val, south x), hsouth x⟩,
      (continuous_subtype_val.prodMk south.continuous).subtype_mk _⟩
  let γ : C(EquatorSphere v × G₀, T) :=
    ⟨fun x => exactSectionRight (liftN (equatorNorth v x.1)) x.2.val,
      continuous_exactSectionRight.comp
        (((liftN.continuous.comp (equatorNorth v).continuous).comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd))⟩
  have hN : liftN.comp (equatorNorth v) = γ.comp (rawGraphMap (ContinuousMap.const (EquatorSphere v) (1 : G₀))) := by
    apply ContinuousMap.ext
    intro x
    exact (exactSectionRight_one (liftN (equatorNorth v x))).symm
  have hS : liftS.comp (equatorSouth v) = γ.comp (rawGraphMap g) := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hglue x
  have hgraph := rawHomologyMap_graph_eq_constant_of_sphere_class_zero n eQ g (1 : G₀) hg n z
    (hVanishing g hg)
  obtain ⟨c, correction, hc⟩ := exists_raw_homological_clutching_lift
    (equatorNorth v) (equatorSouth v) (closedHemisphereInclusion v) (closedHemisphereInclusion (-v))
    liftN liftS γ D.homologicalProjection g (1 : G₀) hN hS rfl rfl rfl n z bN bS hbN hbS hgraph
  let base := hemisphericalBaseCycle v n z bN bS hbN hbS
  have hCycles : rawCyclesMap D.homologicalProjection (n + 1) c =
      base + rawCyclesMap (equatorInclusion v) (n + 1) correction := by
    apply Subtype.ext
    exact hc
  have hClass : rawHomologyMap D.homologicalProjection (n + 1) (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk base + rawHomologyMap (equatorInclusion v) (n + 1)
        (Submodule.Quotient.mk correction) := by
    rw [rawHomologyMap_mk, rawHomologyMap_mk, ← Submodule.Quotient.mk_add]
    exact congrArg Submodule.Quotient.mk hCycles
  rw [rawHomologyMap_equatorInclusion_eq_zero, LinearMap.zero_apply, add_zero] at hClass
  exact ⟨c, hClass⟩

end BanachIsometric.ExactSectionPrincipalData
