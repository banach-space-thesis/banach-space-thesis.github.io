import BanachIsometric.CubicalSphereInverse
import BanachIsometric.GenLoopRepetitionLocalLipschitz

/-! The actual sphere repetition is locally Lipschitz near every fiber over
a non-pole target. The inverse chart and the actual cubical branch formulas
are used, so no global Lipschitz assertion is made for the raw repetition. -/

noncomputable section
namespace BanachIsometric.SphereGenerator
open Set Metric
open scoped Topology Topology.Homotopy NNReal unitInterval

theorem sphereRepetition_eq_repeat_at_inverse (n d : ℕ) (w : Sph (n + 1))
    (hw : w ≠ sphereBasepoint (n + 1)) :
    sphereRepetition n d w =
      repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d (sphereCubeInverse (n + 1) w) := by
  calc
    _ = sphereRepetition n d (cubeToSphere (n + 1) (sphereCubeInverse (n + 1) w)) :=
      congrArg (sphereRepetition n d) (cubeToSphere_sphereCubeInverse n w hw).symm
    _ = _ := congrArg (fun f : C((Fin (n + 1) → unitInterval), Sph (n + 1)) =>
      f (sphereCubeInverse (n + 1) w)) (sphereRepetition_comp_cubeToSphere n d)

theorem exists_lipschitzOn_sphereRepetition_nhds_of_nonpole_fiber
    (n d : ℕ) (target w : Sph (n + 1)) (htarget : target ≠ sphereBasepoint (n + 1))
    (hw : sphereRepetition n d w = target) :
    ∃ L : ℝ≥0, ∃ U ∈ 𝓝 w, LipschitzOnWith L (sphereRepetition n d) U := by
  have hwPole : w ≠ sphereBasepoint (n + 1) := by
    intro he
    subst w
    exact htarget (hw.symm.trans (sphereRepetition_basepoint n d))
  let u := sphereCubeInverse (n + 1) w
  have hu : repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d u = target :=
    (sphereRepetition_eq_repeat_at_inverse n d w hwPole).symm.trans hw
  have hγ : ∀ v : Fin (n + 1) → unitInterval, sphereGenerator (n + 1) v = target →
      ∃ L : ℝ≥0, ∃ U ∈ 𝓝 v, LipschitzOnWith L (sphereGenerator (n + 1)) U := by
    intro v hv
    have hvInterior : v ∉ Cube.boundary (Fin (n + 1)) := by
      intro hb
      exact htarget (hv.symm.trans (cubeToSphere_boundary _ _ hb))
    exact exists_lipschitzOn_cubeToSphere_nhds _ v hvInterior
  obtain ⟨LR, UR, hUR, hR⟩ := exists_lipschitzOn_repeatGenLoop_nhds_of_nonbase
    (0 : Fin (n + 1)) (sphereGenerator (n + 1)) htarget hγ d u hu
  obtain ⟨LI, UI, hUI, hI⟩ := exists_lipschitzOn_sphereCubeInverse_nhds n w hwPole
  have hIc : ContinuousAt (sphereCubeInverse (n + 1)) w := hI.continuousOn.continuousAt hUI
  let U := (UI ∩ (sphereCubeInverse (n + 1) ⁻¹' UR)) ∩
    {v : Sph (n + 1) | v ≠ sphereBasepoint (n + 1)}
  have hU : U ∈ 𝓝 w := Filter.inter_mem
    (Filter.inter_mem hUI (hIc.preimage_mem_nhds hUR))
    (isOpen_ne.mem_nhds hwPole)
  have hcomp : LipschitzOnWith (LR * LI)
      (fun v => repeatGenLoop (0 : Fin (n + 1)) (sphereGenerator (n + 1)) d
        (sphereCubeInverse (n + 1) v)) U :=
    hR.comp (hI.mono (fun _ hv => hv.1.1)) (fun _ hv => hv.1.2)
  refine ⟨LR * LI, U, hU, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro a ha b hb
  rw [sphereRepetition_eq_repeat_at_inverse n d a ha.2,
    sphereRepetition_eq_repeat_at_inverse n d b hb.2]
  exact hcomp.dist_le_mul a ha b hb

end BanachIsometric.SphereGenerator
