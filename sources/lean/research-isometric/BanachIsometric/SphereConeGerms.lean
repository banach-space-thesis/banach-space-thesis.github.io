import BanachIsometric.SphereConeCount

/-!
# Actual sphere germs give actual cone germs away from zero

Exact equality near a sphere point pulls back through the actual continuous
normalization map. Positive radial multiplication consequently preserves
the germ equality of the two norm cones. No regularity of either sphere
map is needed for this exact statement.
-/

namespace BanachIsometric

open Set Metric Filter NormedSpace
open scoped Topology

theorem coneExtension_eventuallyEq_of_sphere_germ
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {A B : sphere (0 : V) 1 → W} {z : sphere (0 : V) 1}
    (hAB : A =ᶠ[𝓝 z] B) {ρ : ℝ} (hρ : 0 < ρ) :
    coneExtension A =ᶠ[𝓝 (ρ • z.val)] coneExtension B := by
  have hz : ‖z.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using z.property
  have hzne : z.val ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
  have hcenter : ρ • z.val ≠ 0 := smul_ne_zero hρ.ne' hzne
  have hnormalize : NormedSpace.normalize (ρ • z.val) = z.val := by
    rw [normalize_smul_of_pos hρ, normalize_eq_self_of_norm_eq_one hz]
  have hcont : ContinuousAt (fun y : V => NormedSpace.normalize y) (ρ • z.val) :=
    (continuousAt_id.norm.inv₀ (norm_ne_zero_iff.mpr hcenter)).smul continuousAt_id
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hAB
  have hnear : ∀ᶠ y in 𝓝 (ρ • z.val), dist (NormedSpace.normalize y) z.val < ε := by
    have h := hcont.tendsto.eventually (ball_mem_nhds (NormedSpace.normalize (ρ • z.val)) hε)
    simpa only [hnormalize, mem_ball] using h
  have hne : ∀ᶠ y in 𝓝 (ρ • z.val), y ≠ 0 :=
    isOpen_compl_singleton.mem_nhds hcenter
  filter_upwards [hnear, hne] with y hy hyne
  have heq : A (coneDirection y hyne) = B (coneDirection y hyne) := by
    apply hball
    change dist (NormedSpace.normalize y) z.val < ε
    exact hy
  rw [coneExtension_of_ne A y hyne, coneExtension_of_ne B y hyne, heq]

theorem unitSphereCone_eventuallyEq_of_sphere_germ
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : sphere (0 : V) 1 → sphere (0 : V) 1} {z : sphere (0 : V) 1}
    (hfg : f =ᶠ[𝓝 z] g) {ρ : ℝ} (hρ : 0 < ρ) :
    unitSphereCone f =ᶠ[𝓝 (ρ • z.val)] unitSphereCone g :=
  coneExtension_eventuallyEq_of_sphere_germ (hfg.mono (fun _ h => congrArg Subtype.val h)) hρ

end BanachIsometric
