import BanachIsometric.CompactOrbit
import BanachIsometric.LocalOrbitSlice

/-!
# Assembling a local Lipschitz orbit section

Compactness supplies small representatives. An immersed exponential patch and
local factorisation along its stabiliser then supply a Lipschitz section. The
factorisation and injective-derivative premises below remain explicit until
they are instantiated for the actual moment representation.
-/

namespace BanachIsometric

open Filter Set
open scoped Topology NNReal

variable {G E W : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [MulAction G W] [ContinuousSMul G W]

/-- Quantitative slice assembly. The hypotheses describe an actual local
factorisation of small group elements, and the derivative of the actual patch
orbit map. No quotient-manifold or orbit-inverse assertion is a hypothesis. -/
theorem exists_lipschitz_orbit_section_of_local_factorization
    (v : W) (e : E → G) (he0 : e 0 = 1)
    (c : G → E) (hc0 : c 1 = 0) (hc : ContinuousAt c 1)
    (hcover : ∀ᶠ R : G in 𝓝 1, e (c R) • v = R • v)
    (D : E →L[ℝ] W) (hf : HasStrictFDerivAt (fun x => e x • v) D 0)
    (hD : Function.Injective D)
    (heLip : ∃ T ∈ 𝓝 (0 : E), ∃ L : ℝ≥0, LipschitzOnWith L e T) :
    ∃ s : W → G, ∃ N ∈ 𝓝 v, ∃ L : ℝ≥0,
      s v = 1 ∧ LipschitzOnWith L s N ∧
      ∀ y ∈ N, (∃ R : G, R • v = y) → s y • v = y := by
  have hf0 : e 0 • v = v := by rw [he0, one_smul]
  obtain ⟨g, U, hU, W₀, hW₀, C, hg0, hgLip, hgInv, _⟩ :=
    exists_lipschitz_inverse_of_injective_strictDerivative
      (fun x => e x • v) D hf hD
  rw [hf0] at hW₀ hg0
  have hgCont : ContinuousAt g v := hgLip.continuousOn.continuousAt hW₀
  obtain ⟨T, hT, L, hL⟩ := heLip
  have hsmall : ∀ᶠ R : G in 𝓝 1, c R ∈ U := by
    apply hc.tendsto.eventually
    simpa only [hc0] using hU
  obtain ⟨V, hVsubset, hVopen, hV1⟩ := mem_nhds_iff.mp (hsmall.and hcover)
  obtain ⟨N₀, hN₀open, hvN₀, hrep⟩ := compactOrbit_local_representatives v V hVopen hV1
  have hpre : g ⁻¹' T ∈ 𝓝 v := hgCont.tendsto.eventually (by simpa only [hg0] using hT)
  let N : Set W := N₀ ∩ W₀ ∩ g ⁻¹' T
  have hN : N ∈ 𝓝 v := inter_mem (inter_mem (hN₀open.mem_nhds hvN₀) hW₀) hpre
  refine ⟨fun y => e (g y), N, hN, L * C, ?_, ?_, ?_⟩
  · change e (g v) = 1
    rw [hg0, he0]
  · apply hL.comp (hgLip.mono (fun _ h => h.1.2))
    intro y hy
    exact hy.2
  · intro y hy hOrbit
    obtain ⟨R, hRV, hRy⟩ := hrep y hy.1.1 hOrbit
    have hRU : c R ∈ U := (hVsubset hRV).1
    have hRcover : e (c R) • v = R • v := (hVsubset hRV).2
    have hgy : g y = c R := by
      rw [← hRy, ← hRcover]
      exact hgInv (c R) hRU
    change e (g y) • v = y
    rw [hgy, hRcover, hRy]

end BanachIsometric
