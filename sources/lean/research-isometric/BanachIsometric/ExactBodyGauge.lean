import BanachIsometric.ExactFamilyTopology

/-!
# Exact body images give exact functional identities

The bundle is defined by equality of bodies, whereas the signed integral
argument uses equality of their homogeneous gauges. This bridge proves that
these statements are equivalent for actual definite positively homogeneous
functions, without convexity, symmetry, continuity, or a norm triangle law.
-/

namespace BanachIsometric

open Set
open scoped NNReal

section Gauges

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem positiveHomogeneous_eq_of_unit_sublevel_eq {p q : E → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) (hq : IsDefinitePositiveHomogeneous q)
    (hsub : {x | p x ≤ 1} = {x | q x ≤ 1}) : p = q := by
  have hle {p q : E → ℝ} (hp : IsDefinitePositiveHomogeneous p)
      (hq : IsDefinitePositiveHomogeneous q)
      (hsub : {x | p x ≤ 1} ⊆ {x | q x ≤ 1}) (x : E) : q x ≤ p x := by
    by_cases hx : x = 0
    · simp [hx, (hp.eq_zero_iff 0).mpr rfl, (hq.eq_zero_iff 0).mpr rfl]
    have hpx := hp.pos hx
    have hn : p ((p x)⁻¹ • x) ≤ 1 := by
      rw [hp.smul_nonneg _ (inv_nonneg.mpr hpx.le), inv_mul_cancel₀ hpx.ne']
    have hb := hsub hn
    change q ((p x)⁻¹ • x) ≤ 1 at hb
    rw [hq.smul_nonneg _ (inv_nonneg.mpr hpx.le), ← div_eq_inv_mul] at hb
    exact (div_le_one hpx).mp hb
  funext x
  exact le_antisymm (hle hq hp (subset_of_eq hsub.symm) x) (hle hp hq (subset_of_eq hsub) x)

theorem gauge_eq_of_exact_body_image {p : E → ℝ} {g : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (A : E →ₗ[ℝ] V) (hA : Function.Injective A)
    (hbody : A '' {x | p x ≤ 1} = {v | g v ≤ 1} ∩ Set.range A) :
    ∀ x, g (A x) = p x := by
  have hq : IsDefinitePositiveHomogeneous (fun x => g (A x)) :=
    { nonneg := fun x => hg.nonneg (A x)
      eq_zero_iff := fun x => (hg.eq_zero_iff (A x)).trans (by
        constructor
        · intro hx
          exact hA (hx.trans (map_zero A).symm)
        · rintro rfl
          exact map_zero A)
      smul_nonneg := fun t ht x => by rw [map_smul, hg.smul_nonneg _ ht] }
  have hsub : {x | p x ≤ 1} = {x | g (A x) ≤ 1} := by
    ext x
    constructor
    · intro hx
      have hh : A x ∈ A '' {x | p x ≤ 1} := ⟨x, hx, rfl⟩
      rw [hbody] at hh
      exact hh.1
    · intro hx
      have hh : A x ∈ A '' {x | p x ≤ 1} := by
        rw [hbody]
        exact ⟨hx, ⟨x, rfl⟩⟩
      obtain ⟨z, hz, hzx⟩ := hh
      rwa [hA hzx] at hz
  exact fun x => (congrFun (positiveHomogeneous_eq_of_unit_sublevel_eq hp hq hsub) x).symm

end Gauges

section Family

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Converting actual global exact body maps into the precise geometric data
used by the cone calculation. The global maps remain explicit input here;
their construction from the bundle is a separate theorem. -/
noncomputable def exactTangentialFamilyOfBodyMaps {p : E → ℝ} {g : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) (hg : IsDefinitePositiveHomogeneous g)
    (normal : C(Metric.sphere (0 : V) 1, Metric.sphere (0 : V) 1))
    (maps : Metric.sphere (0 : V) 1 → E →L[ℝ] V)
    (hLip : ∃ L : ℝ≥0, LipschitzWith L maps)
    (hInjective : ∀ z, Function.Injective (maps z))
    (hTangent : ∀ z y, inner ℝ (maps z y) (normal z).val = 0)
    (hbody : ∀ z, maps z '' {x | p x ≤ 1} = {v | g v ≤ 1} ∩ Set.range (maps z)) :
    ExactTangentialFamily E V g p where
  normal := normal
  maps := maps
  maps_lipschitz := hLip
  tangent := hTangent
  gauge_eq z := gauge_eq_of_exact_body_image hp hg (maps z).toLinearMap (hInjective z) (hbody z)

end Family

end BanachIsometric
