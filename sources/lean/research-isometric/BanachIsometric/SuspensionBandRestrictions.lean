import BanachIsometric.SuspensionBand

/-! Exact band action determines the actual restrictions of the suspension
on both closed hemispheres. This permits use of the same degree-controlled
map in the concrete pullback clutching construction. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def coneNorthHeight (t : unitInterval) : Icc (-1 : ℝ) 1 :=
  ⟨Real.sqrt (1 - (t : ℝ) ^ 2), by
    constructor
    · linarith [Real.sqrt_nonneg (1 - (t : ℝ) ^ 2)]
    · have h := Real.sq_sqrt (unitInterval_one_sub_sq_nonneg t)
      nlinarith [Real.sqrt_nonneg (1 - (t : ℝ) ^ 2), sq_nonneg (t : ℝ)]⟩

def coneSouthHeight (t : unitInterval) : Icc (-1 : ℝ) 1 :=
  ⟨-(coneNorthHeight t : ℝ), by
    constructor <;> linarith [(coneNorthHeight t).property.1, (coneNorthHeight t).property.2]⟩

theorem equatorBand_coneNorthHeight (v : sphere (0 : V) 1) (t : unitInterval)
    (z : EquatorSphere v) : equatorBand v (coneNorthHeight t, z) = (hemisphereCone v (t, z)).val := by
  apply Subtype.ext
  change Real.sqrt (1 - (t : ℝ) ^ 2) • v.val +
      Real.sqrt (1 - Real.sqrt (1 - (t : ℝ) ^ 2) ^ 2) • z.val.val =
    Real.sqrt (1 - (t : ℝ) ^ 2) • v.val + (t : ℝ) • z.val.val
  rw [Real.sq_sqrt (unitInterval_one_sub_sq_nonneg t),
    show 1 - (1 - (t : ℝ) ^ 2) = (t : ℝ) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg t.property.1]

theorem equatorBand_coneSouthHeight (v : sphere (0 : V) 1) (t : unitInterval)
    (z : EquatorSphere v) : equatorBand v (coneSouthHeight t, z) =
      (hemisphereCone (-v) (t, equatorOppositePole v z)).val := by
  apply Subtype.ext
  change (-Real.sqrt (1 - (t : ℝ) ^ 2)) • v.val +
      Real.sqrt (1 - (-Real.sqrt (1 - (t : ℝ) ^ 2)) ^ 2) • z.val.val =
    Real.sqrt (1 - (t : ℝ) ^ 2) • (-v.val) + (t : ℝ) • z.val.val
  rw [neg_sq, Real.sq_sqrt (unitInterval_one_sub_sq_nonneg t),
    show 1 - (1 - (t : ℝ) ^ 2) = (t : ℝ) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg t.property.1]
  simp only [neg_smul, smul_neg]

theorem suspension_restrictions_of_band_action [FiniteDimensional ℝ V]
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hband : ∀ a : Icc (-1 : ℝ) 1, ∀ z, φ (equatorBand v (a, z)) = equatorBand v (a, f z)) :
    (∀ x : closedHemisphere v, φ x.val = (hemisphereMap v q₀ f x).val) ∧
    (∀ x : closedHemisphere (-v), φ x.val =
      (hemisphereMap (-v) (equatorOppositePole v q₀) (oppositeEquatorMap v f) x).val) := by
  constructor
  · intro x
    obtain ⟨⟨t, z⟩, rfl⟩ := hemisphereCone_surjective v q₀ x
    rw [← equatorBand_coneNorthHeight, hband, hemisphereMap_cone, ← equatorBand_coneNorthHeight]
  · intro x
    let e := equatorOppositePole v
    obtain ⟨⟨t, w⟩, rfl⟩ := hemisphereCone_surjective (-v) (e q₀) x
    let z := e.symm w
    have he : e z = w := e.apply_symm_apply w
    have hef : oppositeEquatorMap v f w = e (f z) := rfl
    rw [← he, ← equatorBand_coneSouthHeight, hband, hemisphereMap_cone]
    rw [he, hef, ← equatorBand_coneSouthHeight]

end BanachIsometric
