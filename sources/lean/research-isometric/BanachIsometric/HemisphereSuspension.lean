import BanachIsometric.HemisphereConeSurjective
import BanachIsometric.ClosedCoverGluing

/-! Actual suspension of an equator self-map, constructed on the two closed
hemispheres by quotient descent. The result preserves hemispheres and has
the specified equatorial restriction; no sphere map classification is used. -/

noncomputable section
namespace BanachIsometric
open Set Metric Topology
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem hemisphereCone_zero (v : sphere (0 : V) 1) (z : EquatorSphere v) :
    (hemisphereCone v (0, z)).val = v := by
  apply Subtype.ext
  change Real.sqrt (1 - (0 : ℝ) ^ 2) • v.val + (0 : ℝ) • z.val.val = v.val
  norm_num

theorem hemisphereCone_one (v : sphere (0 : V) 1) (z : EquatorSphere v) :
    hemisphereCone v (1, z) = equatorNorth v z := by
  apply Subtype.ext
  apply Subtype.ext
  change Real.sqrt (1 - (1 : ℝ) ^ 2) • v.val + (1 : ℝ) • z.val.val = z.val.val
  norm_num

def equatorOppositePole (v : sphere (0 : V) 1) : EquatorSphere v ≃ₜ EquatorSphere (-v) where
  toFun z := ⟨⟨z.val.val, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (by
    change inner ℝ (-v.val) z.val.val = 0
    rw [inner_neg_left, Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.val.property, neg_zero])⟩,
      by simpa only [Metric.mem_sphere, dist_zero_right] using norm_eq_of_mem_sphere z⟩
  invFun z := ⟨⟨z.val.val, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (by
    have hz := Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.val.property
    change inner ℝ (-v.val) z.val.val = 0 at hz
    rw [inner_neg_left] at hz
    exact neg_eq_zero.mp hz)⟩,
      by simpa only [Metric.mem_sphere, dist_zero_right] using norm_eq_of_mem_sphere z⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

def hemisphereConeMap (v : sphere (0 : V) 1) (f : C(EquatorSphere v, EquatorSphere v)) :
    C(unitInterval × EquatorSphere v, closedHemisphere v) :=
  (hemisphereCone v).comp ⟨fun p => (p.1, f p.2),
    continuous_fst.prodMk (f.continuous.comp continuous_snd)⟩

theorem hemisphereConeMap_factorsThrough (v : sphere (0 : V) 1)
    (f : C(EquatorSphere v, EquatorSphere v)) :
    Function.FactorsThrough (hemisphereConeMap v f) (hemisphereCone v) := by
  rintro ⟨t, z⟩ ⟨u, w⟩ he
  obtain ⟨htu, hzw⟩ := hemisphereCone_fiber v t u z w he
  subst u
  rcases hzw with ht | hzw
  · subst t
    apply Subtype.ext
    exact (hemisphereCone_zero v (f z)).trans (hemisphereCone_zero v (f w)).symm
  · cases hzw
    rfl

def hemisphereMap [FiniteDimensional ℝ V] (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v)) : C(closedHemisphere v, closedHemisphere v) :=
  (isQuotientMap_hemisphereCone v q₀).lift (hemisphereConeMap v f)
    (hemisphereConeMap_factorsThrough v f)

theorem hemisphereMap_cone [FiniteDimensional ℝ V] (v : sphere (0 : V) 1)
    (q₀ : EquatorSphere v) (f : C(EquatorSphere v, EquatorSphere v))
    (t : unitInterval) (z : EquatorSphere v) :
    hemisphereMap v q₀ f (hemisphereCone v (t, z)) = hemisphereCone v (t, f z) :=
  congrArg (fun g : C(unitInterval × EquatorSphere v, closedHemisphere v) => g (t, z))
    ((isQuotientMap_hemisphereCone v q₀).lift_comp (hemisphereConeMap v f)
      (hemisphereConeMap_factorsThrough v f))

theorem hemisphereMap_equator [FiniteDimensional ℝ V] (v : sphere (0 : V) 1)
    (q₀ : EquatorSphere v) (f : C(EquatorSphere v, EquatorSphere v)) (z : EquatorSphere v) :
    hemisphereMap v q₀ f (equatorNorth v z) = equatorNorth v (f z) := by
  rw [← hemisphereCone_one, hemisphereMap_cone, hemisphereCone_one]

theorem exists_suspension [FiniteDimensional ℝ V] (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v)) :
    ∃ φ : C(sphere (0 : V) 1, sphere (0 : V) 1),
      (∀ x : closedHemisphere v, φ x.val = (hemisphereMap v q₀ f x).val) ∧
      (∀ x : closedHemisphere (-v), φ x.val =
        (hemisphereMap (-v) (equatorOppositePole v q₀)
          ((⟨equatorOppositePole v, (equatorOppositePole v).continuous⟩ :
            C(EquatorSphere v, EquatorSphere (-v))).comp
            (f.comp ⟨(equatorOppositePole v).symm, (equatorOppositePole v).symm.continuous⟩)) x).val) ∧
      ∀ z, φ (equatorInclusion v z) = equatorInclusion v (f z) := by
  let e := equatorOppositePole v
  let eC : C(EquatorSphere v, EquatorSphere (-v)) := ⟨e, e.continuous⟩
  let eiC : C(EquatorSphere (-v), EquatorSphere v) := ⟨e.symm, e.symm.continuous⟩
  let fS := eC.comp (f.comp eiC)
  let n : C(closedHemisphere v, sphere (0 : V) 1) :=
    ⟨fun x => (hemisphereMap v q₀ f x).val,
      continuous_subtype_val.comp (hemisphereMap v q₀ f).continuous⟩
  let s : C(closedHemisphere (-v), sphere (0 : V) 1) :=
    ⟨fun x => (hemisphereMap (-v) (e q₀) fS x).val,
      continuous_subtype_val.comp (hemisphereMap (-v) (e q₀) fS).continuous⟩
  have hclosedN : IsClosed (closedHemisphere v) :=
    isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)
  have hclosedS : IsClosed (closedHemisphere (-v)) :=
    isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)
  have hcover : closedHemisphere v ∪ closedHemisphere (-v) = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : 0 ≤ inner ℝ v.val x.val
    · exact Or.inl hx
    · right
      change 0 ≤ inner ℝ (-v.val) x.val
      rw [inner_neg_left]
      linarith
  have hagree : ∀ x (hx : x ∈ closedHemisphere v) (hy : x ∈ closedHemisphere (-v)),
      n ⟨x, hx⟩ = s ⟨x, hy⟩ := by
    intro x hx hy
    have hz : inner ℝ v.val x.val = 0 := by
      change 0 ≤ inner ℝ v.val x.val at hx
      change 0 ≤ inner ℝ (-v.val) x.val at hy
      rw [inner_neg_left] at hy
      linarith
    let z : EquatorSphere v := ⟨⟨x.val,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hz⟩,
      by simpa only [Metric.mem_sphere, dist_zero_right] using norm_eq_of_mem_sphere x⟩
    have hn : equatorNorth v z = ⟨x, hx⟩ := by apply Subtype.ext; apply Subtype.ext; rfl
    have hs : equatorNorth (-v) (e z) = ⟨x, hy⟩ := by apply Subtype.ext; apply Subtype.ext; rfl
    change (hemisphereMap v q₀ f ⟨x, hx⟩).val =
      (hemisphereMap (-v) (e q₀) fS ⟨x, hy⟩).val
    rw [← hn, ← hs, hemisphereMap_equator, hemisphereMap_equator]
    apply Subtype.ext
    change (f z).val.val = (f (e.symm (e z))).val.val
    rw [e.symm_apply_apply]
  obtain ⟨φ, hN, hS⟩ := exists_continuousMap_glue_closed_cover hclosedN hclosedS hcover n s hagree
  refine ⟨φ, hN, hS, ?_⟩
  intro z
  change φ (equatorNorth v z).val = _
  rw [hN (equatorNorth v z)]
  change (hemisphereMap v q₀ f (equatorNorth v z)).val = _
  rw [hemisphereMap_equator]
  rfl

end BanachIsometric
