import BanachIsometric.HemisphereConeSurjective

/-! An actual equatorial null-homotopy extends over the literal closed
hemisphere, by descending through the proved compact cone quotient map. -/

noncomputable section

namespace BanachIsometric

open Set Metric
open scoped Topology

theorem exists_hemisphere_extension_of_homotopy_from_constant
    {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace Y] (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, Y)) (c : Y)
    (h : ContinuousMap.Homotopy (ContinuousMap.const _ c) f) :
    ∃ e : C(closedHemisphere v, Y), ∀ z, e (equatorNorth v z) = f z := by
  let lift : closedHemisphere v → unitInterval × EquatorSphere v :=
    fun x => (hemisphereCone_surjective v q₀ x).choose
  have hlift : ∀ x, hemisphereCone v (lift x) = x :=
    fun x => (hemisphereCone_surjective v q₀ x).choose_spec
  have hdesc : ∀ a b : unitInterval × EquatorSphere v,
      hemisphereCone v a = hemisphereCone v b → h a = h b := by
    rintro ⟨t, z⟩ ⟨u, w⟩ he
    obtain ⟨htu, hzw⟩ := hemisphereCone_fiber v t u z w he
    subst u
    rcases hzw with ht | hzw
    · subst t
      exact (h.apply_zero z).trans (h.apply_zero w).symm
    · cases hzw
      rfl
  let e : closedHemisphere v → Y := fun x => h (lift x)
  have heq : e ∘ hemisphereCone v = h :=
    funext (fun a => hdesc (lift (hemisphereCone v a)) a (hlift (hemisphereCone v a)))
  have hcont : Continuous e := by
    apply (isQuotientMap_hemisphereCone v q₀).continuous_iff.mpr
    rw [heq]
    exact h.continuous
  refine ⟨⟨e, hcont⟩, ?_⟩
  intro z
  have hcone : hemisphereCone v (1, z) = equatorNorth v z := by
    apply Subtype.ext
    apply Subtype.ext
    change Real.sqrt (1 - (1 : ℝ) ^ 2) • v.val + (1 : ℝ) • z.val.val = z.val.val
    norm_num
  calc
    e (equatorNorth v z) = e (hemisphereCone v (1, z)) := congrArg e hcone.symm
    _ = h (1, z) := congrFun heq (1, z)
    _ = f z := h.apply_one z

end BanachIsometric
