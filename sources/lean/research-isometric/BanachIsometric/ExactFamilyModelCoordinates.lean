import BanachIsometric.ExactFamilyTopology

/-!
# Actual model coordinates for exact families

A genuine continuous linear equivalence changes the model coordinates and
pulls back the specified gauge. The ambient norm, normal map, tangency and
all actual section maps retain their original meaning.
-/

namespace BanachIsometric

open scoped NNReal

variable {W E V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem IsDefinitePositiveHomogeneous.comp_continuousLinearEquiv
    {p : E → ℝ} (hp : IsDefinitePositiveHomogeneous p) (e : W ≃L[ℝ] E) :
    IsDefinitePositiveHomogeneous (fun x => p (e x)) where
  nonneg := fun x => hp.nonneg (e x)
  eq_zero_iff := fun x => by
    rw [hp.eq_zero_iff]
    exact e.map_eq_zero_iff
  smul_nonneg := fun t ht x => by rw [map_smul, hp.smul_nonneg t ht]

namespace ExactTangentialFamily

variable {g : V → ℝ} {p : E → ℝ}

noncomputable def transportModel (A : ExactTangentialFamily E V g p) (e : W ≃L[ℝ] E) :
    ExactTangentialFamily W V g (fun x => p (e x)) where
  normal := A.normal
  maps z := (A.maps z).comp e.toContinuousLinearMap
  maps_lipschitz := by
    obtain ⟨L, hL⟩ := A.maps_lipschitz
    let T : (E →L[ℝ] V) →L[ℝ] (W →L[ℝ] V) :=
      (ContinuousLinearMap.compL ℝ W E V).flip e.toContinuousLinearMap
    exact ⟨_, T.lipschitz.comp hL⟩
  tangent := fun z y => A.tangent z (e y)
  gauge_eq := fun z y => A.gauge_eq z (e y)

@[simp] theorem transportModel_maps_apply
    (A : ExactTangentialFamily E V g p) (e : W ≃L[ℝ] E) (z) (y : W) :
    (A.transportModel e).maps z y = A.maps z (e y) := rfl

end ExactTangentialFamily
end BanachIsometric
