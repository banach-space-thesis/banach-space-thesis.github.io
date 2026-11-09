import BanachIsometric.SingularKunnethComponents

/-! On a tensor cycle, a pairing by two boundary-killing maps factors
through the two actual homology projections. This keeps the representative
argument valid even when individual tensor summands are not cycles. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW
open scoped TensorProduct DirectSum

variable (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]

theorem rawTensorHomologyInclusion_component {n p q : ℕ} (h : p + q = n)
    (c : RawHomologyTensorDegree X Y n) :
    rawTensorComponent X Y p q (rawTensorHomologyInclusion X Y n c).val =
      TensorProduct.map (rawFactorHomologyInclusion X p) (rawFactorHomologyInclusion Y q)
        (rawHomologyTensorComponent X Y h c) := by
  have he : (rawTensorComponent X Y p q).comp ((rawTensorTotalDegree X Y n).subtype.comp
      (rawTensorHomologyInclusion X Y n)) =
      (TensorProduct.map (rawFactorHomologyInclusion X p) (rawFactorHomologyInclusion Y q)).comp
        (rawHomologyTensorComponent X Y h) := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨r, s⟩, hrs⟩
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change rawTensorComponent X Y p q
      (rawTensorHomologyInclusion X Y n (rawHomologyTensorInclusion X Y hrs (a ⊗ₜ[ℚ] b))).val =
      TensorProduct.map (rawFactorHomologyInclusion X p) (rawFactorHomologyInclusion Y q)
        (rawHomologyTensorComponent X Y h (rawHomologyTensorInclusion X Y hrs (a ⊗ₜ[ℚ] b)))
    rw [rawTensorHomologyInclusion_tmul]
    change rawTensorComponent X Y p q (rawTensorInclusion X Y r s
      (rawFactorHomologyInclusion X r a ⊗ₜ[ℚ] rawFactorHomologyInclusion Y s b)) = _
    by_cases hp : (r, s) = (p, q)
    · have hr : r = p := congrArg Prod.fst hp
      have hs : s = q := congrArg Prod.snd hp
      subst r
      subst s
      simp only [rawHomologyTensorComponent_inclusion, rawTensorComponent_inclusion, TensorProduct.map_tmul]
    · rw [rawTensorComponent_inclusion_of_ne X Y hp,
        rawHomologyTensorComponent_inclusion_of_ne X Y h hrs hp, map_zero]
  exact LinearMap.congr_fun he c

theorem rawTensorCycle_pairing {n p q : ℕ} (h : p + q = n)
    {A B : Type*} [AddCommMonoid A] [Module ℚ A] [AddCommMonoid B] [Module ℚ B]
    (f : RawRationalChains X p →ₗ[ℚ] A) (g : RawRationalChains Y q →ₗ[ℚ] B)
    (hf : ∀ a, f (rawBoundary p a) = 0) (hg : ∀ b, g (rawBoundary q b) = 0)
    (c : rawTensorCycles X Y n) :
    TensorProduct.map f g (rawTensorComponent X Y p q c.val.val) =
      TensorProduct.map (f.comp (rawFactorHomologyInclusion X p))
        (g.comp (rawFactorHomologyInclusion Y q))
        (rawHomologyTensorComponent X Y h (rawTensorHomologyProjection X Y n c.val)) := by
  let L := (TensorProduct.map f g).comp (rawTensorComponent X Y p q)
  have hf0 : f.comp (rawBoundary p) = 0 := LinearMap.ext hf
  have hg0 : g.comp (rawBoundary q) = 0 := LinearMap.ext hg
  have hd : ∀ z, L (rawTensorTotalBoundary X Y z) = 0 := by
    intro z
    simp only [L, LinearMap.comp_apply, rawTensorComponent_totalBoundary, map_add, map_smul,
      TensorProduct.map_map, LinearMap.comp_id, hf0, hg0, TensorProduct.map_zero_left,
      TensorProduct.map_zero_right, LinearMap.zero_apply, smul_zero, add_zero]
  have hz := rawTensorBoundary_totalHomotopy_of_cycle X Y (rawTensorCycles_totalBoundary_zero X Y n c)
  have he := congrArg L hz
  rw [map_add, hd, zero_add, ← rawTensorHomologyInclusion_projection X Y n c.val] at he
  change TensorProduct.map f g (rawTensorComponent X Y p q
    (rawTensorHomologyInclusion X Y n (rawTensorHomologyProjection X Y n c.val)).val) = _ at he
  rw [rawTensorHomologyInclusion_component X Y h, TensorProduct.map_map] at he
  exact he.symm

end BanachIsometric.SingularEZ
