import BanachIsometric.SingularKunneth
import BanachIsometric.AlexanderWhitneyCoassociativity

/-! Each Künneth component is obtained by applying the two homology
projections to the literal Alexander--Whitney component. In particular,
these component maps kill actual boundaries. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW
open scoped TensorProduct DirectSum

variable (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]

def rawHomologyTensorComponent {n p q : ℕ} (h : p + q = n) :
    RawHomologyTensorDegree X Y n →ₗ[ℚ] (RawHomology X p ⊗[ℚ] RawHomology Y q) :=
  DirectSum.component ℚ (HomologyBidegrees n)
    (fun ij => RawHomology X ij.val.1 ⊗[ℚ] RawHomology Y ij.val.2) ⟨(p, q), h⟩

@[simp] theorem rawHomologyTensorComponent_inclusion {n p q : ℕ} (h : p + q = n)
    (c : RawHomology X p ⊗[ℚ] RawHomology Y q) :
    rawHomologyTensorComponent X Y h (rawHomologyTensorInclusion X Y h c) = c := by
  simp only [rawHomologyTensorComponent, rawHomologyTensorInclusion, DirectSum.component.lof_self]

theorem rawHomologyTensorComponent_inclusion_of_ne {n p q r s : ℕ} (h : p + q = n)
    (h' : r + s = n) (hne : (r, s) ≠ (p, q)) (c : RawHomology X r ⊗[ℚ] RawHomology Y s) :
    rawHomologyTensorComponent X Y h (rawHomologyTensorInclusion X Y h' c) = 0 := by
  have hj : (⟨(r, s), h'⟩ : HomologyBidegrees n) ≠ ⟨(p, q), h⟩ :=
    fun he => hne (congrArg Subtype.val he)
  simp only [rawHomologyTensorComponent, rawHomologyTensorInclusion, DirectSum.component.of, hj, dite_false]

theorem rawTensorHomologyProjectionTotal_component {n p q : ℕ} (h : p + q = n)
    (c : RawBigradedTensorChains X Y) :
    rawHomologyTensorComponent X Y h (rawTensorHomologyProjectionTotal X Y n c) =
      TensorProduct.map (rawFactorHomologyProjection X p) (rawFactorHomologyProjection Y q)
        (rawTensorComponent X Y p q c) := by
  have he : (rawHomologyTensorComponent X Y h).comp (rawTensorHomologyProjectionTotal X Y n) =
      (TensorProduct.map (rawFactorHomologyProjection X p) (rawFactorHomologyProjection Y q)).comp
        (rawTensorComponent X Y p q) := by
    apply DirectSum.linearMap_ext
    rintro ⟨r, s⟩
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change rawHomologyTensorComponent X Y h
        (rawTensorHomologyProjectionTotal X Y n (rawTensorInclusion X Y r s (a ⊗ₜ[ℚ] b))) =
      TensorProduct.map (rawFactorHomologyProjection X p) (rawFactorHomologyProjection Y q)
        (rawTensorComponent X Y p q (rawTensorInclusion X Y r s (a ⊗ₜ[ℚ] b)))
    by_cases hp : (r, s) = (p, q)
    · have hr : r = p := congrArg Prod.fst hp
      have hs : s = q := congrArg Prod.snd hp
      subst r
      subst s
      simp only [rawTensorHomologyProjectionTotal_tmul X Y h, rawHomologyTensorComponent_inclusion,
        rawTensorComponent_inclusion, TensorProduct.map_tmul]
    · rw [rawTensorComponent_inclusion_of_ne X Y hp, map_zero]
      by_cases hr : r + s = n
      · rw [rawTensorHomologyProjectionTotal_tmul X Y hr,
          rawHomologyTensorComponent_inclusion_of_ne X Y h hr hp]
      · rw [rawTensorHomologyProjectionTotal_of_ne X Y hr, map_zero]
  exact LinearMap.congr_fun he c

def rawKunnethChainComponent (n p q : ℕ) :
    RawRationalChains (X × Y) n →ₗ[ℚ] (RawHomology X p ⊗[ℚ] RawHomology Y q) :=
  (TensorProduct.map (rawFactorHomologyProjection X p) (rawFactorHomologyProjection Y q)).comp
    (rawAWComponent X Y n p q)

theorem rawKunnethChainComponent_projection {n p q : ℕ}
    (h : p + q = n) (c : RawRationalChains (X × Y) n) :
    rawHomologyTensorComponent X Y h
        (rawTensorHomologyProjectionTotal X Y n (rawAlexanderWhitney n c)) =
      rawKunnethChainComponent X Y n p q c :=
  rawTensorHomologyProjectionTotal_component X Y h (rawAlexanderWhitney n c)

theorem rawKunnethChainComponent_cycle {n p q : ℕ} (h : p + q = n)
    (c : RawHomologyCycles (X × Y) n) :
    rawHomologyTensorComponent X Y h
      (rawSingularKunnethEquiv X Y n (rawFactorHomologyProjection (X × Y) n c.val)) =
        rawKunnethChainComponent X Y n p q c.val := by
  rw [rawSingularKunnethEquiv_cycle]
  exact rawKunnethChainComponent_projection X Y h c.val

theorem rawKunnethChainComponent_boundary {n p q : ℕ} (h : p + q = n)
    (c : RawRationalChains (X × Y) (n + 1)) :
    rawKunnethChainComponent X Y n p q (rawBoundary n c) = 0 := by
  rw [← rawKunnethChainComponent_projection X Y h,
    ← show rawTensorTotalBoundary X Y (rawAlexanderWhitney (n + 1) c) =
      rawAlexanderWhitney n (rawBoundary n c) from LinearMap.congr_fun (rawAlexanderWhitney_boundary n) c,
    rawTensorHomologyProjectionTotal_boundary, map_zero]

end BanachIsometric.SingularEZ
