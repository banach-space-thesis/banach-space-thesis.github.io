import BanachIsometric.FiniteNerveOrderPrismChain
import BanachIsometric.FiniteNerveConeVertexMaps
import BanachIsometric.FiniteNerveRationalQuotientHomology

/-! Actual finite-chain contraction for a cone at an arbitrary apex. The
minimum vertex map lies below both the identity and the constant apex map.
Their proved weak prism homotopies are subtracted and transported through the
proved normalization projection. Positive homology vanishing follows from
the explicit chain identity, not from an acyclicity assumption. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type} [LinearOrder ι] [Fintype ι]
variable (K : Complex ι) (a : ι) (hcone : ∀ s ∈ K.faces, insert a s ∈ K.faces)

def weakConeHomotopy (n : ℕ) : WeakRationalChains K n →ₗ[ℚ] WeakRationalChains K (n + 1) :=
  weakOrderPrism K (coneMinVertex a) coneIdentityVertex (coneMinVertex_le_identity a)
      (coneMinIdentity_faces K a hcone) n -
    weakOrderPrism K (coneMinVertex a) (coneConstantVertex a) (coneMinVertex_le_constant a)
      (coneMinConstant_faces K a hcone) n

theorem weakConeHomotopy_chain_identity (n : ℕ) :
    (weakRationalBoundary K (n + 1)).comp (weakConeHomotopy K a hcone (n + 1)) +
      (weakConeHomotopy K a hcone n).comp (weakRationalBoundary K n) =
      LinearMap.id - weakVertexChainMap K (coneConstantVertex a)
        (orderPrism_right_faces K (coneMinVertex a) (coneConstantVertex a)
          (coneMinConstant_faces K a hcone)) (n + 1) := by
  apply LinearMap.ext
  intro x
  have h₁ := LinearMap.congr_fun
    (weakOrderPrism_chain_identity K (coneMinVertex a) coneIdentityVertex
      (coneMinVertex_le_identity a) (coneMinIdentity_faces K a hcone) n) x
  have h₂ := LinearMap.congr_fun
    (weakOrderPrism_chain_identity K (coneMinVertex a) (coneConstantVertex a)
      (coneMinVertex_le_constant a) (coneMinConstant_faces K a hcone) n) x
  rw [weakVertexChainMap_identity] at h₁
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply] at h₁ h₂ ⊢
  simp only [weakConeHomotopy, LinearMap.sub_apply, map_sub]
  calc
    _ = (weakRationalBoundary K (n + 1)
        (weakOrderPrism K (coneMinVertex a) coneIdentityVertex (coneMinVertex_le_identity a)
          (coneMinIdentity_faces K a hcone) (n + 1) x) +
        weakOrderPrism K (coneMinVertex a) coneIdentityVertex (coneMinVertex_le_identity a)
          (coneMinIdentity_faces K a hcone) n (weakRationalBoundary K n x)) -
      (weakRationalBoundary K (n + 1)
        (weakOrderPrism K (coneMinVertex a) (coneConstantVertex a) (coneMinVertex_le_constant a)
          (coneMinConstant_faces K a hcone) (n + 1) x) +
        weakOrderPrism K (coneMinVertex a) (coneConstantVertex a) (coneMinVertex_le_constant a)
          (coneMinConstant_faces K a hcone) n (weakRationalBoundary K n x)) := by abel
    _ = _ := by rw [h₁, h₂]; abel

def finiteConeHomotopy (n : ℕ) : FiniteRationalChains K n →ₗ[ℚ] FiniteRationalChains K (n + 1) :=
  (strictChainProjection K (n + 1)).comp
    ((weakConeHomotopy K a hcone n).comp (strictChainInclusion K n))

theorem finiteConeHomotopy_chain_identity (n : ℕ) :
    (finiteRationalBoundary K (n + 1)).comp (finiteConeHomotopy K a hcone (n + 1)) +
      (finiteConeHomotopy K a hcone n).comp (finiteRationalBoundary K n) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  let y := strictChainInclusion K (n + 1) x
  have hw := LinearMap.congr_fun (weakConeHomotopy_chain_identity K a hcone n) y
  have hp := congrArg (strictChainProjection K (n + 1)) hw
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_add, map_sub] at hp
  have hb : strictChainProjection K (n + 1)
      (weakRationalBoundary K (n + 1) (weakConeHomotopy K a hcone (n + 1) y)) =
      finiteRationalBoundary K (n + 1)
        (strictChainProjection K (n + 2) (weakConeHomotopy K a hcone (n + 1) y)) :=
    LinearMap.congr_fun (strictChainProjection_boundary K (n + 1)) _
  have hj : weakRationalBoundary K n y =
      strictChainInclusion K n (finiteRationalBoundary K n x) :=
    LinearMap.congr_fun (strictChainInclusion_boundary K n) x
  have hc : strictChainProjection K (n + 1)
      (weakVertexChainMap K (coneConstantVertex a)
        (orderPrism_right_faces K (coneMinVertex a) (coneConstantVertex a)
          (coneMinConstant_faces K a hcone)) (n + 1) y) = 0 :=
    LinearMap.congr_fun (strictChainProjection_constant K a _ n) y
  have hpx : strictChainProjection K (n + 1) y = x :=
    LinearMap.congr_fun (strictChainProjection_inclusion K (n + 1)) x
  rw [hb, hj, hc, hpx, sub_zero] at hp
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    finiteConeHomotopy, y] using hp

include hcone in
theorem exists_boundary_of_cycle_cone (n : ℕ) (x : FiniteRationalChains K (n + 1))
    (hx : finiteRationalBoundary K n x = 0) :
    ∃ y : FiniteRationalChains K (n + 2), finiteRationalBoundary K (n + 1) y = x := by
  refine ⟨finiteConeHomotopy K a hcone (n + 1) x, ?_⟩
  have h := LinearMap.congr_fun (finiteConeHomotopy_chain_identity K a hcone n) x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    hx, map_zero, add_zero] using h

include hcone in
theorem subsingleton_quotientRationalHomology_cone (n : ℕ) :
    Subsingleton (QuotientRationalHomology K (n + 1)) := by
  apply (Submodule.Quotient.subsingleton_iff _).mpr
  intro x
  have hx : finiteRationalBoundary K n x.val = 0 := x.property
  obtain ⟨y, hy⟩ := exists_boundary_of_cycle_cone K a hcone n x.val hx
  exact ⟨y, Subtype.ext hy⟩

end BanachIsometric.FiniteNerve
