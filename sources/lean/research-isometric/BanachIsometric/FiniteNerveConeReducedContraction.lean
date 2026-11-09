import BanachIsometric.FiniteNerveConeContraction
import BanachIsometric.FiniteNerveOrderPrismZero
import BanachIsometric.FiniteNerveAugmentation

/-! Actual degree-zero reduced chain filling in a finite cone. The apex is
an actual vertex face, and augmentation is the literal rational coefficient
sum. The same constructed cone operator fills every zero-augmentation chain. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type} [LinearOrder ι] [Fintype ι]
variable (K : Complex ι) (a : ι) (hcone : ∀ s ∈ K.faces, insert a s ∈ K.faces)

def coneApexSimplex (hvertex : {a} ∈ K.faces) : StrictOrderedSimplex K 0 := by
  letI : Subsingleton (Fin 1) := Fin.subsingleton_one
  let f : Fin 1 →o ι := ⟨fun _ => a, monotone_const⟩
  refine ⟨⟨f, K.downward _ hvertex _ ?_ ?_⟩, Subsingleton.strictMono _⟩
  · intro x hx
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_singleton_self a
  · exact Finset.image_nonempty.mpr Finset.univ_nonempty

theorem strictChainProjection_constant_zero (hvertex : {a} ∈ K.faces)
    (hf : ∀ s ∈ K.faces, s.image (coneConstantVertex a) ∈ K.faces) :
    ((strictChainProjection K 0).comp (weakVertexChainMap K (coneConstantVertex a) hf 0)).comp
        (strictChainInclusion K 0) =
      (LinearMap.toSpanSingleton ℚ _ (Finsupp.single (coneApexSimplex K a hvertex) 1)).comp
        (finiteAugmentation K) := by
  letI : Subsingleton (Fin 1) := Fin.subsingleton_one
  apply Finsupp.lhom_ext
  intro v c
  have hsingle : Finsupp.single v c = c • Finsupp.single v 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  simp only [LinearMap.comp_apply, strictChainInclusion, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, weakVertexChainMap_single, strictChainProjection_single,
    finiteAugmentation_single, LinearMap.toSpanSingleton_apply, one_smul]
  rw [dif_pos (Subsingleton.strictMono _)]
  congr 1

theorem weakConeHomotopy_zero_identity :
    (weakRationalBoundary K 0).comp (weakConeHomotopy K a hcone 0) =
      LinearMap.id - weakVertexChainMap K (coneConstantVertex a)
        (orderPrism_right_faces K (coneMinVertex a) (coneConstantVertex a)
          (coneMinConstant_faces K a hcone)) 0 := by
  apply LinearMap.ext
  intro x
  have h₁ := LinearMap.congr_fun
    (weakOrderPrism_zero_identity K (coneMinVertex a) coneIdentityVertex
      (coneMinVertex_le_identity a) (coneMinIdentity_faces K a hcone)) x
  have h₂ := LinearMap.congr_fun
    (weakOrderPrism_zero_identity K (coneMinVertex a) (coneConstantVertex a)
      (coneMinVertex_le_constant a) (coneMinConstant_faces K a hcone)) x
  rw [weakVertexChainMap_identity] at h₁
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at h₁ h₂ ⊢
  simp only [weakConeHomotopy, LinearMap.sub_apply, map_sub]
  rw [h₁, h₂]
  abel

theorem finiteConeHomotopy_zero_identity (hvertex : {a} ∈ K.faces)
    (x : FiniteRationalChains K 0) :
    finiteRationalBoundary K 0 (finiteConeHomotopy K a hcone 0 x) =
      x - finiteAugmentation K x • Finsupp.single (coneApexSimplex K a hvertex) 1 := by
  let y := strictChainInclusion K 0 x
  have hw := LinearMap.congr_fun (weakConeHomotopy_zero_identity K a hcone) y
  have hp := congrArg (strictChainProjection K 0) hw
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub] at hp
  have hb : strictChainProjection K 0 (weakRationalBoundary K 0 (weakConeHomotopy K a hcone 0 y)) =
      finiteRationalBoundary K 0 (strictChainProjection K 1 (weakConeHomotopy K a hcone 0 y)) :=
    LinearMap.congr_fun (strictChainProjection_boundary K 0) _
  have hc : strictChainProjection K 0
      (weakVertexChainMap K (coneConstantVertex a)
        (orderPrism_right_faces K (coneMinVertex a) (coneConstantVertex a)
          (coneMinConstant_faces K a hcone)) 0 y) =
      finiteAugmentation K x • Finsupp.single (coneApexSimplex K a hvertex) 1 :=
    LinearMap.congr_fun (strictChainProjection_constant_zero K a hvertex _) x
  have hpx : strictChainProjection K 0 y = x :=
    LinearMap.congr_fun (strictChainProjection_inclusion K 0) x
  rw [hb, hc, hpx] at hp
  exact hp

include hcone in
theorem exists_boundary_of_augmentation_zero_cone (hvertex : {a} ∈ K.faces)
    (x : FiniteRationalChains K 0) (hx : finiteAugmentation K x = 0) :
    ∃ y : FiniteRationalChains K 1, finiteRationalBoundary K 0 y = x := by
  refine ⟨finiteConeHomotopy K a hcone 0 x, ?_⟩
  simpa only [hx, zero_smul, sub_zero] using finiteConeHomotopy_zero_identity K a hcone hvertex x

end BanachIsometric.FiniteNerve
