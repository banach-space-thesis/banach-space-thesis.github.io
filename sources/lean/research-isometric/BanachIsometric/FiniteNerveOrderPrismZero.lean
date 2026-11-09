import BanachIsometric.FiniteNerveOrderPrismChain

/-! The actual ordered-prism identity in degree zero, with its two literal
endpoint faces. No negative chain degree is introduced. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type} [LinearOrder ι] [Fintype ι]
variable (K : Complex ι) (f g : ι →o ι) (hfg : ∀ a, f a ≤ g a)
  (hboth : ∀ s ∈ K.faces, s.image f ∪ s.image g ∈ K.faces)

theorem weakOrderPrism_zero_single (v : OrderedSimplex K 0) :
    weakRationalBoundary K 0 (weakOrderPrism K f g hfg hboth 0 (Finsupp.single v 1)) =
      Finsupp.single (orderedVertexMap K g (orderPrism_right_faces K f g hboth) v) 1 -
        Finsupp.single (orderedVertexMap K f (orderPrism_left_faces K f g hboth) v) 1 := by
  have hp : weakOrderPrism K f g hfg hboth 0 (Finsupp.single v 1) =
      Finsupp.single (orderPrismSimplex K f g hfg hboth v (0 : Fin 1)) 1 := by
    rw [weakOrderPrism_single_one]
    simp
  rw [hp, weakRationalBoundary_single]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val •
    Finsupp.single (orderedFace K i (orderPrismSimplex K f g hfg hboth v (0 : Fin 1))) 1) = _
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_one_smul]
  rw [orderPrismSimplex_face_top]
  have hb := orderPrismSimplex_face_bottom K f g hfg hboth v
  change orderedFace K (1 : Fin 2) (orderPrismSimplex K f g hfg hboth v (0 : Fin 1)) = _ at hb
  rw [hb, sub_eq_add_neg]

theorem weakOrderPrism_zero_identity :
    (weakRationalBoundary K 0).comp (weakOrderPrism K f g hfg hboth 0) =
      weakVertexChainMap K g (orderPrism_right_faces K f g hboth) 0 -
        weakVertexChainMap K f (orderPrism_left_faces K f g hboth) 0 := by
  apply Finsupp.lhom_ext
  intro v a
  have hsingle : Finsupp.single v a = a • Finsupp.single v 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, weakVertexChainMap_single] using
    weakOrderPrism_zero_single K f g hfg hboth v

end BanachIsometric.FiniteNerve
