import BanachIsometric.FiniteNerveOrderPrism
import BanachIsometric.FiniteNerveVertexMap

/-! Actual endpoint faces of the ordered vertex prism. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open SingularPrism
variable {ι : Type} [LinearOrder ι] [Fintype ι]
variable (K : Complex ι) (f g : ι →o ι) (hfg : ∀ a, f a ≤ g a)
  (hboth : ∀ s ∈ K.faces, s.image f ∪ s.image g ∈ K.faces)

include hboth in
theorem orderPrism_left_faces (s : Finset ι) (hs : s ∈ K.faces) : s.image f ∈ K.faces :=
  K.downward _ (hboth s hs) _ Finset.subset_union_left
    (Finset.image_nonempty.mpr (K.nonempty s hs))

include hboth in
theorem orderPrism_right_faces (s : Finset ι) (hs : s ∈ K.faces) : s.image g ∈ K.faces :=
  K.downward _ (hboth s hs) _ Finset.subset_union_right
    (Finset.image_nonempty.mpr (K.nonempty s hs))

theorem orderPrismSimplex_face_top {n : ℕ} (v : OrderedSimplex K n) :
    orderedFace K 0 (orderPrismSimplex K f g hfg hboth v 0) =
      orderedVertexMap K g (orderPrism_right_faces K f g hboth) v := by
  apply Subtype.ext
  apply OrderHom.ext
  funext k
  have hu := congrFun (upper_zero_face_zero n) k
  have hm := congrFun (merge_zero_face_zero n) k
  simp only [Function.comp_apply] at hu hm
  change (if upper (0 : Fin (n + 1)) ((0 : Fin (n + 2)).succAbove k) = 0 then
      f (v.val ((0 : Fin (n + 1)).predAbove ((0 : Fin (n + 2)).succAbove k))) else
      g (v.val ((0 : Fin (n + 1)).predAbove ((0 : Fin (n + 2)).succAbove k)))) = _
  rw [hu, hm]
  rfl

theorem orderPrismSimplex_face_bottom {n : ℕ} (v : OrderedSimplex K n) :
    orderedFace K (Fin.last (n + 1)) (orderPrismSimplex K f g hfg hboth v (Fin.last n)) =
      orderedVertexMap K f (orderPrism_left_faces K f g hboth) v := by
  apply Subtype.ext
  apply OrderHom.ext
  funext k
  have hu := congrFun (upper_last_face_last n) k
  have hm := congrFun (merge_last_face_last n) k
  simp only [Function.comp_apply] at hu hm
  change (if upper (Fin.last n) ((Fin.last (n + 1)).succAbove k) = 0 then
      f (v.val ((Fin.last n).predAbove ((Fin.last (n + 1)).succAbove k))) else
      g (v.val ((Fin.last n).predAbove ((Fin.last (n + 1)).succAbove k)))) = _
  rw [hu, hm]
  rfl

end BanachIsometric.FiniteNerve
