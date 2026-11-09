import BanachIsometric.FiniteNerveRationalBoundary
import BanachIsometric.SingularPrismFaces

/-! Literal weakly ordered simplex prisms between comparable vertex maps.
Their faces satisfy the actual prism identities, using only finite vertex
coordinate equations. No chain homotopy or acyclicity is assumed. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open SingularPrism

variable {ι : Type} [LinearOrder ι] [Fintype ι]
variable (K : Complex ι) (f g : ι →o ι) (hfg : ∀ a, f a ≤ g a)
  (hboth : ∀ s ∈ K.faces, s.image f ∪ s.image g ∈ K.faces)

def orderPrismValue {n : ℕ} (v : OrderedSimplex K n) (i : Fin (n + 1))
    (k : Fin (n + 2)) : ι :=
  if upper i k = 0 then f (v.val (i.predAbove k)) else g (v.val (i.predAbove k))

include hfg in
theorem monotone_orderPrismValue {n : ℕ} (v : OrderedSimplex K n) (i : Fin (n + 1)) :
    Monotone (orderPrismValue K f g v i) := by
  intro a b hab
  have hp := v.val.monotone (i.predAbove_right_monotone hab)
  have hone : (1 : Fin 2) ≠ 0 := by decide
  by_cases ha : (i : ℕ) < (a : ℕ) <;> by_cases hb : (i : ℕ) < (b : ℕ)
  · simpa only [orderPrismValue, upper, ha, hb, ite_true, hone, ite_false] using
      g.monotone hp
  · have hab' : (a : ℕ) ≤ (b : ℕ) := hab
    omega
  · simpa only [orderPrismValue, upper, ha, hb, ite_true, ite_false, if_pos rfl,
      hone] using (hfg _).trans (g.monotone hp)
  · simpa only [orderPrismValue, upper, ha, hb, ite_false, if_pos rfl] using f.monotone hp

def orderPrismSimplex {n : ℕ} (v : OrderedSimplex K n) (i : Fin (n + 1)) :
    OrderedSimplex K (n + 1) := by
  refine ⟨⟨orderPrismValue K f g v i, monotone_orderPrismValue K f g hfg v i⟩,
    K.downward _ (hboth _ v.property) _ ?_ ?_⟩
  · intro a ha
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp ha
    by_cases h : upper i k = 0
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨v.val (i.predAbove k), Finset.mem_image.mpr ⟨i.predAbove k, Finset.mem_univ _, rfl⟩,
          by simp [orderPrismValue, h]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨v.val (i.predAbove k), Finset.mem_image.mpr ⟨i.predAbove k, Finset.mem_univ _, rfl⟩,
          by simp [orderPrismValue, h]⟩)
  · exact Finset.image_nonempty.mpr Finset.univ_nonempty

@[simp] theorem orderPrismSimplex_apply {n : ℕ} (v : OrderedSimplex K n)
    (i : Fin (n + 1)) (k : Fin (n + 2)) :
    (orderPrismSimplex K f g hfg hboth v i).val k = orderPrismValue K f g v i k := rfl

theorem orderPrismSimplex_face_before {n : ℕ} (v : OrderedSimplex K (n + 1))
    (i : Fin (n + 1)) (j : Fin (n + 2)) (h : j ≤ i.castSucc) :
    orderedFace K j.castSucc (orderPrismSimplex K f g hfg hboth v i.succ) =
      orderPrismSimplex K f g hfg hboth (orderedFace K j v) i := by
  apply Subtype.ext
  apply OrderHom.ext
  funext k
  have hu := congrFun (upper_face_before i j h) k
  have hm := congrFun (merge_face_before i j h) k
  simp only [Function.comp_apply] at hu hm
  change (if upper i.succ (j.castSucc.succAbove k) = 0 then
      f (v.val (i.succ.predAbove (j.castSucc.succAbove k))) else
      g (v.val (i.succ.predAbove (j.castSucc.succAbove k)))) = _
  rw [hu, hm]
  rfl

theorem orderPrismSimplex_face_after {n : ℕ} (v : OrderedSimplex K (n + 1))
    (i : Fin (n + 1)) (j : Fin (n + 2)) (h : i.castSucc < j) :
    orderedFace K j.succ (orderPrismSimplex K f g hfg hboth v i.castSucc) =
      orderPrismSimplex K f g hfg hboth (orderedFace K j v) i := by
  apply Subtype.ext
  apply OrderHom.ext
  funext k
  have hu := congrFun (upper_face_after i j h) k
  have hm := congrFun (merge_face_after i j h) k
  simp only [Function.comp_apply] at hu hm
  change (if upper i.castSucc (j.succ.succAbove k) = 0 then
      f (v.val (i.castSucc.predAbove (j.succ.succAbove k))) else
      g (v.val (i.castSucc.predAbove (j.succ.succAbove k)))) = _
  rw [hu, hm]
  rfl

theorem orderPrismSimplex_face_middle {n : ℕ} (v : OrderedSimplex K (n + 1))
    (i : Fin (n + 1)) :
    orderedFace K i.succ.castSucc (orderPrismSimplex K f g hfg hboth v i.castSucc) =
      orderedFace K i.succ.castSucc (orderPrismSimplex K f g hfg hboth v i.succ) := by
  apply Subtype.ext
  apply OrderHom.ext
  funext k
  have hu := congrFun (upper_middle i) k
  have hm := congrFun (merge_middle i) k
  simp only [Function.comp_apply] at hu hm
  change (if upper i.castSucc (i.succ.castSucc.succAbove k) = 0 then
      f (v.val (i.castSucc.predAbove (i.succ.castSucc.succAbove k))) else
      g (v.val (i.castSucc.predAbove (i.succ.castSucc.succAbove k)))) = _
  rw [hu, hm]
  rfl

end BanachIsometric.FiniteNerve
