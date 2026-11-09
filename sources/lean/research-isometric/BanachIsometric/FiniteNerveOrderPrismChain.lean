import BanachIsometric.FiniteNerveOrderPrismEndpoints
import BanachIsometric.PrismCancellation

/-! The actual chain homotopy induced by comparable ordered vertex maps.
All cancellation premises are discharged by literal prism face identities. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type} [LinearOrder ι] [Fintype ι]
variable (K : Complex ι) (f g : ι →o ι) (hfg : ∀ a, f a ≤ g a)
  (hboth : ∀ s ∈ K.faces, s.image f ∪ s.image g ∈ K.faces)

def weakOrderPrism (n : ℕ) : WeakRationalChains K n →ₗ[ℚ] WeakRationalChains K (n + 1) :=
  Finsupp.linearCombination ℚ (fun simplex =>
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
      Finsupp.single (orderPrismSimplex K f g hfg hboth simplex i) 1)

@[simp] theorem weakOrderPrism_single_one (n : ℕ) (simplex : OrderedSimplex K n) :
    weakOrderPrism K f g hfg hboth n (Finsupp.single simplex 1) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        Finsupp.single (orderPrismSimplex K f g hfg hboth simplex i) 1 := by
  simp [weakOrderPrism]

theorem weakOrderPrism_boundary_single (n : ℕ) (simplex : OrderedSimplex K (n + 1)) :
    weakRationalBoundary K (n + 1) (weakOrderPrism K f g hfg hboth (n + 1)
        (Finsupp.single simplex 1)) +
      weakOrderPrism K f g hfg hboth n (weakRationalBoundary K n (Finsupp.single simplex 1)) =
      Finsupp.single (orderedVertexMap K g (orderPrism_right_faces K f g hboth) simplex) 1 -
        Finsupp.single (orderedVertexMap K f (orderPrism_left_faces K f g hboth) simplex) 1 := by
  let u : Fin (n + 2) → Fin (n + 3) → WeakRationalChains K (n + 1) := fun i j =>
    (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) •
      Finsupp.single (orderedFace K j (orderPrismSimplex K f g hfg hboth simplex i)) 1
  let v : Fin (n + 1) → Fin (n + 2) → WeakRationalChains K (n + 1) := fun i j =>
    (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) •
      Finsupp.single (orderPrismSimplex K f g hfg hboth (orderedFace K j simplex) i) 1
  have hlower (i : Fin (n + 1)) (j : Fin (n + 2)) (h : j ≤ i.castSucc) :
      u i.succ j.castSucc = -v i j := by
    dsimp only [u, v]
    rw [orderPrismSimplex_face_before K f g hfg hboth simplex i j h]
    simp only [Fin.val_succ, Fin.coe_castSucc]
    rw [show (i : ℕ) + 1 + (j : ℕ) = ((i : ℕ) + (j : ℕ)) + 1 by omega,
      pow_succ, mul_neg_one, neg_smul]
  have hupper (i : Fin (n + 1)) (j : Fin (n + 2)) (h : i.castSucc < j) :
      u i.castSucc j.succ = -v i j := by
    dsimp only [u, v]
    rw [orderPrismSimplex_face_after K f g hfg hboth simplex i j h]
    simp only [Fin.val_succ, Fin.coe_castSucc]
    rw [show (i : ℕ) + ((j : ℕ) + 1) = ((i : ℕ) + (j : ℕ)) + 1 by omega,
      pow_succ, mul_neg_one, neg_smul]
  have hdiagonal (i : Fin (n + 1)) :
      u i.castSucc i.succ.castSucc = -u i.succ i.succ.castSucc := by
    dsimp only [u]
    rw [orderPrismSimplex_face_middle K f g hfg hboth simplex i]
    simp only [Fin.val_succ, Fin.coe_castSucc]
    rw [show ((i : ℕ) + 1) + ((i : ℕ) + 1) = ((i : ℕ) + ((i : ℕ) + 1)) + 1 by omega,
      pow_succ, mul_neg_one, neg_smul, neg_neg]
  have hc := signed_prism_cancellation n u v hlower hupper hdiagonal
  have hleft : weakRationalBoundary K (n + 1)
      (weakOrderPrism K f g hfg hboth (n + 1) (Finsupp.single simplex 1)) =
      ∑ i, ∑ j, u i j := by
    simp only [weakOrderPrism_single_one, map_sum, map_zsmul, weakRationalBoundary_single,
      Finset.smul_sum, smul_smul, ← pow_add, u]
  have hright : weakOrderPrism K f g hfg hboth n
      (weakRationalBoundary K n (Finsupp.single simplex 1)) = ∑ i, ∑ j, v i j := by
    simp only [weakRationalBoundary_single, map_sum, map_zsmul, weakOrderPrism_single_one,
      Finset.smul_sum, smul_smul, ← pow_add]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [v, Nat.add_comm]
  have hOdd : Odd ((n + 1) + (n + 2)) := ⟨n + 1, by omega⟩
  rw [hleft, hright, hc]
  simp only [u, Fin.val_zero, zero_add, pow_zero, one_smul, orderPrismSimplex_face_top,
    Fin.val_last, hOdd.neg_one_pow, orderPrismSimplex_face_bottom, neg_one_smul, sub_eq_add_neg]

theorem weakOrderPrism_chain_identity (n : ℕ) :
    (weakRationalBoundary K (n + 1)).comp (weakOrderPrism K f g hfg hboth (n + 1)) +
      (weakOrderPrism K f g hfg hboth n).comp (weakRationalBoundary K n) =
      weakVertexChainMap K g (orderPrism_right_faces K f g hboth) (n + 1) -
        weakVertexChainMap K f (orderPrism_left_faces K f g hboth) (n + 1) := by
  apply Finsupp.lhom_ext
  intro simplex a
  have hsingle : Finsupp.single simplex a = a • Finsupp.single simplex 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    weakVertexChainMap_single] using weakOrderPrism_boundary_single K f g hfg hboth n simplex

end BanachIsometric.FiniteNerve
