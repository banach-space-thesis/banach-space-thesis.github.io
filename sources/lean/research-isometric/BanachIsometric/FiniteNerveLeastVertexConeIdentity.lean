import BanachIsometric.FiniteNerveLeastVertexCone

/-! The actual chain-cone identity at a least vertex, proved on the finite
ordered-face basis and extended linearly. No chain exactness premise is used. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type} [LinearOrder ι] [OrderBot ι] [Fintype ι]
variable (K : Complex ι) (hcone : ∀ s ∈ K.faces, insert (⊥ : ι) s ∈ K.faces)

theorem prependBottom_face_zero_of_first_eq_bottom {n : ℕ}
    (v : StrictOrderedSimplex K (n + 1)) (hv : v.val.val 0 = ⊥)
    (hpos : (⊥ : ι) < (strictOrderedFace K 0 v).val.val 0) :
    prependBottomSimplex K hcone (strictOrderedFace K 0 v) hpos = v := by
  apply Subtype.ext
  apply Subtype.ext
  apply OrderHom.ext
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact hv.symm
  · change (strictOrderedFace K 0 v).val.val j = v.val.val j.succ
    exact congrArg v.val.val (congrFun Fin.succAbove_zero j)

theorem leastVertexCone_chain_identity_single (n : ℕ)
    (v : StrictOrderedSimplex K (n + 1)) :
    finiteRationalBoundary K (n + 1)
        (leastVertexCone K hcone (n + 1) (Finsupp.single v 1)) +
      leastVertexCone K hcone n (finiteRationalBoundary K n (Finsupp.single v 1)) =
        Finsupp.single v 1 := by
  classical
  by_cases hv : (⊥ : ι) < v.val.val 0
  · rw [leastVertexCone_single, dif_pos hv, finiteRationalBoundary_single,
      finiteRationalBoundary_single]
    simp only [map_sum, map_zsmul, leastVertexCone_single]
    have hfaces : ∀ i : Fin (n + 2), (⊥ : ι) < (strictOrderedFace K i v).val.val 0 :=
      bottom_lt_face_first K v hv
    simp only [dif_pos (hfaces _)]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, strictOrderedFace_prependBottom_zero,
      strictOrderedFace_prependBottom_succ, Fin.val_succ, pow_succ, mul_neg, mul_one,
      neg_smul, Finset.sum_neg_distrib]
    abel
  · have hv0 : v.val.val 0 = ⊥ := le_antisymm (le_of_not_gt hv) bot_le
    have hpos : (⊥ : ι) < (strictOrderedFace K 0 v).val.val 0 := by
      have h01 : (0 : Fin (n + 2)) < (0 : Fin (n + 1)).succ := by simp
      simpa only [strictOrderedFace, orderedFace_apply, Fin.succAbove_zero, hv0] using
        v.property h01
    have hsucc : ∀ i : Fin (n + 1),
        ¬ (⊥ : ι) < (strictOrderedFace K i.succ v).val.val 0 := by
      intro i
      change ¬ (⊥ : ι) < v.val.val (i.succ.succAbove 0)
      rw [Fin.succ_succAbove_zero, hv0]
      exact lt_irrefl _
    rw [leastVertexCone_single, dif_neg hv, map_zero, zero_add,
      finiteRationalBoundary_single]
    simp only [map_sum, map_zsmul]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, leastVertexCone_single, dif_pos hpos,
      dif_neg (hsucc _), smul_zero, Finset.sum_const_zero, add_zero,
      prependBottom_face_zero_of_first_eq_bottom K hcone v hv0 hpos]

theorem leastVertexCone_chain_identity (n : ℕ) :
    (finiteRationalBoundary K (n + 1)).comp (leastVertexCone K hcone (n + 1)) +
      (leastVertexCone K hcone n).comp (finiteRationalBoundary K n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro v a
  have hsingle : Finsupp.single v a = a • Finsupp.single v 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  exact leastVertexCone_chain_identity_single K hcone n v

include hcone in
theorem exists_boundary_of_cycle_leastVertexCone (n : ℕ)
    (x : FiniteRationalChains K (n + 1)) (hx : finiteRationalBoundary K n x = 0) :
    ∃ y : FiniteRationalChains K (n + 2), finiteRationalBoundary K (n + 1) y = x := by
  refine ⟨leastVertexCone K hcone (n + 1) x, ?_⟩
  have h := LinearMap.congr_fun (leastVertexCone_chain_identity K hcone n) x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, hx,
    map_zero, add_zero] using h

end BanachIsometric.FiniteNerve
