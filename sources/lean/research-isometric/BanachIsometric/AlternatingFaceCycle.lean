import BanachIsometric.RawSingularChains

/-! An actual compatible family of boundary simplices determines a cycle.
No simplex filling or extension of the family is assumed. The proof pairs
the signed terms on the two sides of each codimension-two face. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X : Type*} [TopologicalSpace X]

theorem rawBoundary_alternating_face_family (n : ℕ)
    (σ : Fin (n + 3) → RawSingularSimplex X (n + 1))
    (hface : ∀ (i j : Fin (n + 2)), i ≤ j →
      (σ j.succ).comp (face i) = (σ i.castSucc).comp (face j)) :
    rawBoundary n (∑ i : Fin (n + 3),
      (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (σ i) (1 : ℚ)) = 0 := by
  classical
  simp only [map_sum, map_zsmul, rawBoundary_single, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, ← Finset.sum_product']
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.is_lt), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.coe_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congrArg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using congrArg Fin.castSucc (congrArg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero'] at hij'
    · simpa [S] using Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, Fin.coe_castLT, pow_add, pow_one,
        mul_neg, neg_mul, neg_neg, mul_one]
      exact mul_comm _ _
    · have hji : Fin.castLT j (lt_of_le_of_lt (Finset.mem_filter.mp hij).right i.is_lt) ≤ i :=
        (Finset.mem_filter.mp hij).right
      congr 1
      simpa only [φ, Fin.castSucc_castLT] using (hface _ i hji).symm

end BanachIsometric.SingularPrism
