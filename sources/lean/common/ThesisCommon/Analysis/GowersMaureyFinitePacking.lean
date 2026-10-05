import ThesisCommon.Analysis.GowersMaureyIntervalPacking

/-! Passing from an unordered finite disjoint interval packing to the
successive interval families in the constructed norm. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem largeIntervalWeight_finset_packing (D : ConstructionData 𝕜) {N : ℕ} (hN : 0 < N)
    {x : C00 𝕜} (hx : intervalNorm D N x ≤ 1) (S : Finset (ℕ × ℕ))
    (hvalid : ∀ E ∈ S, E.1 ≤ E.2)
    (hdisj : ∀ E ∈ S, ∀ F ∈ S, E ≠ F →
      Disjoint (Finset.Icc E.1 E.2) (Finset.Icc F.1 F.2)) :
    (∑ E ∈ S, largeIntervalWeight D N x ⟨E.1, E.2⟩) ≤ 1 := by
  classical
  have hinj : Function.Injective (fun E : S => E.val.1) := by
    intro E F hef
    apply Subtype.ext
    by_contra hne
    have hd := hdisj E.val E.property F.val F.property hne
    exact Finset.disjoint_left.mp hd
      (Finset.mem_Icc.mpr ⟨le_rfl, hvalid _ E.property⟩)
      (Finset.mem_Icc.mpr ⟨hef.ge, hef.trans_le (hvalid _ F.property)⟩)
  let ord : LinearOrder S := LinearOrder.lift' (fun E : S => E.val.1) hinj
  letI : LinearOrder S := ord
  letI : LE S := ord.toLE
  letI : LT S := ord.toLT
  let e : Fin S.card ≃o S := Fintype.orderIsoFinOfCardEq S (k := S.card) (by simp)
  let I : FiniteIntervalFamily S.card := {
    interval := fun i => ⟨(e i).val.1, (e i).val.2⟩
    successive := by
      intro i j hij s hs t ht
      have hstart : (e i).val.1 < (e j).val.1 := by
        apply lt_of_not_ge
        intro hji
        have hji' : e j ≤ e i := hji
        exact (not_le_of_gt hij) (e.le_iff_le.mp hji')
      have hne : (e i).val ≠ (e j).val := by
        intro heq
        exact (ne_of_lt hstart) (congrArg Prod.fst heq)
      have hd := hdisj _ (e i).property _ (e j).property hne
      have hend : (e i).val.2 < (e j).val.1 := by
        by_contra hn
        exact Finset.disjoint_left.mp hd
          (Finset.mem_Icc.mpr ⟨hstart.le, by omega⟩)
          (Finset.mem_Icc.mpr ⟨le_rfl, hvalid _ (e j).property⟩)
      exact (Finset.mem_Icc.mp hs).2.trans_lt (hend.trans_le (Finset.mem_Icc.mp ht).1) }
  have hsum : (∑ i, largeIntervalWeight D N x (I.interval i)) =
      ∑ E ∈ S, largeIntervalWeight D N x ⟨E.1, E.2⟩ := by
    have he := Equiv.sum_comp e.toEquiv (fun E : S => largeIntervalWeight D N x ⟨E.val.1, E.val.2⟩)
    exact he.trans (Finset.sum_attach S (fun E => largeIntervalWeight D N x ⟨E.1, E.2⟩))
  rw [← hsum]
  exact largeIntervalWeight_packing D hN hx I

end ThesisCommon.GowersMaurey
