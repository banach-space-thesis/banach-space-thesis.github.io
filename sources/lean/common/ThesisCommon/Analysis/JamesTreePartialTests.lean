import ThesisCommon.Analysis.JamesTreePreSpace

/-! Dropping empty members of a finite disjoint segment family preserves its
actual finite product norm. This includes an empty remaining family and the
infinite exponent; no padding by hypothetical segments is used. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem piLp_norm_eq_of_zero_off_embedding (p : BanachExponent)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ↪ κ)
    (f : PiLp p.val (fun _ : ι => 𝕜)) (g : PiLp p.val (fun _ : κ => 𝕜))
    (he : ∀ i, f i = g (e i)) (hz : ∀ j ∉ Set.range e, g j = 0) : ‖f‖ = ‖g‖ := by
  classical
  rcases p with ⟨p, hp1⟩
  letI : Fact (1 ≤ p) := ⟨hp1⟩
  by_cases hp : p = ∞
  · subst p
    rw [← PiLp.norm_ofLp f, ← PiLp.norm_ofLp g]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      change ‖f i‖ ≤ _
      rw [he i]
      exact norm_le_pi_norm (WithLp.ofLp g) (e i)
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro j
      change ‖g j‖ ≤ _
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        rw [← he i]
        exact norm_le_pi_norm (WithLp.ofLp f) i
      · rw [hz j hj, norm_zero]
        exact norm_nonneg _
  · have hpr : 0 < p.toReal :=
      ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le hp1)) hp
    rw [PiLp.norm_eq_sum hpr, PiLp.norm_eq_sum hpr]
    congr 1
    exact Fintype.sum_of_injective e e.injective
      (fun i => ‖f i‖ ^ p.toReal) (fun j => ‖g j‖ ^ p.toReal)
      (fun j hj => by dsimp only; rw [hz j hj, norm_zero, Real.zero_rpow hpr.ne'])
      (fun i => by dsimp only; rw [he i])

/-- A partial test may contain empty segments. They contribute zero and can
be dropped, leaving a genuine finite disjoint test with exactly the same norm. -/
theorem jamesTree_partial_test_norm_le (p : BanachExponent)
    {S : JamesTreeSegmentFamily} (a : JamesTreePreSpace 𝕜 p S)
    {ι : Type*} [Fintype ι] (A : ι → Finset DyadicTreeNode)
    (ha : ∀ i, (A i).Nonempty → S.allows (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ‖WithLp.toLp p.val (fun i => ∑ t ∈ A i, a t)‖ ≤ ‖a‖ := by
  classical
  let I := {i : ι // (A i).Nonempty}
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let T : JamesTreeTest S := {
    count := Fintype.card I
    segment := fun k => A (e.symm k).val
    allowed := fun k => ha _ (e.symm k).property
    disjoint := fun i j hij => hd (fun heq => hij (e.symm.injective (Subtype.ext heq))) }
  let b : Fin T.count ↪ ι := {
    toFun := fun k => (e.symm k).val
    inj' := fun _ _ h => e.symm.injective (Subtype.ext h) }
  have heq := piLp_norm_eq_of_zero_off_embedding p b
    (jamesTreeTestMap 𝕜 p T a.coefficients)
    (WithLp.toLp p.val (fun i => ∑ t ∈ A i, a t))
    (fun _ => rfl) (fun i hi => by
      have hnot : ¬ (A i).Nonempty := by
        intro h
        apply hi
        refine ⟨e ⟨i, h⟩, ?_⟩
        exact congrArg Subtype.val (e.symm_apply_apply ⟨i, h⟩)
      have hempty : A i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
      change (∑ t ∈ A i, a t) = 0
      rw [hempty, Finset.sum_empty])
  rw [← heq]
  exact a.test_norm_le T

end ThesisCommon
