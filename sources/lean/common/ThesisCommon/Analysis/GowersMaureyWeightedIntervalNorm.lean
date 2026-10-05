import ThesisCommon.Analysis.GowersMaureyConcaveSum
import ThesisCommon.Analysis.GowersMaureyFormIntervals

/-! Summing interval estimates against a single finite measure. This is
the Jensen step used for the higher interval norms in source Lemma 7. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem intervalNorm_le_of_weight_measure (D : ConstructionData 𝕜)
    (x : C00 𝕜) {n : ℕ} (hn : 0 < n) (G : ℝ → ℝ)
    (hG : ConcaveOn ℝ (Set.Ici 0) G) (hmono : MonotoneOn G (Set.Ici 0))
    {C b W : ℝ} (hC : 0 ≤ C) (μ : ℕ → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (htotal : (∑ i ∈ (supportInterval x).set, μ i) = W)
    (hbound : ∀ E : Interval, E.set ⊆ (supportInterval x).set →
      implicitNorm D (restrict E x) ≤ C * (G (∑ i ∈ E.set, μ i) + b)) :
    intervalNorm D n x ≤ C * ((n : ℝ) * G (W / n) + n * b) := by
  classical
  rw [intervalNorm, Seminorm.sSup_apply (intervalSums_bddAbove D n)]
  letI : Nonempty (Set.range (intervalSum D (N := n))) := (Set.range_nonempty _).to_subtype
  apply ciSup_le
  rintro ⟨p, I, rfl⟩
  let J := I.inter (supportInterval x)
  have hJ : ∀ i, (J.interval i).set ⊆ (supportInterval x).set := I.inter_subset _
  have hrestrict : ∀ i, restrict (I.interval i) x = restrict (J.interval i) x := by
    intro i
    change restrict (I.interval i) x = restrict ((I.interval i).inter (supportInterval x)) x
    rw [← restrict_restrict, restrict_supportInterval]
  have hsum : (∑ i, ∑ j ∈ (J.interval i).set, μ j) ≤ W := by
    rw [← htotal]
    exact J.sum_mass_le hJ μ hμ
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hJensen := concave_sum_le_card_mul hG hmono Finset.univ hnonempty
    (fun i => ∑ j ∈ (J.interval i).set, μ j)
    (fun i _ => Finset.sum_nonneg fun j _ => hμ j) hsum
  simp only [Finset.card_univ, Fintype.card_fin] at hJensen
  change intervalSum D I x ≤ _
  rw [intervalSum_apply]
  calc
    (∑ i, implicitNorm D (restrict (I.interval i) x)) =
        ∑ i, implicitNorm D (restrict (J.interval i) x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hrestrict i]
    _ ≤ ∑ i, C * (G (∑ j ∈ (J.interval i).set, μ j) + b) :=
      Finset.sum_le_sum fun i _ => hbound _ (hJ i)
    _ = C * ((∑ i, G (∑ j ∈ (J.interval i).set, μ j)) + n * b) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp
    _ ≤ C * ((n : ℝ) * G (W / n) + n * b) :=
      mul_le_mul_of_nonneg_left (add_le_add_right hJensen _) hC

end ThesisCommon.GowersMaurey
