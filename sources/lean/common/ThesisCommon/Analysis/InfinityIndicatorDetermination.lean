import ThesisCommon.Analysis.FilterFunctionalCharge
import ThesisCommon.Analysis.InfinityFiniteApproximation

/-! Bounded operators on supported scalar bounded families are determined
by all supported indicator functions. The finite sums here use indicators
of arbitrary subsets, not only singleton coordinate vectors. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 Γ Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem infinity_finite_range_indicator_representation
    (x : lp (fun _ : Γ => 𝕜) ∞) (hx : (Set.range (fun i => x i)).Finite)
    {B : Set Γ} (hsupp : ∀ i ∉ B, x i = 0) :
    ∃ (n : ℕ) (c : Fin n → 𝕜) (A : Fin n → Set Γ),
      (∀ i, A i ⊆ B) ∧ Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (∀ i, c i ≠ 0) ∧ x = ∑ i, c i • infinityIndicator (A i) := by
  classical
  let V : Set 𝕜 := Set.range (fun i => x i) \ {0}
  have hV : V.Finite := hx.diff
  letI := hV.fintype
  let e := Fintype.equivFin V
  let c : Fin (Fintype.card V) → 𝕜 := fun i => (e.symm i).val
  let A : Fin (Fintype.card V) → Set Γ := fun i => {j | x j = c i}
  have hc : ∀ i, c i ≠ 0 := fun i => (e.symm i).property.2
  have hdisj : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro k hi hj
    apply hij
    apply e.symm.injective
    exact Subtype.ext (hi.symm.trans hj)
  refine ⟨Fintype.card V, c, A, ?_, hdisj, hc, ?_⟩
  · intro i j hj
    by_contra hn
    exact hc i (hj.symm.trans (hsupp j hn))
  · ext j
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      infinityIndicator_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hj : x j = 0
    · have hn : ∀ i, j ∉ A i := fun i hi => hc i (hi.symm.trans hj)
      simp only [if_neg (hn _), Finset.sum_const_zero, hj]
    · let z : V := ⟨x j, ⟨⟨j, rfl⟩, hj⟩⟩
      let i := e z
      have hci : c i = x j := congrArg Subtype.val (e.symm_apply_apply z)
      have hi : j ∈ A i := hci.symm
      rw [Finset.sum_eq_single i]
      · simpa only [if_pos hi] using hci.symm
      · intro k _ hki
        have hk : j ∉ A k := fun hk => Set.disjoint_left.mp (hdisj hki.symm) hi hk
        simp only [if_neg hk]
      · simp

theorem infinity_operator_zero_on_supported_of_indicators
    (T : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] Y) {B : Set Γ}
    (hT : ∀ A : Set Γ, A ⊆ B → T (infinityIndicator A) = 0)
    (x : lp (fun _ : Γ => 𝕜) ∞) (hsupp : ∀ i ∉ B, x i = 0) : T x = 0 := by
  classical
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨y, hy, hzero, _, hdist⟩ :=
    infinity_exists_finite_range_approximation x (div_pos hε (by positivity : 0 < ‖T‖ + 1))
  obtain ⟨n, c, A, hAB, _, _, hrepr⟩ :=
    infinity_finite_range_indicator_representation y hy
      (fun i hi => hzero i (hsupp i hi))
  have hTy : T y = 0 := by
    rw [hrepr, map_sum]
    simp only [map_smul, hT _ (hAB _), smul_zero, Finset.sum_const_zero]
  have hreprT : T x = T (x - y) := by rw [map_sub, hTy, sub_zero]
  have hd : ‖x - y‖ * (‖T‖ + 1) < ε := (lt_div_iff₀ (by positivity)).mp hdist
  have hn : ‖T x‖ ≤ ‖T‖ * ‖x - y‖ := by
    rw [hreprT]
    exact T.le_opNorm _
  nlinarith [norm_nonneg (x - y)]

theorem infinity_operator_eq_on_supported_of_indicators
    (T S : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] Y) {B : Set Γ}
    (h : ∀ A : Set Γ, A ⊆ B → T (infinityIndicator A) = S (infinityIndicator A))
    (x : lp (fun _ : Γ => 𝕜) ∞) (hsupp : ∀ i ∉ B, x i = 0) : T x = S x := by
  have hz := infinity_operator_zero_on_supported_of_indicators (T - S)
    (fun A hA => by simpa only [ContinuousLinearMap.sub_apply, sub_eq_zero] using h A hA)
    x hsupp
  exact sub_eq_zero.mp hz

end ThesisCommon
