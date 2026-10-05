import ThesisCommon.Analysis.RCLikeL1FiniteCutApproximation

/-! Disjoint cutoff mass identities for real or complex L1. -/
noncomputable section
open MeasureTheory Set Filter Function
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem rclike_lOneCut_compl_cut (A B : Set X) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (f : Lp 𝕜 1 μ) :
    lpCut B hB (lpCut Aᶜ hA.compl f) = lpCut (B \ A) (hB.diff hA) f := by
  apply Lp.ext
  filter_upwards [lpCut_coe B hB (lpCut Aᶜ hA.compl f), lpCut_coe Aᶜ hA.compl f,
    lpCut_coe (B \ A) (hB.diff hA) f] with x h1 h2 h3
  rw [h1, h3]
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hxA, hxB, h2]

theorem norm_rclike_lOneCut_union (A B : Set X) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (f : Lp 𝕜 1 μ) :
    ‖lpCut (A ∪ B) (hA.union hB) f‖ =
      ‖lpCut A hA f‖ + ‖lpCut B hB (lpCut Aᶜ hA.compl f)‖ := by
  rw [rclike_lOneCut_compl_cut A B hA hB]
  simp only [norm_rclike_lOneCut_eq_integral]
  have heq : A ∪ B = A ∪ (B \ A) := by ext x; simp
  rw [heq]
  exact setIntegral_union (disjoint_sdiff_self_right) (hB.diff hA)
    (L1.integrable_coeFn f).norm.integrableOn (L1.integrable_coeFn f).norm.integrableOn

theorem norm_rclike_lOneCut_add_compl (A : Set X) (hA : MeasurableSet A)
    (f : Lp 𝕜 1 μ) : ‖lpCut A hA f‖ + ‖lpCut Aᶜ hA.compl f‖ = ‖f‖ := by
  simp only [norm_rclike_lOneCut_eq_integral]
  rw [L1.norm_eq_integral_norm]
  exact integral_add_compl hA (L1.integrable_coeFn f).norm

theorem rclike_lOneCut_add_compl (A : Set X) (hA : MeasurableSet A)
    (f : Lp 𝕜 1 μ) : lpCut A hA f + lpCut Aᶜ hA.compl f = f := by
  apply Lp.ext
  filter_upwards [lpCut_coe A hA f, lpCut_coe Aᶜ hA.compl f,
    Lp.coeFn_add (lpCut A hA f) (lpCut Aᶜ hA.compl f)] with x ha hb hc
  rw [hc, Pi.add_apply, ha, hb]
  by_cases hx : x ∈ A <;> simp [hx]

theorem rclike_lOneCut_pairwise_ae_disjoint (A : ℕ → Set X)
    (hA : ∀ n, MeasurableSet (A n)) (hd : Pairwise (Disjoint on A))
    (f : ℕ → Lp 𝕜 1 μ) :
    Pairwise fun i j => ∀ᵐ x ∂μ,
      lpCut (A i) (hA i) (f i) x = 0 ∨ lpCut (A j) (hA j) (f j) x = 0 := by
  intro i j hij
  filter_upwards [lpCut_coe (A i) (hA i) (f i), lpCut_coe (A j) (hA j) (f j)]
    with x hi hj
  rw [hi, hj]
  by_cases hx : x ∈ A i
  · right
    exact indicator_of_notMem (fun hxj => (Set.disjoint_left.mp (hd hij)) hx hxj) _
  · exact Or.inl (indicator_of_notMem hx _)

end ThesisCommon
