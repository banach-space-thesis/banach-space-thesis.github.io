import ThesisCommon.Analysis.L1DisjointEllOne
import Mathlib.Order.Disjointed

/-! Almost-everywhere disjoint countable L1 families admit genuinely
pairwise disjoint measurable supports. Null overlaps are removed explicitly
before applying the constructed ℓ¹ embedding and retraction. -/
noncomputable section
open MeasureTheory Set Filter Function
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}

theorem exists_disjoint_measurable_lOne_supports
    (f : ℕ → Lp 𝕜 1 μ)
    (hd : Pairwise fun i j => ∀ᵐ x ∂μ, f i x = 0 ∨ f j x = 0) :
    ∃ A : ℕ → Set X, ∃ hA : ∀ n, MeasurableSet (A n),
      Pairwise (Disjoint on A) ∧ ∀ n, lpCut (A n) (hA n) (f n) = f n := by
  let B : ℕ → Set X := fun n => Function.support (f n)
  let A := disjointed B
  have hA : ∀ n, MeasurableSet (A n) :=
    MeasurableSet.disjointed fun n => (Lp.stronglyMeasurable (f n)).measurableSet_support
  refine ⟨A, hA, disjoint_disjointed B, ?_⟩
  intro n
  have hg : ∀ᵐ x ∂μ, ∀ j, n ≠ j → f n x = 0 ∨ f j x = 0 := by
    apply ae_all_iff.mpr
    intro j
    by_cases hnj : n = j
    · exact Eventually.of_forall fun _ h => False.elim (h hnj)
    · exact (hd hnj).mono fun x hx _ => hx
  apply Lp.ext
  filter_upwards [lpCut_coe (A n) (hA n) (f n), hg] with x hcut hx
  rw [hcut]
  by_cases hfn : f n x = 0
  · simp [hfn]
  · have hxA : x ∈ A n := by
      change x ∈ disjointed B n
      rw [disjointed_eq_inter_compl]
      refine ⟨hfn, mem_iInter₂.mpr fun j hj => ?_⟩
      simpa only [B, Set.mem_compl_iff, Function.mem_support, not_not] using
        (hx j (Ne.symm (Nat.ne_of_lt hj))).resolve_left hfn
    exact Set.indicator_of_mem hxA (f n)

theorem exists_lOne_ae_disjoint_isometric_retraction
    (f : ℕ → Lp 𝕜 1 μ)
    (hd : Pairwise fun i j => ∀ᵐ x ∂μ, f i x = 0 ∨ f j x = 0)
    (hnorm : ∀ n, ‖f n‖ = 1) :
    ∃ V : lp (fun _ : ℕ => 𝕜) 1 →ₗᵢ[𝕜] Lp 𝕜 1 μ,
      ∃ U : Lp 𝕜 1 μ →L[𝕜] lp (fun _ : ℕ => 𝕜) 1,
        (∀ n, V (lp.single 1 n 1) = f n) ∧
        U.comp V.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 _ ∧
        ‖U‖ ≤ 1 ∧ ‖V.toContinuousLinearMap‖ = 1 := by
  obtain ⟨A, hA, hdis, hf⟩ := exists_disjoint_measurable_lOne_supports f hd
  exact exists_lOne_disjoint_isometric_retraction f A hA hdis hf hnorm

theorem exists_lOne_norm_disjoint_isometric_retraction
    (f : ℕ → Lp 𝕜 1 μ)
    (hd : Pairwise fun i j => ∀ᵐ x ∂μ, min ‖f i x‖ ‖f j x‖ = 0)
    (hnorm : ∀ n, ‖f n‖ = 1) :
    ∃ V : lp (fun _ : ℕ => 𝕜) 1 →ₗᵢ[𝕜] Lp 𝕜 1 μ,
      ∃ U : Lp 𝕜 1 μ →L[𝕜] lp (fun _ : ℕ => 𝕜) 1,
        (∀ n, V (lp.single 1 n 1) = f n) ∧
        U.comp V.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 _ ∧
        ‖U‖ ≤ 1 ∧ ‖V.toContinuousLinearMap‖ = 1 := by
  apply exists_lOne_ae_disjoint_isometric_retraction f _ hnorm
  intro i j hij
  filter_upwards [hd hij] with x hx
  by_cases hi : f i x = 0
  · exact Or.inl hi
  · right
    by_contra hj
    have hp := lt_min (norm_pos_iff.mpr hi) (norm_pos_iff.mpr hj)
    rw [hx] at hp
    exact (lt_irrefl 0) hp

end ThesisCommon
