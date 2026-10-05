import PEMS.KakutaniRepresentation
import PEMS.DisjointOutputWitnessWeis
import ThesisCommon.Analysis.OperatorIsometryTransport
import ThesisCommon.Analysis.L1AEDisjointness
import ThesisCommon.Analysis.ComplexL1CutModulus

/-! Positive disjoint fragments witnessing weak noncompactness on actual
AL spaces. Ordered Kakutani representation transports the constructed
measurable cuts, preserving their norms and domination by the output modulus. -/
noncomputable section
open MeasureTheory Set Filter Topology Function ThesisCommon
namespace PEMS

private def orderedIsometry {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Lattice E] [Lattice F]
    [IsOrderedAddMonoid E] [IsOrderedAddMonoid F]
    (e : E ≃ₗᵢ[ℝ] F) (he : ∀ x, 0 ≤ e x ↔ 0 ≤ x) : E ≃o F where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro x y
    change e x ≤ e y ↔ x ≤ y
    rw [← sub_nonneg, ← map_sub, he, sub_nonneg]

private theorem ae_disjoint_cuts {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X]
    {μ : Measure X} {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hd : Disjoint A B) (f g : Lp 𝕜 1 μ) :
    ∀ᵐ x ∂μ, lpCut A hA f x = 0 ∨ lpCut B hB g x = 0 := by
  filter_upwards [lpCut_coe A hA f, lpCut_coe B hB g] with x hf hg
  by_cases hx : x ∈ A
  · right
    have hxB : x ∉ B := fun h => Set.disjoint_left.mp hd hx h
    simpa [hxB] using hg
  · left
    simpa [hx] using hf

theorem exists_real_AL_disjoint_positiveWitness
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Lattice F] [IsOrderedAddMonoid F] [IsOrderedModule ℝ F] [HasSolidNorm F]
    (T : E →L[ℝ] F) (hE : IsALSpace ℝ E)
    (hF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    (hT : ¬IsWeaklyCompactOperator T) :
    ∃ (x : ℕ → E) (ψ : ℕ → F) (l : ℝ),
      (∀ n, ‖x n‖ = 1) ∧ (∀ n, 0 ≤ ψ n) ∧ (∀ n, ψ n ≤ |T (x n)|) ∧
      (Pairwise fun i j => ψ i ⊓ ψ j = 0) ∧ weakEssentialNorm T ≤ l ∧
      Tendsto (fun n => ‖ψ n‖) atTop (𝓝 l) := by
  obtain ⟨X, mX, μ, hμ, ⟨a⟩⟩ := exists_lOne_representation_of_real_isAL hE
  letI := mX
  obtain ⟨Y, mY, ν, _, b, hb⟩ := exists_ordered_lOne_representation_of_real_AL hF
  letI := mY
  let o := orderedIsometry b hb
  let R := operatorTransport a b T
  have hR : ¬IsWeaklyCompactOperator R :=
    fun h => hT ((weaklyCompact_operatorTransport_iff a b T).mp h)
  obtain ⟨f, A, hA, l, hf, _, hd, hl, ht⟩ :=
    exists_real_disjointOutputWitness_weakEssentialNorm hμ R hR
  let q (n : ℕ) := |lpCut (A n) (hA n) (R (f n))|
  let ψ (n : ℕ) := b.symm (q n)
  have hbψ (n : ℕ) : b (ψ n) = q n := b.apply_symm_apply _
  have hbabs (z : F) : b |z| = |b z| := by
    change o (z ⊔ -z) = b z ⊔ -(b z)
    rw [o.map_sup]
    exact congrArg (fun w => b z ⊔ w) (map_neg b z)
  refine ⟨fun n => a.symm (f n), ψ, l, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [a.symm.norm_map, hf]
  · intro n
    exact (hb (ψ n)).mp (by rw [hbψ]; exact abs_nonneg _)
  · intro n
    apply o.le_iff_le.mp
    change b (ψ n) ≤ b |T (a.symm (f n))|
    rw [hbψ, hbabs]
    change |lpCut (A n) (hA n) (R (f n))| ≤ |R (f n)|
    rw [← lOneCut_abs]
    exact lOneCut_le_self _ _ (abs_nonneg _)
  · intro i j hij
    apply b.injective
    change o (ψ i ⊓ ψ j) = b 0
    rw [o.map_inf]
    change b (ψ i) ⊓ b (ψ j) = b 0
    rw [hbψ, hbψ, map_zero]
    exact lOne_abs_inf_eq_zero_of_ae_disjoint _ _
      (ae_disjoint_cuts (hA i) (hA j) (hd hij) _ _)
  · simpa only [R, weakEssentialNorm_operatorTransport] using hl
  · simpa only [ψ, b.symm.norm_map, q, norm_abs_eq_norm] using ht

theorem exists_complex_AL_disjoint_positiveWitness
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    (T : E →L[ℂ] F) (hE : IsALSpace ℂ E) (B : BanachLatticeModel ℂ F)
    (hB : ∀ x y : B.realForm, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    (hT : ¬IsWeaklyCompactOperator T) :
    ∃ (x : ℕ → E) (ψ : ℕ → B.realForm) (l : ℝ),
      (∀ n, ‖x n‖ = 1) ∧ (∀ n, 0 ≤ ψ n) ∧ (∀ n, ψ n ≤ B.modulus (T (x n))) ∧
      (Pairwise fun i j => ψ i ⊓ ψ j = 0) ∧ weakEssentialNorm T ≤ l ∧
      Tendsto (fun n => ‖ψ n‖) atTop (𝓝 l) := by
  obtain ⟨X, mX, μ, hμ, ⟨a⟩⟩ := exists_lOne_representation_of_complex_isAL hE
  letI := mX
  obtain ⟨Y, mY, ν, _, bR, b, hb, hbmod⟩ := exists_lOne_representation_of_complex_AL_model B hB
  letI := mY
  let o := orderedIsometry bR hb
  let R := operatorTransport a b T
  have hR : ¬IsWeaklyCompactOperator R :=
    fun h => hT ((weaklyCompact_operatorTransport_iff a b T).mp h)
  obtain ⟨f, A, hA, l, hf, _, hd, hl, ht⟩ :=
    exists_complex_disjointOutputWitness_weakEssentialNorm hμ R hR
  let q (n : ℕ) := complexL1Modulus (lpCut (A n) (hA n) (R (f n)))
  let ψ (n : ℕ) := bR.symm (q n)
  have hbψ (n : ℕ) : bR (ψ n) = q n := bR.apply_symm_apply _
  refine ⟨fun n => a.symm (f n), ψ, l, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [a.symm.norm_map, hf]
  · intro n
    exact (hb (ψ n)).mp (by rw [hbψ]; exact complexL1Modulus_nonneg _)
  · intro n
    apply o.le_iff_le.mp
    change bR (ψ n) ≤ bR (B.modulus (T (a.symm (f n))))
    rw [hbψ, ← hbmod]
    change complexL1Modulus (lpCut (A n) (hA n) (R (f n))) ≤ complexL1Modulus (R (f n))
    rw [complexL1Modulus_cut]
    exact lOneCut_le_self _ _ (complexL1Modulus_nonneg _)
  · intro i j hij
    apply bR.injective
    change o (ψ i ⊓ ψ j) = bR 0
    rw [o.map_inf]
    change bR (ψ i) ⊓ bR (ψ j) = bR 0
    rw [hbψ, hbψ, map_zero]
    exact complexL1Modulus_inf_eq_zero_of_ae_disjoint _ _
      (ae_disjoint_cuts (hA i) (hA j) (hd hij) _ _)
  · simpa only [R, weakEssentialNorm_operatorTransport] using hl
  · simpa only [ψ, bR.symm.norm_map, q, norm_complexL1Modulus] using ht

end PEMS
