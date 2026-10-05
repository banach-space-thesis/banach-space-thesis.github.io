import ThesisCommon.Analysis.ALFragmentConditionalIncrement
import ThesisCommon.Analysis.ALFragmentOrderCompleteness

/-! Exact conditional division inside a homogeneous fragment. Chain upper
bounds are actual norm limits of finite fragment joins. A maximal fragment
under the prescribed measurable conditional budget exhausts that budget,
because every nonzero residual admits a genuine small conditional increment. -/
noncomputable section
open MeasureTheory Set Filter Topology
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]

omit [CompleteSpace E] [OrderClosedTopology E] in
theorem continuous_alFragmentConditionalMass
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e)) :
    Continuous (alFragmentConditionalMass hAL e S) :=
  (lOneSubsigmaProjection (alFragmentMeasure hAL e)
    (booleanSubalgebraStoneMeasurableSpace_le S)).continuous.comp
      (isometry_alFragmentIndicator hAL e).continuous

/-- Every measurable conditional budget below the mass of a fragment is
realized exactly by a subfragment, including the zero budget. -/
theorem homogeneous_exists_exact_conditional_mass
    {a : PositiveFragmentAlgebra e} (ha : IsDensityHomogeneous a)
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (hden : topologicalDensity S < principalDensity a)
    (b : PositiveFragmentAlgebra e) (hba : b ≤ a)
    (g : Lp ℝ 1 (alFragmentMeasure hAL e))
    (hg : AEStronglyMeasurable[booleanSubalgebraStoneMeasurableSpace S]
      g (alFragmentMeasure hAL e))
    (hg0 : 0 ≤ g) (hgb : g ≤ alFragmentConditionalMass hAL e S b) :
    ∃ z : PositiveFragmentAlgebra e, z ≤ b ∧
      alFragmentConditionalMass hAL e S z = g := by
  classical
  let M := alFragmentConditionalMass hAL e S
  have hM0 : M ⊥ = 0 := (alFragmentConditionalMass_eq_zero_iff hAL e S ⊥).mpr rfl
  let s : Set (PositiveFragmentAlgebra e) := {z | z ≤ b ∧ M z ≤ g}
  have hchain : ∀ c ⊆ s, IsChain (· ≤ ·) c →
      ∃ d ∈ s, ∀ z ∈ c, z ≤ d := by
    intro c hcs hc
    obtain ⟨d, hd, F, hF, hlim⟩ := positiveFragment_exists_isLUB_finset_limit hAL c
    have hjoin (n : ℕ) : (F n).sup id ∈ insert ⊥ c := by
      have hsup : ∀ x ∈ insert ⊥ c, ∀ y ∈ insert ⊥ c, x ⊔ y ∈ insert ⊥ c := by
        intro x hx y hy
        rcases hx with rfl | hx
        · simpa only [bot_sup_eq] using hy
        rcases hy with rfl | hy
        · simpa only [sup_bot_eq] using (mem_insert_of_mem ⊥ hx)
        rcases hc.total hx hy with hxy | hyx
        · rw [sup_eq_right.mpr hxy]
          exact mem_insert_of_mem ⊥ hy
        · rw [sup_eq_left.mpr hyx]
          exact mem_insert_of_mem ⊥ hx
      exact Finset.sup_mem (insert ⊥ c) (mem_insert _ _) hsup (F n) id
        (fun z hz => mem_insert_of_mem ⊥ (hF n hz))
    have hbound (n : ℕ) : M ((F n).sup id) ≤ g := by
      rcases hjoin n with hz | hz
      · simpa only [hz, hM0] using hg0
      · exact (hcs hz).2
    have hlim' : Tendsto (fun n => (F n).sup id) atTop (𝓝 d) :=
      (isometry_positiveFragmentValue e).isEmbedding.tendsto_nhds_iff.mpr hlim
    refine ⟨d, ⟨hd.2 (fun z hz => (hcs hz).1), ?_⟩, fun z hz => hd.1 hz⟩
    exact le_of_tendsto' ((continuous_alFragmentConditionalMass hAL e S).tendsto d |>.comp hlim')
      hbound
  obtain ⟨z, hz, hmax⟩ := zorn_le₀ s hchain
  refine ⟨z, hz.1, ?_⟩
  by_contra hne
  have hpart : z ⊔ (b \ z) = b := sup_sdiff_cancel_right hz.1
  have hdisj : Disjoint z (b \ z) := disjoint_sdiff_self_right
  have hMpart : M z + M (b \ z) = M b := by
    exact (alFragmentConditionalMass_sup_of_disjoint hAL e S z (b \ z) hdisj).symm.trans
      (congrArg M hpart)
  have hres : M (b \ z) = M b - M z := by rw [← hMpart]; abel
  have hgsub : AEStronglyMeasurable[booleanSubalgebraStoneMeasurableSpace S]
      (g - M z) (alFragmentMeasure hAL e) :=
    (lOneSubsigma (alFragmentMeasure hAL e) (booleanSubalgebraStoneMeasurableSpace S)).sub_mem
      hg (alFragmentConditionalMass_aestronglyMeasurable hAL e S z)
  have hgsub0 : 0 ≤ g - M z := sub_nonneg.mpr hz.2
  have hgsuble : g - M z ≤ M (b \ z) := by
    rw [hres]
    exact sub_le_sub_right hgb (M z)
  have hgsubne : g - M z ≠ 0 := fun hh => hne (sub_eq_zero.mp hh).symm
  obtain ⟨w, hw0, hwr, hMw⟩ := homogeneous_exists_small_conditional_increment hAL e ha S hS
    hden (b \ z) (sdiff_le.trans hba) (g - M z) hgsub hgsub0 hgsuble hgsubne
  have hzw : Disjoint z w := hdisj.mono_right hwr
  have hsum : z ⊔ w ∈ s := by
    refine ⟨sup_le hz.1 (hwr.trans sdiff_le), ?_⟩
    change alFragmentConditionalMass hAL e S (z ⊔ w) ≤ g
    rw [alFragmentConditionalMass_sup_of_disjoint hAL e S z w hzw]
    exact add_le_of_le_sub_left hMw
  have hwy : w ≤ z := le_sup_right.trans (hmax hsum le_sup_left)
  exact hw0 (disjoint_self.mp (hzw.mono_left hwy))

end ThesisCommon
