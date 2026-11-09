import PEMS.Section44Decomposition
import ThesisCommon.Analysis.DualLattice

/-! The adjoint-at-one representative and its essential supremum on a
strictly localizable domain, including uncountable partitions. -/
noncomputable section
open MeasureTheory Set Filter ThesisCommon
open scoped ENNReal Function Classical ThesisCommon.PositiveOperatorOrder ThesisCommon.DualLattice

namespace PEMS

variable {I X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
set_option maxHeartbeats 1200000

/-- The Riesz--Kantorovich value of the modulus of the actual Banach adjoint
at the constant-one functional. -/
theorem section44_adjoint_modulus_at_one (U : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    let one := linftyL1Pairing ν (linftyOne ν)
    IsLUB (banachAdjoint U '' Icc (-one) one) (banachAdjoint |U| one) := by
  let one := linftyL1Pairing ν (linftyOne ν)
  have hone (g : LOne ℝ ν) (hg : 0 ≤ g) : one g = ‖g‖ := by
    rw [show one = linftyL1Pairing ν (linftyOne ν) from rfl, linftyL1Pairing_one]
    change L1.integralCLM g = _
    rw [← L1.integral_def, L1.integral_eq_integral, lOne_norm_eq_integral_of_nonneg g hg]
  change IsLUB (banachAdjoint U '' Icc (-one) one) (banachAdjoint |U| one)
  constructor
  · rintro _ ⟨φ, hφ, rfl⟩ f hf
    have hmod : dualModulus φ ≤ one := by
      apply dualModulus_least
      intro g hg
      have hlo := hφ.1 g hg
      have hhi := hφ.2 g hg
      change -one g ≤ φ g at hlo
      exact abs_le.mpr ⟨hlo, hhi⟩
    change φ (U f) ≤ one (|U| f)
    calc
      _ ≤ |φ (U f)| := le_abs_self _
      _ ≤ dualModulus φ |U f| := dualModulus_abs_dominates φ (U f)
      _ ≤ one |U f| := hmod _ (abs_nonneg _)
      _ = ‖U f‖ := (hone _ (abs_nonneg _)).trans (norm_abs_eq_norm _)
      _ ≤ ‖|U| f‖ := by
        have hm : |U f| ≤ |U| f := by
          simpa only [abs_of_nonneg hf, ← abs_lOneOperator_eq] using lOneOperatorModulus_dominates U f
        exact (norm_abs_eq_norm _).symm.trans_le
          (norm_le_norm_of_abs_le_abs (by
            simpa only [abs_abs, abs_of_nonneg ((abs_nonneg U) f hf)] using hm))
      _ = _ := (hone _ ((abs_nonneg U) f hf)).symm
  · intro ψ hψ f hf
    have hbound (g : LOne ℝ μ) (hg : 0 ≤ g) : ‖U g‖ ≤ ψ g := by
      obtain ⟨φ, hφ, hφg⟩ := exists_dual_vector'' ℝ (U g)
      have hmem : φ ∈ Icc (-one) one := by
        constructor <;> intro z hz
        · change -one z ≤ φ z
          rw [hone z hz]
          exact (neg_le_neg ((φ.le_opNorm z).trans (by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hφ (norm_nonneg z)))).trans
              (neg_abs_le _)
        · rw [hone z hz]
          exact (le_abs_self _).trans ((φ.le_opNorm z).trans (by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hφ (norm_nonneg z)))
      have hh := hψ (show banachAdjoint U φ ∈ banachAdjoint U '' Icc (-one) one from ⟨φ, hmem, rfl⟩) g hg
      change φ (U g) ≤ ψ g at hh
      rwa [hφg] at hh
    have hne : (modulusCandidates U f).Nonempty :=
      ⟨_, ⟨PositiveDecomposition.single f hf, rfl⟩⟩
    have hpos : ∀ z ∈ modulusCandidates U f, 0 ≤ z := by
      rintro _ ⟨d, rfl⟩
      exact d.value_nonneg U
    have hbdd : BddAbove (norm '' modulusCandidates U f) := by
      refine ⟨‖U‖ * ‖f‖, ?_⟩
      rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
      exact d.norm_value_le (lOne_norm_add_of_nonneg μ) U
    obtain ⟨w, hw, u, hu, hlim, _⟩ := al_exists_isLUB_of_directed_norm_bdd
      (lOne_norm_add_of_nonneg ν) hne hpos (modulusCandidates_directed U f) hbdd
    have heq : w = |U| f := by
      rw [abs_lOneOperator_eq, lOneOperatorModulus, operatorModulus_apply_of_nonneg _ _ _ _ hf]
      exact hw.unique (operatorModulusPos_isLUB _ _ _ _ hf)
    change one (|U| f) ≤ ψ f
    rw [hone _ ((abs_nonneg U) f hf), ← heq]
    apply le_of_tendsto' hlim.norm
    intro n
    obtain ⟨d, hd⟩ := hu n
    rw [← hd]
    change ‖∑ j, |U (d.part j)|‖ ≤ ψ f
    calc
      _ ≤ ∑ j, ‖|U (d.part j)|‖ := norm_sum_le _ _
      _ = ∑ j, ‖U (d.part j)‖ := by simp only [norm_abs_eq_norm]
      _ ≤ ∑ j, ψ (d.part j) := Finset.sum_le_sum fun j _ => hbound _ (d.nonneg j)
      _ = ψ f := by rw [← map_sum, d.sum_eq]

namespace Section44Partition

variable (D : Section44Partition I μ)

theorem ae_on_pieces {p : X → Prop} (hp : MeasurableSet {x | p x}) :
    (∀ᵐ x ∂μ, p x) ↔ ∀ i, ∀ᵐ x ∂μ.restrict (D.piece i), p x := by
  calc
    _ ↔ (∀ᵐ x ∂Measure.sum (fun i => μ.restrict (D.piece i)), p x) := by rw [D.sum_restrict]
    _ ↔ _ := Measure.ae_sum_iff' hp

theorem paste_ae (f : I → X → ℝ) (i : I) :
    D.paste f =ᵐ[μ.restrict (D.piece i)] f i :=
  (ae_restrict_mem (D.measurable i)).mono (fun _ hx => D.paste_eq f hx)

theorem piece_nonneg {U : LOne ℝ μ →L[ℝ] LOne ℝ ν}
    (hU : 0 ≤ U) (i : I) : 0 ≤ U.comp (D.includePiece i) :=
  fun f hf => hU _ (lebesgueL1Extend_nonneg (D.piece i) (D.measurable i) f hf)

def adjointDensity (U : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hU : 0 ≤ U) : X → ℝ :=
  D.paste (fun i => positiveAdjointOneDensity (U.comp (D.includePiece i)) (D.piece_nonneg hU i))

theorem measurable_adjointDensity (U : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hU : 0 ≤ U) :
    Measurable (D.adjointDensity U hU) :=
  D.measurable_paste _ fun _ => measurable_positiveAdjointOneDensity _ _

theorem adjointDensity_piece (U : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hU : 0 ≤ U) (i : I) :
    D.adjointDensity U hU =ᵐ[μ.restrict (D.piece i)]
      positiveAdjointOneDensity (U.comp (D.includePiece i)) (D.piece_nonneg hU i) :=
  D.paste_ae _ i

theorem adjointDensity_bounds (U : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hU : 0 ≤ U) (x : X) :
    0 ≤ D.adjointDensity U hU x ∧ D.adjointDensity U hU x ≤ ‖U‖ := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (D.covers ▸ mem_univ x)
  change 0 ≤ D.paste _ x ∧ D.paste _ x ≤ _
  rw [D.paste_eq _ hi]
  obtain ⟨h₁, h₂⟩ := positiveAdjointOneDensity_bounds
    (U.comp (D.includePiece i)) (D.piece_nonneg hU i) x
  exact ⟨h₁, h₂.trans (D.norm_comp_piece_le U i)⟩

def adjointOne (U : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hU : 0 ≤ U) : Lp ℝ ∞ μ :=
  (memLp_top_of_bound (D.measurable_adjointDensity U hU).aestronglyMeasurable ‖U‖
    (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (D.adjointDensity_bounds U hU x).1]
      exact (D.adjointDensity_bounds U hU x).2)).toLp (D.adjointDensity U hU)

theorem adjointOne_coe (U : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hU : 0 ≤ U) :
    D.adjointOne U hU =ᵐ[μ] D.adjointDensity U hU :=
  MemLp.coeFn_toLp _

theorem adjointOne_pairing (U : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hU : 0 ≤ U) :
    linftyL1Pairing μ (D.adjointOne U hU) =
      banachAdjoint U (linftyL1Pairing ν (linftyOne ν)) := by
  let F := linftyL1Pairing μ (D.adjointOne U hU)
  let G := banachAdjoint U (linftyL1Pairing ν (linftyOne ν))
  have hpiece (i : I) (f : LOne ℝ (μ.restrict (D.piece i))) :
      F (D.includePiece i f) = G (D.includePiece i f) := by
    let Ui := U.comp (D.includePiece i)
    let hi := D.piece_nonneg hU i
    have hμ : D.adjointOne U hU =ᵐ[μ.restrict (D.piece i)] D.adjointDensity U hU :=
      ae_restrict_of_ae (D.adjointOne_coe U hU)
    have hcoe : D.adjointOne U hU =ᵐ[μ.restrict (D.piece i)] positiveAdjointOne Ui hi :=
      hμ.trans ((D.adjointDensity_piece U hU i).trans (positiveAdjointOne_coe Ui hi).symm)
    have hleft : F (D.includePiece i f) = linftyL1Pairing _ (positiveAdjointOne Ui hi) f := by
      rw [show F = linftyL1Pairing μ (D.adjointOne U hU) from rfl, linftyL1Pairing_apply,
        linftyL1Pairing_apply, ← integral_indicator (D.measurable i)]
      apply integral_congr_ae
      filter_upwards [lebesgueLpExtend_coe (𝕜 := ℝ) (D.piece i) (D.measurable i) f,
        (ae_restrict_iff' (D.measurable i)).mp hcoe] with x hx hx'
      change D.adjointOne U hU x * lebesgueLpExtend (𝕜 := ℝ) (D.piece i) (D.measurable i) f x = _
      rw [hx]
      by_cases h : x ∈ D.piece i <;> simp [h, hx']
    rw [hleft, positiveAdjointOne_pairing]
    rfl
  apply ContinuousLinearMap.ext
  intro f
  have hs := decomposableLp_hasSum_extensions (𝕜 := ℝ) (by norm_num)
    D.piece D.measurable D.disjoint D.sum_restrict f
  let fPiece (i : I) := D.includePiece i (lebesgueLpRestrict (𝕜 := ℝ) (D.piece i) f)
  have hF : HasSum (fun i => F (fPiece i)) (F f) := hs.map F F.continuous
  have hG : HasSum (fun i => G (fPiece i)) (G f) := hs.map G G.continuous
  rw [show (fun i => G (fPiece i)) = (fun i => F (fPiece i)) from
    funext (fun i => (hpiece i _).symm)] at hG
  exact hF.unique hG

theorem norm_le_iff_adjointDensity (U : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hU : 0 ≤ U)
    {c : ℝ} (hc : 0 ≤ c) :
    ‖U‖ ≤ c ↔ ∀ᵐ x ∂μ, D.adjointDensity U hU x ≤ c := by
  rw [D.norm_le_iff_pieces U hc, D.ae_on_pieces (measurableSet_le
    (D.measurable_adjointDensity U hU) measurable_const)]
  constructor
  · intro h i
    filter_upwards [D.adjointDensity_piece U hU i,
      (norm_positive_le_iff_adjointDensity (D.piece_nonneg hU i) hc).mp (h i)] with x hx hb
    rwa [hx]
  · intro h i
    apply (norm_positive_le_iff_adjointDensity (D.piece_nonneg hU i) hc).mpr
    filter_upwards [D.adjointDensity_piece U hU i, h i] with x hx hb
    rwa [hx] at hb

theorem norm_adjointOne (U : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hU : 0 ≤ U) :
    ‖D.adjointOne U hU‖ = ‖U‖ := by
  apply le_antisymm
  · apply linfty_norm_le_of_ae_bound _ (norm_nonneg _)
    filter_upwards [D.adjointOne_coe U hU] with x hx
    rw [hx, Real.norm_of_nonneg (D.adjointDensity_bounds U hU x).1]
    exact (D.adjointDensity_bounds U hU x).2
  · apply (D.norm_le_iff_adjointDensity U hU (norm_nonneg _)).mpr
    filter_upwards [D.adjointOne_coe U hU, linfty_ae_norm_le_norm (D.adjointOne U hU)]
      with x hx hbound
    rw [← hx]
    exact (le_abs_self _).trans hbound

theorem norm_eq_essSup_adjointDensity (U : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hU : 0 ≤ U) :
    ‖U‖ = essSup (D.adjointDensity U hU) μ := by
  rw [← D.norm_adjointOne U hU]
  exact (linfty_norm_eq_essSup_of_nonneg _ (by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [D.adjointOne_coe U hU] with x hx
    rw [hx]
    exact (D.adjointDensity_bounds U hU x).1)).trans (essSup_congr_ae (D.adjointOne_coe U hU))

end Section44Partition

end PEMS
