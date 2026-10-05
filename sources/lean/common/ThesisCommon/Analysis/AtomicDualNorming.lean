import ThesisCommon.Analysis.AtomicDualSeries
import ThesisCommon.Analysis.CountableCoefficientCodes
import ThesisCommon.Analysis.NormingSequence

/-! A countable norming family and an ell-one model of the dual yield a
countable norming family made of normalized coordinate functionals. An
optional zero coordinate treats empty index sets without extra hypotheses. -/
noncomputable section
namespace ThesisCommon
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dualAtomScale (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1) : ℝ :=
  max 1 ‖d.symm.toContinuousLinearMap‖

theorem dualAtomScale_pos (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1) :
    0 < dualAtomScale d := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

def normalizedDualAtom (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1) :
    Option I → (E →L[ℝ] ℝ)
  | none => 0
  | some i => (dualAtomScale d)⁻¹ • dualAtom d i

theorem normalizedDualAtom_norm_le (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (i : Option I) : ‖normalizedDualAtom d i‖ ≤ 1 := by
  cases i with
  | none => simp only [normalizedDualAtom,norm_zero,zero_le_one]
  | some i =>
    change ‖(dualAtomScale d)⁻¹ • dualAtom d i‖ ≤ 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (dualAtomScale_pos d))]
    calc
      _ ≤ (dualAtomScale d)⁻¹ * dualAtomScale d := mul_le_mul_of_nonneg_left
        ((dualAtom_norm_le d i).trans (le_max_right _ _)) (inv_nonneg.mpr (dualAtomScale_pos d).le)
      _ = 1 := inv_mul_cancel₀ (dualAtomScale_pos d).ne'

theorem dualAtomScale_mul_normalized (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (i : I) (x : E) :
    dualAtomScale d * |normalizedDualAtom d (some i) x| = |dualAtom d i x| := by
  change dualAtomScale d * |(dualAtomScale d)⁻¹ * dualAtom d i x| = _
  rw [abs_mul,abs_of_pos (inv_pos.mpr (dualAtomScale_pos d)),← mul_assoc,
    mul_inv_cancel₀ (dualAtomScale_pos d).ne',one_mul]

theorem exists_norming_dual_atoms
    (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (e : ℕ → E →L[ℝ] ℝ) (he : IsNorming e) :
    ∃ q : ℕ → Option I, IsNorming (fun n => normalizedDualAtom d (q n)) := by
  classical
  obtain ⟨c,hc⟩ := he
  let S : Set I := ⋃ n, Function.support (d (e n))
  have hS : S.Countable := Set.countable_iUnion (fun n => lp_one_countable_support (d (e n)))
  obtain ⟨q,hq⟩ := Set.countable_iff_exists_subset_range.mp (hS.image Option.some)
  let f : ℕ → E →L[ℝ] ℝ := fun n => normalizedDualAtom d (q n)
  have hf (n : ℕ) : ‖f n‖ ≤ 1 := normalizedDualAtom_norm_le d (q n)
  let L := max 1 ‖d.toContinuousLinearMap‖
  let M := dualAtomScale d
  have hL1 : 1 ≤ L := le_max_left _ _
  have hM1 : 1 ≤ M := le_max_left _ _
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hM : 0 < M := dualAtomScale_pos d
  have hLM : 0 < L*M := mul_pos hL hM
  have hLM1 : 1 ≤ L*M := by nlinarith
  have hd (n : ℕ) : ‖d (e n)‖ ≤ L := by
    calc
      _ ≤ ‖d.toContinuousLinearMap‖ * ‖e n‖ := d.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖d.toContinuousLinearMap‖ * 1 :=
        mul_le_mul_of_nonneg_left (hc.2.2.1 n) (norm_nonneg d.toContinuousLinearMap)
      _ ≤ L := by rw [mul_one]; exact le_max_right _ _
  refine ⟨q,c/(L*M),div_pos hc.1 hLM,(div_le_one hLM).mpr (hc.2.1.trans hLM1),hf,?_⟩
  intro x
  have hb := evaluations_bddAbove f hf x
  have hsup0 : 0 ≤ ⨆ n, |f n x| := (abs_nonneg _).trans (le_ciSup hb 0)
  have hbound (n : ℕ) : |e n x| ≤ (L*M) * (⨆ k, |f k x|) := by
    have hatom (i : I) (hi : d (e n) i ≠ 0) : |dualAtom d i x| ≤ M * (⨆ k, |f k x|) := by
      obtain ⟨k,hk⟩ := hq ⟨i,Set.mem_iUnion.mpr ⟨n,hi⟩,rfl⟩
      have hki : M * |f k x| = |dualAtom d i x| := by
        change dualAtomScale d * |normalizedDualAtom d (q k) x| = _
        rw [hk]
        exact dualAtomScale_mul_normalized d i x
      have ht := mul_le_mul_of_nonneg_left (le_ciSup hb k) hM.le
      rwa [hki] at ht
    calc
      _ ≤ ‖d (e n)‖ * (M * (⨆ k, |f k x|)) := dualAtom_evaluation_bound d (e n) x _ hatom
      _ ≤ L * (M * (⨆ k, |f k x|)) :=
        mul_le_mul_of_nonneg_right (hd n) (mul_nonneg hM.le hsup0)
      _ = (L*M) * (⨆ k, |f k x|) := (mul_assoc _ _ _).symm
  have hnorm := (hc.2.2.2 x).trans (ciSup_le hbound)
  change c/(L*M) * ‖x‖ ≤ ⨆ n, |f n x|
  rw [div_mul_eq_mul_div,div_le_iff₀ hLM]
  nlinarith

end ThesisCommon
