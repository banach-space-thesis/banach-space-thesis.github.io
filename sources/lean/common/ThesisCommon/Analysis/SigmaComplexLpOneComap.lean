import ThesisCommon.Analysis.SigmaComplexCoefficientOperators

noncomputable section
namespace ThesisCommon

abbrev complexLpOneComap {ι κ : Type*} (e : ι ↪ κ) (f : lp (fun _ : κ => ℂ) 1) :
    lp (fun _ : ι => ℂ) 1 := lpRestrict (𝕜 := ℂ) 1 e f

@[simp] theorem complexLpOneComap_apply {ι κ : Type*} (e : ι ↪ κ)
    (f : lp (fun _ : κ => ℂ) 1) (i : ι) : complexLpOneComap e f i = f (e i) := rfl

theorem complexLpOneComap_norm_le {ι κ : Type*} (e : ι ↪ κ) (f : lp (fun _ : κ => ℂ) 1) :
    ‖complexLpOneComap e f‖ ≤ ‖f‖ := by
  rw [← (complexLpOneHasSumNorm (complexLpOneComap e f)).tsum_eq,
    ← (complexLpOneHasSumNorm f).tsum_eq]
  exact tsum_comp_le_tsum_of_inj (complexLpOneHasSumNorm f).summable
    (fun _ => norm_nonneg _) e.injective

end ThesisCommon

