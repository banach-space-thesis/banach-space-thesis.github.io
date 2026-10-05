import ThesisCommon.Analysis.GowersMaureyOneExceptionFormsEnvelope
import ThesisCommon.Analysis.GowersMaureyActualRISProfile
import ThesisCommon.Analysis.GowersMaureyConstructionProfileGap

/-! The actual RIS norm estimate with one exceptional special size.
The exceptional tests have a strict affine norm budget; every other form
uses the genuine interpolation profile with that size removed. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem RISData.sum_norm_le_one_exception_interpolation
    {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ} {x : Fin N → C00 𝕜}
    (h : RISData D ε x) (k : ℕ) {B θ : ℝ} (hθ : θ < 1) (hB : B < 1-θ)
    (hexception : ∀ z : Fin k → C00 𝕜, SpecialSequence D (implicitNorm D) z →
      ∀ m n E F, ‖pairing (specialFunctional z)
        (GowersMaurey.restrict E (spread m n (GowersMaurey.restrict F (∑ i, x i))))‖ ≤
        B+θ*implicitNorm D (GowersMaurey.restrict F (∑ i, x i))) :
    implicitNorm D (∑ i, x i) ≤
      (1+2*ε)*interpolationG (D.specialSizes \ {k}) N := by
  let K := D.specialSizes \ {k}
  let g : ℕ → ℝ := fun l => interpolationProfile K l
  have hg : ∀ l : ℕ, 2 ≤ l → Real.sqrt (logarithmicWeight l) ≤ g l := by
    intro l hl
    exact interpolationProfile_ge_sqrt K (by exact_mod_cast (show 1 ≤ l by omega))
  have hgpos : ∀ l, 2 ≤ l → 0 < g l := by
    intro l hl
    exact (zero_lt_one.trans_le (one_le_sqrt_logarithmicWeight
      (by exact_mod_cast (show 1 ≤ l by omega)))).trans_le (hg l hl)
  have hgf : ∀ l : ℕ, 2 ≤ l → g l ≤ logarithmicWeight l := by
    intro l hl
    exact interpolationProfile_le_weight K (by exact_mod_cast (show 1 ≤ l by omega))
  have hgs : ∀ l, l ∈ D.specialSizes → l ≠ k → g l ≤ Real.sqrt (logarithmicWeight l) := by
    intro l hl hne
    exact interpolationProfile_le_sqrt_at_selected_size K
      (by have := D.specialSize_ge_two hl; omega) ⟨hl, hne⟩
  apply h.sum_norm_le_of_support (interpolationG K) g
    (interpolationG_concaveOn K) (interpolationG_monotoneOn K)
    (fun s hs hs1 => interpolationG_small K hs hs1) interpolation_support_slope_nonneg
    (fun s hs => interpolationG_support K hs) (by linarith)
    (fun r s hr hs => interpolationG_mul_le K hr hs) hg
    (fun l hl => interpolationProfile_inverse_mul K (by exact_mod_cast hl))
  intro F r hr hn
  refine exists_norming_form_of_affine_exception_bound D g k hgpos hgf hgs
    (GowersMaurey.restrict F (∑ i, x i)) ?_ hn (hr.trans_lt hn) hθ hB ?_
  · intro n
    rw [restrict_apply]
    split_ifs
    · exact (h.sum_coordinate_le_one n).trans hr
    · simpa only [norm_zero] using zero_le_one.trans hr
  · intro z hz m n E
    exact hexception z hz m n E F

theorem ConstructionData.interpolationG_omit_size (D : ConstructionData 𝕜) (t : ℕ) :
    interpolationG (D.specialSizes \ {D.j (2*t)}) (D.j (2*t)) =
      (D.j (2*t) : ℝ)/logarithmicWeight (D.j (2*t)) := by
  let K := D.specialSizes \ {D.j (2*t)}
  have hv := D.interpolationProfile_eq_on_gap K (fun _ h => h.1) (2*t)
    (by simp [K]) (s := (D.j (2*t) : ℝ))
    ⟨Real.log_le_self (Nat.cast_nonneg _),
      (by linarith [Real.add_one_le_exp (D.j (2*t) : ℝ)])⟩
  have hi := interpolationProfile_inverse_mul K
    (show 1 ≤ (D.j (2*t) : ℝ) by exact_mod_cast D.j_positive _)
  rw [hv] at hi
  simpa only [K, div_eq_mul_inv, mul_comm] using hi.symm

end ThesisCommon.GowersMaurey
