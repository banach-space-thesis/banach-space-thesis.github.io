import ThesisCommon.Analysis.GowersMaureyFormIntervals
import ThesisCommon.Analysis.GowersMaureyConcavePartition

/-! The minimal-interval argument in source Lemma 3, on the actual norm.
All numerical profile assumptions and the source's local form-norming
condition are explicit. No property of the eventual operator quotient is
an assumption. Empty intervals and a form with a full-size piece are handled. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem interval_norm_le_of_forms_and_measure (D : ConstructionData 𝕜) (x : C00 𝕜)
    (A : Interval) (G : ℝ → ℝ) (g : ℕ → ℝ) {d b C K q : ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 0) G) (hmono : MonotoneOn G (Set.Ici 0))
    (hsmallG : ∀ t, 0 ≤ t → t ≤ 1 → G t = t) (hd : 0 ≤ d)
    (hsupport : ∀ u, 1 ≤ u → G u ≤ 1 + d * (u - 1))
    (hmul : ∀ r s, 0 ≤ r → 0 ≤ s → G r * G s ≤ G (r * s))
    (hq : 1 < q) (hg : ∀ k, 2 ≤ k → q ≤ g k)
    (hgprofile : ∀ k, 2 ≤ k → (g k)⁻¹ * k = G k)
    (hb : 0 ≤ b) (hbudget : ∀ k : ℕ, 2 ≤ k → (k : ℝ) < K → (k : ℝ) * b ≤ 1 - d)
    (hC : 1 ≤ C) (μ : ℕ → ℝ) (hμ : ∀ n, 0 ≤ μ n)
    (hdom : ∀ E : Interval, E.set ⊆ A.set → b < implicitNorm D (restrict E x) →
      implicitNorm D (restrict E x) ≤ ∑ n ∈ E.set, μ n)
    (hnorm : ∀ E : Interval, E.set ⊆ A.set → ∀ r : ℝ, 1 ≤ r →
      r < implicitNorm D (restrict E x) →
      ∃ k : ℕ, 2 ≤ k ∧ ∃ a : C00 𝕜, IsForm D k (g k) a ∧ r < ‖pairing a (restrict E x)‖)
    (hlarge : ∀ E : Interval, E.set ⊆ A.set → ∀ k : ℕ, 2 ≤ k → K ≤ k →
      ∀ a : C00 𝕜, IsForm D k (g k) a → ‖pairing a (restrict E x)‖ ≤ C) :
    ∀ E : Interval, E.set ⊆ A.set → b < implicitNorm D (restrict E x) →
      implicitNorm D (restrict E x) ≤ C * G (∑ n ∈ E.set, μ n) := by
  classical
  have hG1 : G 1 = 1 := hsmallG 1 (by norm_num) le_rfl
  have hC0 : 0 ≤ C := by linarith
  have hq0 : 0 < q := by linarith
  suffices hh : ∀ n : ℕ, ∀ E : Interval, E.set.card = n → E.set ⊆ A.set →
      b < implicitNorm D (restrict E x) →
      implicitNorm D (restrict E x) ≤ C * G (∑ n ∈ E.set, μ n) by
    intro E hEA hEb
    exact hh E.set.card E rfl hEA hEb
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E hcard hEA hEb
    by_contra hbad
    let v := implicitNorm D (restrict E x)
    let w := ∑ n ∈ E.set, μ n
    have hv0 : 0 ≤ v := apply_nonneg _ _
    have hvw : v ≤ w := hdom E hEA hEb
    have hw0 : 0 ≤ w := hv0.trans hvw
    have hbad' : C * G w < v := lt_of_not_ge hbad
    have hv1 : 1 < v := by
      by_contra hv
      have hv' : v ≤ 1 := le_of_not_gt hv
      have hGv : v ≤ G w := by
        rw [← hsmallG v hv0 hv']
        exact hmono hv0 hw0 hvw
      have hh := hGv.trans (le_mul_of_one_le_left (hv0.trans hGv) hC)
      exact (not_lt_of_ge hh) hbad'
    have hw1 : 1 ≤ w := hv1.le.trans hvw
    have hGw1 : 1 ≤ G w := by rw [← hG1]; exact hmono (by norm_num) hw0 hw1
    have hCw : C ≤ C * G w := by nlinarith
    have hvq : v / q < v := by
      apply (div_lt_iff₀ hq0).mpr
      nlinarith
    let r := max (C * G w) (v / q)
    have hr1 : 1 ≤ r := hC.trans (hCw.trans (le_max_left _ _))
    have hrv : r < v := max_lt_iff.mpr ⟨hbad', hvq⟩
    obtain ⟨k, hk, a, ha, hra⟩ := hnorm E hEA r hr1 hrv
    have hg0 : 0 < g k := hq0.trans_le (hg k hk)
    have hkK : (k : ℝ) < K := by
      by_contra hkk
      have hbnd := hlarge E hEA k hk (le_of_not_gt hkk) a ha
      have hCr : C ≤ r := hCw.trans (le_max_left _ _)
      exact (not_lt_of_ge (hbnd.trans hCr)) hra
    obtain ⟨I, hIE, hIa⟩ := ha.exists_interval_decomposition E x
    have hproper : ∀ i, (I.interval i).set ≠ E.set := by
      intro i hfull
      have hbnd : ‖pairing a (restrict E x)‖ ≤ v / q := by
        calc
          _ ≤ (g k)⁻¹ * intervalSum D I x := hIa
          _ = (g k)⁻¹ * v := by rw [I.intervalSum_eq_of_full hIE hfull D x]
          _ ≤ q⁻¹ * v := mul_le_mul_of_nonneg_right
            ((inv_le_inv₀ hg0 hq0).mpr (hg k hk)) hv0
          _ = v / q := by ring
      exact (not_lt_of_ge (hbnd.trans (le_max_right _ _))) hra
    let u (i : Fin k) := ∑ n ∈ (I.interval i).set, μ n
    let y (i : Fin k) := implicitNorm D (restrict (I.interval i) x)
    let S := Finset.univ.filter (fun i => y i ≤ b)
    have hylarge : ∀ i, i ∉ S → y i ≤ C * G (u i) := by
      intro i hi
      have hbi : b < y i := by
        exact lt_of_not_ge (fun hle => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩))
      have hlt : (I.interval i).set.card < n := by
        rw [← hcard]
        exact Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨hIE i, hproper i⟩)
      exact ih (I.interval i).set.card hlt (I.interval i) rfl ((hIE i).trans hEA) hbi
    have hnumeric : (g k)⁻¹ * ∑ i, y i ≤ C * G w :=
      concave_partition_sum_estimate hG hmono hG1 hd hsupport hmul
        (inv_nonneg.mpr hg0.le) (inv_le_one_of_one_le₀ (hq.le.trans (hg k hk)))
        (hgprofile k hk) hb (hbudget k hk hkK) hC hw1 u y
        (fun i => Finset.sum_nonneg fun j _ => hμ j) (I.sum_mass_le hIE μ hμ) S
        (fun i hi => (Finset.mem_filter.mp hi).2) hylarge
    have hfinal : ‖pairing a (restrict E x)‖ ≤ C * G w := by
      apply hIa.trans
      rw [intervalSum_apply]
      exact hnumeric
    exact (not_lt_of_ge (hfinal.trans (le_max_left _ _))) hra

end ThesisCommon.GowersMaurey
