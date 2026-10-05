import ThesisCommon.Analysis.ConcavePerspectiveBound
import Mathlib.Analysis.Convex.Jensen

/-! The finite Jensen and perspective estimates in the interval induction
of Gowers--Maurey, Section 2, Lemma 3. These are real inequalities, with
every profile and numerical hypothesis explicit. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey

theorem concave_sum_le_card_mul {ι : Type*} {G : ℝ → ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 0) G) (hmono : MonotoneOn G (Set.Ici 0))
    (S : Finset ι) (hS : S.Nonempty) (u : ι → ℝ) (hu : ∀ i ∈ S, 0 ≤ u i)
    {w : ℝ} (hsum : (∑ i ∈ S, u i) ≤ w) :
    (∑ i ∈ S, G (u i)) ≤ (S.card : ℝ) * G (w / S.card) := by
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have h := hG.le_map_sum (t := S) (w := fun _ => (S.card : ℝ)⁻¹) (p := u)
    (fun _ _ => inv_nonneg.mpr hcard.le)
    (by simp [ne_of_gt hcard]) hu
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  have hsum0 : 0 ≤ ∑ i ∈ S, u i := Finset.sum_nonneg hu
  have hw : 0 ≤ w := hsum0.trans hsum
  calc
    (∑ i ∈ S, G (u i)) = (S.card : ℝ) * ((S.card : ℝ)⁻¹ * ∑ i ∈ S, G (u i)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcard), one_mul]
    _ ≤ (S.card : ℝ) * G ((S.card : ℝ)⁻¹ * ∑ i ∈ S, u i) := mul_le_mul_of_nonneg_left h hcard.le
    _ ≤ (S.card : ℝ) * G (w / S.card) := by
      apply mul_le_mul_of_nonneg_left _ hcard.le
      apply hmono (mul_nonneg (inv_nonneg.mpr hcard.le) hsum0) (div_nonneg hw hcard.le)
      simpa only [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcard.le)

/-- The numerical step after dividing intervals into s small pieces and
m remaining pieces. Here k=s+m, alpha=1/g(k), G(k)=k/g(k). -/
theorem concave_two_class_estimate {G : ℝ → ℝ} {d : ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 0) G) (hG1 : G 1 = 1)
    (hsupport : ∀ u, 1 ≤ u → G u ≤ 1 + d * (u - 1))
    (hmul : ∀ r s, 0 ≤ r → 0 ≤ s → G r * G s ≤ G (r * s))
    {s m k α b C w : ℝ} (hs : 0 ≤ s) (hm : 0 < m) (hkm : k = m + s)
    (hα1 : α ≤ 1) (hαk : α * k = G k)
    (hb : 0 ≤ b) (hkb : k * b ≤ 1 - d) (hC : 1 ≤ C) (hw : 1 ≤ w) :
    α * (s * b + C * m * G (w / m)) ≤ C * G w := by
  have hk : 0 < k := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hd : 0 ≤ 1 - d := (mul_nonneg hk.le hb).trans hkb
  let t := s / k
  have ht : 0 ≤ t := div_nonneg hs hk.le
  have ht1 : t < 1 := by dsimp [t]; apply (div_lt_one hk).mpr; linarith
  have hmt : m / k = 1 - t := by dsimp [t]; field_simp; linarith
  have hsmall : α * s * b ≤ C * (t * (1 - d)) := by
    calc
      α * s * b ≤ s * b := by nlinarith [mul_nonneg hs hb]
      _ = t * (k * b) := by dsimp [t]; field_simp
      _ ≤ t * (1 - d) := mul_le_mul_of_nonneg_left hkb ht
      _ ≤ _ := le_mul_of_one_le_left (mul_nonneg ht hd) hC
  have harg : k * (w / m) = w / (1 - t) := by
    rw [← hmt]
    field_simp
  have hlarge : α * C * m * G (w / m) ≤ C * ((1 - t) * G (w / (1 - t))) := by
    calc
      _ = C * (m / k) * (G k * G (w / m)) := by
        rw [← hαk]
        field_simp
      _ ≤ C * (m / k) * G (k * (w / m)) :=
        mul_le_mul_of_nonneg_left (hmul k (w / m) hk.le (div_nonneg (by linarith) hm.le))
          (mul_nonneg hC0 (div_nonneg hm.le hk.le))
      _ = _ := by rw [hmt, harg]; ring
  have hG' : ConcaveOn ℝ (Set.Ici 1) G :=
    hG.subset (by intro u hu; change 0 ≤ u; exact zero_le_one.trans (show 1 ≤ u from hu))
      (convex_Ici 1)
  have hpers := concave_perspective_le_of_support hG' hG1 hsupport hw ht ht1
  calc
    _ = α * s * b + α * C * m * G (w / m) := by ring
    _ ≤ C * (t * (1 - d)) + C * ((1 - t) * G (w / (1 - t))) := add_le_add hsmall hlarge
    _ = C * ((1 - t) * G (w / (1 - t)) + t * (1 - d)) := by ring
    _ ≤ C * G w := mul_le_mul_of_nonneg_left hpers hC0

end ThesisCommon.GowersMaurey
