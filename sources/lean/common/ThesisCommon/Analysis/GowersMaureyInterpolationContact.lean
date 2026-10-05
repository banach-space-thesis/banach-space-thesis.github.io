import ThesisCommon.Analysis.GowersMaureyInterpolationBarriers
import ThesisCommon.Analysis.GowersMaureyLogTangent
import ThesisCommon.Analysis.ConcaveEnvelopeContact

/-! The contact step for the actual interpolation profile. A logarithmic
tangent controls the central interval by concavity and the complement by
the square-root-logarithmic barrier. Numerical exterior estimates are
kept separate from this exact envelope argument. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem logarithmicProfileTangent_concaveOn (s : ℝ) :
    ConcaveOn ℝ (Set.Ici 0) (logarithmicProfileTangent s) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [logarithmicProfileTangent, smul_eq_mul]
  have he : a * (logarithmicProfileIntercept s + logarithmicProfileSlope s * x) +
      b * (logarithmicProfileIntercept s + logarithmicProfileSlope s * y) =
      logarithmicProfileIntercept s + logarithmicProfileSlope s * (a * x + b * y) := by
    calc
      _ = (a + b) * logarithmicProfileIntercept s +
        logarithmicProfileSlope s * (a * x + b * y) := by ring
      _ = _ := by rw [hab, one_mul]
  exact he.le

theorem interpolationG_eq_logarithmicProfile_of_tangent
    (K : Set ℕ) {I : Set ℝ} {s : ℝ} (hs : 1 ≤ s) (hsI : s ∈ I)
    (hgap : ∀ t, 1 ≤ t → t ∈ I →
      submultiplicativeHull (interpolationSeed K) t = logarithmicWeight t)
    (hsmall : ∀ t, 0 ≤ t → t ≤ 1 → t ≤ logarithmicProfileTangent s t)
    (houtside : ∀ t, 1 ≤ t → t ∉ I →
      sqrtLogarithmicProfile t ≤ logarithmicProfileTangent s t) :
    interpolationG K s = logarithmicProfile s := by
  let H := extendedReciprocalProfile (submultiplicativeHull (interpolationSeed K))
  have hφ : ∀ t, 1 ≤ t → 1 ≤ interpolationSeed K t := fun _ ht => interpolationSeed_ge_one K ht
  have hh : ∀ t, 1 ≤ t → 1 ≤ submultiplicativeHull (interpolationSeed K) t :=
    fun t _ => one_le_submultiplicativeHull hφ t
  have hone : submultiplicativeHull (interpolationSeed K) 1 = 1 :=
    submultiplicativeHull_one hφ (interpolationSeed_one K).le
  have hH0 : ∀ t, 0 ≤ t → 0 ≤ H t := fun _ ht => extendedReciprocalProfile_nonneg hh ht
  have hH1 : ∀ t, 0 ≤ t → H t ≤ t := fun _ ht => extendedReciprocalProfile_le_id hh ht
  have hHT : ∀ t, 0 ≤ t → H t ≤ logarithmicProfileTangent s t := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · exact (extendedReciprocalProfile_of_le ht1).le.trans (hsmall t ht ht1)
    · have htge : 1 ≤ t := (lt_of_not_ge ht1).le
      by_cases htI : t ∈ I
      · change extendedReciprocalProfile _ t ≤ _
        rw [extendedReciprocalProfile_of_one_le hone htge, hgap t htge htI]
        exact logarithmicProfile_le_tangent hs htge
      · have hHG : H t ≤ interpolationG K t := le_positiveConcaveEnvelope hH0 hH1 ht
        have hGU := interpolationG_le_extended_sqrtLogarithmicProfile K ht
        rw [extendedReciprocalProfile_of_one_le (by simp [logarithmicWeight_one]) htge] at hGU
        exact hHG.trans (hGU.trans (houtside t htge htI))
  have hHs : H s = logarithmicProfile s := by
    change extendedReciprocalProfile _ s = _
    rw [extendedReciprocalProfile_of_one_le hone hs, hgap s hs hsI]
    rfl
  have heq := positiveConcaveEnvelope_eq_of_contact hH0 hH1
    (logarithmicProfileTangent_concaveOn s) hHT (zero_le_one.trans hs)
    ((logarithmicProfileTangent_contact (zero_lt_one.trans_le hs)).trans hHs.symm)
  exact heq.trans hHs

theorem interpolationProfile_eq_weight_of_tangent
    (K : Set ℕ) {I : Set ℝ} {s : ℝ} (hs : 1 ≤ s) (hsI : s ∈ I)
    (hgap : ∀ t, 1 ≤ t → t ∈ I →
      submultiplicativeHull (interpolationSeed K) t = logarithmicWeight t)
    (hsmall : ∀ t, 0 ≤ t → t ≤ 1 → t ≤ logarithmicProfileTangent s t)
    (houtside : ∀ t, 1 ≤ t → t ∉ I →
      sqrtLogarithmicProfile t ≤ logarithmicProfileTangent s t) :
    interpolationProfile K s = logarithmicWeight s := by
  have heq := interpolationG_eq_logarithmicProfile_of_tangent K hs hsI hgap hsmall houtside
  change s / interpolationG K s = _
  rw [heq, logarithmicProfile]
  field_simp [(zero_lt_one.trans_le hs).ne']

end ThesisCommon.GowersMaurey
