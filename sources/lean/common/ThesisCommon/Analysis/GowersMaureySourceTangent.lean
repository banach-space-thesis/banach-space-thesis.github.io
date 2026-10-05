import ThesisCommon.Analysis.GowersMaureyLogExterior
import ThesisCommon.Analysis.GowersMaureyRapidProducts
import ThesisCommon.Analysis.ExtendedReciprocalProfile

/-! The exterior tangent criterion on the actual construction sizes.
At the first size the central interval starts at one; at every later
size rapid growth supplies the double-logarithmic lower cutoff. -/
noncomputable section
namespace ThesisCommon.GowersMaurey.ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜] (D : ConstructionData 𝕜)

theorem log_size_large (n : ℕ) : (127 : ℝ) < Real.log (D.j n : ℝ) := by
  have hs := D.one_le_size n
  have hsp : (0 : ℝ) < D.j n := by exact_mod_cast D.j_positive n
  have hLp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hw : (256 : ℝ) < logarithmicWeight (D.j n : ℝ) :=
    D.first_large.trans_le (logarithmicWeight_strictMonoOn.monotoneOn
      (D.one_le_size 0) hs (by exact_mod_cast D.j_strict.monotone (Nat.zero_le n)))
  have hlog := Real.log_le_log (by linarith : 0 < (D.j n : ℝ) + 1)
    (show (D.j n : ℝ) + 1 ≤ 2 * D.j n by linarith)
  rw [Real.log_mul (by norm_num) hsp.ne'] at hlog
  unfold logarithmicWeight at hw
  have hc := (lt_div_iff₀ hLp).mp hw
  nlinarith [log_two_half_le]

theorem loglog_size_ge_sixty_four {n : ℕ} (hn : n ≠ 0) :
    (64 : ℝ) ≤ Real.log (Real.log (D.j n : ℝ)) := by
  have he := D.exp_twice_size_lt_loglog (m := 0) (n := n) (Nat.pos_of_ne_zero hn)
  have h0 := D.size_large 0
  have hb := Real.add_one_le_exp (2 * (D.j 0 : ℝ))
  linarith

theorem logarithmicProfileTangent_concaveOn {s : ℝ} (hs : 1 ≤ s) :
    ConcaveOn ℝ (Set.Ici 0) (logarithmicProfileTangent s) := by
  have hh := (concaveOn_const (c := logarithmicProfileIntercept s) (convex_Ici (0 : ℝ))).add
    (ConcaveOn.smul (logarithmicProfileSlope_nonneg hs)
      (concaveOn_id (convex_Ici (0 : ℝ))))
  simpa only [logarithmicProfileTangent, Pi.add_apply, smul_eq_mul, id_eq] using hh

theorem extended_sqrtProfile_le_tangent_outside_gap {n : ℕ} {s x : ℝ}
    (hs : s ∈ Set.Icc (Real.log (D.j n : ℝ)) (Real.exp (D.j n : ℝ)))
    (_hx : 0 ≤ x)
    (hout : x ∉ Set.Icc
      (if n = 0 then 1 else Real.log (Real.log (D.j n : ℝ)))
      (Real.exp (Real.exp (D.j n : ℝ)))) :
    ThesisCommon.extendedReciprocalProfile (fun t => Real.sqrt (logarithmicWeight t)) x ≤
      logarithmicProfileTangent s x := by
  have hs16 : 16 ≤ s := by have hh := D.log_size_large n; linarith [hs.1]
  have hs1 : 1 ≤ s := by linarith
  by_cases hx1 : x ≤ 1
  · rw [ThesisCommon.extendedReciprocalProfile, if_pos hx1]
    exact logarithmicProfileTangent_ge_identity_below_one hs1 hx1
  · have hx1p : 1 < x := lt_of_not_ge hx1
    rw [ThesisCommon.extendedReciprocalProfile, if_neg hx1]
    change sqrtLogarithmicProfile x ≤ logarithmicProfileTangent s x
    have hN64 : (64 : ℝ) ≤ D.j n := by have hh := D.size_large n; linarith
    by_cases hxlo : x < (if n = 0 then 1 else Real.log (Real.log (D.j n : ℝ)))
    · have hn : n ≠ 0 := by
        intro hn
        have hh : x < 1 := by simpa [hn] using hxlo
        exact (not_lt_of_ge hx1p.le) hh
      rw [if_neg hn] at hxlo
      exact sqrtLogarithmicProfile_le_tangent_below_log_log hN64 hs1 hs.1
        (D.loglog_size_ge_sixty_four hn) hx1p.le hxlo.le
    · have hxhi : Real.exp (Real.exp (D.j n : ℝ)) < x :=
        lt_of_not_ge (fun hh => hout ⟨le_of_not_gt hxlo, hh⟩)
      exact sqrtLogarithmicProfile_le_tangent_above_exp_exp hN64 hs16 hs.2 hxhi.le

end ThesisCommon.GowersMaurey.ConstructionData
