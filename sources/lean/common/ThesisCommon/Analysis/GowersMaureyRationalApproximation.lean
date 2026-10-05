import ThesisCommon.Analysis.GowersMaureyForms
import ThesisCommon.Analysis.GowersMaureyRationalContractions

/-! Gaussian-rational density on a fixed finite support, over every RCLike
field. The approximation uses the actual coefficient mass seminorm. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem RationalCoordinate.zero : RationalCoordinate (0 : 𝕜) := ⟨0, 0, by simp⟩

theorem RationalCoordinate.add {a b : 𝕜} (ha : RationalCoordinate a)
    (hb : RationalCoordinate b) : RationalCoordinate (a + b) := by
  obtain ⟨r,s,rfl⟩ := ha
  obtain ⟨t,u,rfl⟩ := hb
  refine ⟨r+t,s+u,?_⟩
  simp only [Rat.cast_add]
  ring

theorem RationalCoordinate.sum {ι : Type*} (s : Finset ι) (a : ι → 𝕜)
    (ha : ∀ i ∈ s, RationalCoordinate (a i)) : RationalCoordinate (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (RationalCoordinate.zero (𝕜 := 𝕜))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (ha i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

theorem exists_rationalCoordinate_near (a : 𝕜) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : 𝕜, RationalCoordinate b ∧ ‖b - a‖ < ε := by
  obtain ⟨r,hr0,hr1⟩ := exists_rat_btwn
    (show RCLike.re a - ε/2 < RCLike.re a + ε/2 by linarith)
  obtain ⟨s,hs0,hs1⟩ := exists_rat_btwn
    (show RCLike.im a - ε/2 < RCLike.im a + ε/2 by linarith)
  refine ⟨(r : 𝕜) + (s : 𝕜) * RCLike.I, ⟨r,s,rfl⟩, ?_⟩
  have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
    by_cases h : (RCLike.I : 𝕜) = 0
    · simp [h]
    · exact (RCLike.norm_I_of_ne_zero h).le
  have he : (r : 𝕜) + (s : 𝕜) * RCLike.I - a =
      (((r : ℝ) - RCLike.re a : ℝ) : 𝕜) +
        (((s : ℝ) - RCLike.im a : ℝ) : 𝕜) * RCLike.I := by
    nth_rw 1 [← RCLike.re_add_im a]
    simp only [RCLike.ofReal_sub, RCLike.ofReal_ratCast]
    ring
  rw [he]
  calc
    _ ≤ ‖(((r : ℝ) - RCLike.re a : ℝ) : 𝕜)‖ +
        ‖(((s : ℝ) - RCLike.im a : ℝ) : 𝕜) * RCLike.I‖ := norm_add_le _ _
    _ ≤ |(r : ℝ) - RCLike.re a| + |(s : ℝ) - RCLike.im a| := by
      rw [norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal]
      exact add_le_add_left (mul_le_of_le_one_right (abs_nonneg _) hI) _
    _ < ε := by
      have hr : |(r : ℝ) - RCLike.re a| < ε/2 := abs_lt.mpr ⟨by linarith, by linarith⟩
      have hs : |(s : ℝ) - RCLike.im a| < ε/2 := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith

theorem mass_eq_sum_of_support_subset (a : C00 𝕜) (s : Finset ℕ)
    (ha : a.support ⊆ s) : mass a = ∑ n ∈ s, ‖a n‖ := by
  rw [mass_eq]
  exact Finset.sum_subset ha (fun n _ hn => by
    rw [Finsupp.notMem_support_iff.mp hn, norm_zero])

theorem exists_rational_finsupp_near (a : C00 𝕜) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : C00 𝕜, (∀ n, RationalCoordinate (b n)) ∧
      b.support ⊆ a.support ∧ mass (b-a) < ε := by
  classical
  let η : ℝ := ε / (a.support.card + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  choose g hg hgerr using fun n => exists_rationalCoordinate_near (a n) hη
  let b : C00 𝕜 := Finsupp.onFinset a.support
    (fun n => if n ∈ a.support then g n else 0) (by
      intro n hn
      by_contra h
      simp [h] at hn)
  have hb (n : ℕ) : b n = if n ∈ a.support then g n else 0 := rfl
  have hbs : b.support ⊆ a.support := by
    intro n hn
    by_contra h
    exact Finsupp.mem_support_iff.mp hn (by simp [hb, h])
  refine ⟨b, (fun n => ?_), hbs, ?_⟩
  · rw [hb]
    split_ifs
    · exact hg n
    · exact RationalCoordinate.zero
  · have hs : (b-a).support ⊆ a.support :=
      Finsupp.support_sub.trans (Finset.union_subset hbs Finset.Subset.rfl)
    rw [mass_eq_sum_of_support_subset _ _ hs]
    calc
      _ ≤ ∑ n ∈ a.support, η := Finset.sum_le_sum (fun n hn => by
        simpa [Finsupp.sub_apply, hb, hn] using (hgerr n).le)
      _ = a.support.card * η := by simp
      _ < ε := by
        have he : η * (a.support.card + 1) = ε := div_mul_cancel₀ ε (by positivity)
        nlinarith

theorem pairing_add_left (a b x : C00 𝕜) : pairing (a+b) x = pairing a x + pairing b x := by
  have he : pairing (a+b) = pairing a + pairing b := by
    apply Finsupp.lhom_ext
    intro n c
    simp [add_mul]
  exact DFunLike.congr_fun he x

theorem pairing_apply_sum (a x : C00 𝕜) :
    pairing a x = ∑ n ∈ x.support, a n * x n := by
  simp [pairing, Finsupp.lsum_apply, Finsupp.sum, smul_eq_mul]

theorem pairing_comm (a x : C00 𝕜) : pairing a x = pairing x a := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp [pairing_apply_sum]
  | add a b ha hb => rw [pairing_add_left, map_add, ha, hb]
  | single n c =>
      rw [pairing_single, pairing_apply_sum, Finset.sum_eq_single n]
      · simp [mul_comm]
      · intro j _ hj
        simp [Ne.symm hj]
      · intro hn
        simp [Finsupp.notMem_support_iff.mp hn]

theorem pairing_norm_le_mass_mul_implicitNorm (D : ConstructionData 𝕜) (a x : C00 𝕜) :
    ‖pairing a x‖ ≤ mass a * implicitNorm D x := by
  rw [pairing_comm]
  simpa only [mul_comm] using
    pairing_norm_le_mass (coordinate_le_implicitNorm D x) a

end ThesisCommon.GowersMaurey
