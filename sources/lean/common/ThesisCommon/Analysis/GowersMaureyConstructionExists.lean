import ThesisCommon.Analysis.GowersMaureyCoding
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Set.Countable
import Mathlib.Data.Fintype.Basic

/-! Existence of the two free choices in the shift-generated Gowers--Maurey
construction: a rapidly growing sequence and a code for rational block lists.
The code is only required to be injective on the actual coding domain.
Gaussian rational coordinates work uniformly for real and complex scalars. -/

noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Finite rational-coordinate sequences form a countable set. -/
theorem countable_rational_sequences :
    Set.Countable {x : C00 𝕜 | ∀ n, RationalCoordinate (x n)} := by
  let f : ℚ × ℚ → 𝕜 := fun q => (q.1 : 𝕜) + (q.2 : 𝕜) * RCLike.I
  have hf : f 0 = 0 := by simp [f]
  have hr : Set.range f = {c : 𝕜 | RationalCoordinate c} := by
    ext c
    simp only [Set.mem_range, Set.mem_setOf_eq, RationalCoordinate]
    constructor
    · rintro ⟨⟨r, s⟩, h⟩
      exact ⟨r, s, h.symm⟩
    · rintro ⟨r, s, h⟩
      exact ⟨(r, s), h.symm⟩
  have h := Set.countable_range (Finsupp.mapRange (α := ℕ) f hf)
  rwa [Finsupp.range_mapRange, hr] at h

/-- Successive lists with rational unit coordinates are countable; neither
the support order nor the unit bound is needed for this countability step. -/
theorem countable_codingDomain : Set.Countable (CodingDomain (𝕜 := 𝕜)) := by
  classical
  let S : Set (C00 𝕜) := {x | ∀ n, RationalCoordinate (x n)}
  haveI : Countable S := countable_rational_sequences
  have h := Set.countable_range (List.map (Subtype.val : S → C00 𝕜))
  apply h.mono
  intro xs hxs
  have hx : ∀ x ∈ xs, x ∈ S := fun x hx => (hxs.1 x hx).1
  clear hxs
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨ys, hys⟩ := ih (fun y hy => hx y (by simp [hy]))
    refine ⟨⟨x, hx x (by simp)⟩ :: ys, ?_⟩
    simp [hys]

/-- The triple logarithm and logarithmic weight can simultaneously exceed
any prescribed finite bounds along the natural numbers. -/
theorem exists_rapid_growth_step (b : ℕ) :
    ∃ n : ℕ, b < n ∧ 256 < logarithmicWeight n ∧
      (2 * b : ℝ) < Real.log (Real.log (Real.log (n : ℝ))) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have htriple : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ))))
      atTop atTop := Real.tendsto_log_atTop.comp
        (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hnat))
  have hweight : Tendsto (fun n : ℕ => logarithmicWeight n) atTop atTop := by
    exact Tendsto.atTop_div_const (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      (Real.tendsto_log_atTop.comp
        (hnat.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))))
  have h := ((eventually_gt_atTop b).and (hweight.eventually_gt_atTop 256)).and
    (htriple.eventually_gt_atTop (2 * b : ℝ))
  obtain ⟨n, hn⟩ := h.exists
  exact ⟨n, hn.1.1, hn.1.2, hn.2⟩

/-- The required infinite growth sequence is obtained by finite-stage choice. -/
theorem exists_rapid_sequence : ∃ j : ℕ → ℕ,
    StrictMono j ∧ (∀ n, 0 < j n) ∧
      (∀ m n, m < n → (2 * j m : ℝ) < Real.log (Real.log (Real.log (j n : ℝ)))) ∧
      256 < logarithmicWeight (j 0) := by
  obtain ⟨j, hj, hrel⟩ := exists_seq_of_forall_finset_exists
    (fun n : ℕ => 0 < n ∧ 256 < logarithmicWeight n)
    (fun m n : ℕ => m < n ∧ (2 * m : ℝ) < Real.log (Real.log (Real.log (n : ℝ))))
    (fun s _ => by
      obtain ⟨n, hn, hw, hr⟩ := exists_rapid_growth_step (s.sup id)
      refine ⟨n, ⟨(Nat.zero_le _).trans_lt hn, hw⟩, ?_⟩
      intro m hm
      have hle : m ≤ s.sup id := Finset.le_sup (f := id) hm
      refine ⟨hle.trans_lt hn, lt_of_le_of_lt ?_ hr⟩
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hle) (by norm_num))
  exact ⟨j, fun _ _ h => (hrel _ _ h).1, fun n => (hj n).1,
    fun _ _ h => (hrel _ _ h).2, (hj 0).2⟩

/-- The literal construction data exist over every `RCLike` scalar field. -/
theorem constructionData_nonempty : Nonempty (ConstructionData 𝕜) := by
  obtain ⟨j, hj, hp, hr, hf⟩ := exists_rapid_sequence
  obtain ⟨code, hcode⟩ := Set.countable_iff_exists_injOn.mp
    (countable_codingDomain (𝕜 := 𝕜))
  refine ⟨{
    j := j
    j_strict := hj
    j_positive := hp
    rapid := hr
    first_large := hf
    sigma := fun xs => j (2 * code xs + 1)
    sigma_injective := ?_
    sigma_even := fun xs _ => ⟨code xs, rfl⟩ }⟩
  intro xs hxs ys hys h
  apply hcode hxs hys
  have he := hj.injective h
  omega

/-- A fixed choice, suitable for defining an unparameterized concrete space. -/
def chosenConstructionData (𝕜 : Type*) [RCLike 𝕜] : ConstructionData 𝕜 :=
  Classical.choice constructionData_nonempty

end ThesisCommon.GowersMaurey
