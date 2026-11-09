import CKEUPFP.CotypeNoCZero
import CKEUPFP.LpDominatedConvergence
import ThesisCommon.Analysis.RademacherFirstMoment
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# No scalar c₀ in finite-exponent Lp

Finite signed sums of the images of the c₀ unit vectors have one norm bound.
The scalar first-moment Khintchine inequality bounds their finite square
functions by a finite average of those signed sums. Fatou gives an Lp square
envelope; domination then forces the coordinate images to tend to zero.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace CKEUPFP

open ThesisCommon ThesisCommon.Grothendieck

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The real/complex first-moment estimate, adapted from the scalar lemma
in the user's `ThesisCommon/Analysis/EllOneCotype.lean`. -/
theorem scalar_rademacher_second_le_nine_first_sq {n : ℕ} (a : Fin n → 𝕜) :
    (∑ i, ‖a i‖ ^ 2) ≤
      9 * mean (fun ε : Fin n → Bool => ‖∑ i, signedValue (ε i) (a i)‖) ^ 2 := by
  let R (ε : Fin n → Bool) := ∑ i, signedValue (ε i) (a i)
  let A := mean (fun ε => ‖R ε‖)
  have hre (ε : Fin n → Bool) : rademacher (fun i => RCLike.re (a i)) ε = RCLike.re (R ε) := by
    simp only [rademacher, R, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases ε i <;> simp [signedValue]
  have him (ε : Fin n → Bool) : rademacher (fun i => RCLike.im (a i)) ε = RCLike.im (R ε) := by
    simp only [rademacher, R, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases ε i <;> simp [signedValue]
  have hAr : mean (fun ε => |RCLike.re (R ε)|) ≤ A :=
    mean_mono fun ε => by simpa only [Real.norm_eq_abs] using RCLike.norm_re_le_norm (R ε)
  have hAi : mean (fun ε => |RCLike.im (R ε)|) ≤ A :=
    mean_mono fun ε => by simpa only [Real.norm_eq_abs] using RCLike.norm_im_le_norm (R ε)
  have hr := rademacher_second_le_three_first_sq (fun i => RCLike.re (a i))
  have hi := rademacher_second_le_three_first_sq (fun i => RCLike.im (a i))
  simp only [hre] at hr
  simp only [him] at hi
  have hsr := sq_le_sq₀ (mean_nonneg fun ε => abs_nonneg _) (mean_nonneg fun ε => norm_nonneg _) |>.mpr hAr
  have hsi := sq_le_sq₀ (mean_nonneg fun ε => abs_nonneg _) (mean_nonneg fun ε => norm_nonneg _) |>.mpr hAi
  have heq : (∑ i, ‖a i‖ ^ 2) = (∑ i, RCLike.re (a i) ^ 2) +
      ∑ i, RCLike.im (a i) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [pow_two] using (RCLike.norm_sq_eq_def (z := a i))
  change (∑ i, ‖a i‖ ^ 2) ≤ 9 * A ^ 2
  rw [heq]
  nlinarith [sq_nonneg A]

theorem scalar_square_function_le_three_mean {n : ℕ} (a : Fin n → 𝕜) :
    Real.sqrt (∑ i, ‖a i‖ ^ 2) ≤
      3 * mean (fun ε : Fin n → Bool => ‖∑ i, signedValue (ε i) (a i)‖) := by
  have h := scalar_rademacher_second_le_nine_first_sq a
  have hs := Real.sq_sqrt (show 0 ≤ ∑ i : Fin n, ‖a i‖ ^ 2 from
    Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hm := mean_nonneg (fun ε : Fin n → Bool =>
    norm_nonneg (∑ i, signedValue (ε i) (a i)))
  nlinarith [Real.sqrt_nonneg (∑ i, ‖a i‖ ^ 2)]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}

theorem eLpNorm_finiteMean_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (g : Ω → α → ℝ) (hg : ∀ ω, AEStronglyMeasurable (g ω) μ)
    (hp : 1 ≤ p) {R : ℝ≥0∞} (hR : ∀ ω, eLpNorm (g ω) p μ ≤ R) :
    eLpNorm (fun x => mean (fun ω => g ω x)) p μ ≤ R := by
  classical
  have hc : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard0 : (Fintype.card Ω : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : eLpNorm (∑ ω, g ω) p μ ≤ (Fintype.card Ω : ℝ≥0∞) * R := by
    calc
      _ ≤ ∑ ω, eLpNorm (g ω) p μ := eLpNorm_sum_le (fun ω _ => hg ω) hp
      _ ≤ ∑ _ω : Ω, R := Finset.sum_le_sum (fun ω _ => hR ω)
      _ = _ := by simp
  have heq : (fun x => mean (fun ω => g ω x)) =
      (Fintype.card Ω : ℝ)⁻¹ • (∑ ω, g ω) := by
    funext x
    simp [mean]
  rw [heq, eLpNorm_const_smul]
  rw [Real.enorm_eq_ofReal (inv_nonneg.mpr hc.le), ENNReal.ofReal_inv_of_pos hc]
  simp only [ENNReal.ofReal_natCast]
  exact (mul_le_mul_left' hsum _).trans_eq
    (ENNReal.inv_mul_cancel_left hcard0 (by simp))

/-- Square function of the first n scalar functions. -/
def scalarSquarePartial (f : ℕ → α → 𝕜) (n : ℕ) (x : α) : ℝ :=
  Real.sqrt (∑ i : Fin n, ‖f i.val x‖ ^ 2)

/-- The extended supremum prevents an unbounded square function being
silently replaced by zero. It is proved finite almost everywhere below. -/
def scalarSquareSup (f : ℕ → α → 𝕜) (x : α) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (scalarSquarePartial f n x)

def scalarSquareEnvelope (f : ℕ → α → 𝕜) (x : α) : ℝ :=
  (scalarSquareSup f x).toReal

theorem measurable_scalarSquarePartial (f : ℕ → α → 𝕜)
    (hf : ∀ n, StronglyMeasurable (f n)) (n : ℕ) :
    Measurable (scalarSquarePartial f n) := by
  exact (Finset.measurable_sum Finset.univ
    (fun (i : Fin n) _ => ((hf i.val).norm.measurable).pow_const 2)).sqrt

theorem measurable_scalarSquareEnvelope (f : ℕ → α → 𝕜)
    (hf : ∀ n, StronglyMeasurable (f n)) : Measurable (scalarSquareEnvelope f) :=
  (Measurable.iSup (fun n => (measurable_scalarSquarePartial f hf n).ennreal_ofReal)).ennreal_toReal

omit [MeasurableSpace α] in
theorem monotone_scalarSquarePartial (f : ℕ → α → 𝕜) (x : α) :
    Monotone (fun n => scalarSquarePartial f n x) := by
  intro n m hnm
  change Real.sqrt (∑ i : Fin n, ‖f i.val x‖ ^ 2) ≤
    Real.sqrt (∑ i : Fin m, ‖f i.val x‖ ^ 2)
  rw [Fin.sum_univ_eq_sum_range (fun i => ‖f i x‖ ^ 2) n,
    Fin.sum_univ_eq_sum_range (fun i => ‖f i x‖ ^ 2) m]
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
    (fun _ _ _ => sq_nonneg _)

theorem eLpNorm_scalarSquarePartial_le (f : ℕ → α → 𝕜)
    (hf : ∀ n, StronglyMeasurable (f n)) (hp : 1 ≤ p)
    {R : ℝ≥0} (hsign : ∀ (n : ℕ) (ε : Fin n → Bool),
      eLpNorm (fun x => ∑ i, signedValue (ε i) (f i.val x)) p μ ≤ R)
    (n : ℕ) : eLpNorm (scalarSquarePartial f n) p μ ≤ (3 * R : ℝ≥0) := by
  let g (ε : Fin n → Bool) (x : α) : ℝ :=
    ‖∑ i, signedValue (ε i) (f i.val x)‖
  have hg : ∀ ε, AEStronglyMeasurable (g ε) μ := by
    intro ε
    apply StronglyMeasurable.aestronglyMeasurable
    apply StronglyMeasurable.norm
    have hm : StronglyMeasurable (∑ i : Fin n, fun x => signedValue (ε i) (f i.val x)) := by
      apply Finset.stronglyMeasurable_sum
      intro i _
      by_cases hε : ε i = true
      · simpa only [signedValue, hε, ite_true] using hf i.val
      · simpa only [signedValue, if_neg hε] using (hf i.val).neg
    convert hm using 1
    funext x
    simp only [Finset.sum_apply]
  have hgR : ∀ ε, eLpNorm (g ε) p μ ≤ R := by
    intro ε
    simpa only [g, eLpNorm_norm] using hsign n ε
  have hmean : eLpNorm (fun x => mean (fun ε => g ε x)) p μ ≤ R :=
    eLpNorm_finiteMean_le g hg hp hgR
  have hbound : ∀ x, ‖scalarSquarePartial f n x‖ ≤
      3 * ‖mean (fun ε => g ε x)‖ := by
    intro x
    rw [scalarSquarePartial, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (mean_nonneg fun ε => norm_nonneg _)]
    exact scalar_square_function_le_three_mean (fun i : Fin n => f i.val x)
  have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (ae_of_all μ hbound) p
  exact h.trans (by simpa using mul_le_mul_left' hmean (3 : ℝ≥0∞))

theorem ae_scalarSquareSup_lt_top (f : ℕ → α → 𝕜)
    (hf : ∀ n, StronglyMeasurable (f n)) (hp : 1 ≤ p)
    {R : ℝ≥0} (hsign : ∀ (n : ℕ) (ε : Fin n → Bool),
      eLpNorm (fun x => ∑ i, signedValue (ε i) (f i.val x)) p μ ≤ R) :
    ∀ᵐ x ∂μ, scalarSquareSup f x < ⊤ := by
  have hb := ae_bdd_liminf_atTop_of_eLpNorm_bdd
    (zero_lt_one.trans_le hp).ne'
    (fun n => measurable_scalarSquarePartial f hf n)
    (fun n => eLpNorm_scalarSquarePartial_le f hf hp hsign n)
  filter_upwards [hb] with x hx
  have heq : (fun n => ‖scalarSquarePartial f n x‖ₑ) =
      (fun n => ENNReal.ofReal (scalarSquarePartial f n x)) := by
    funext n
    exact Real.enorm_eq_ofReal (Real.sqrt_nonneg _)
  rw [heq] at hx
  have hmono : Monotone (fun n => ENNReal.ofReal (scalarSquarePartial f n x)) :=
    fun n m hnm => ENNReal.ofReal_le_ofReal (monotone_scalarSquarePartial f x hnm)
  rw [(tendsto_atTop_iSup hmono).liminf_eq] at hx
  exact hx

omit [MeasurableSpace α] in
theorem scalarSquarePartial_le_envelope (f : ℕ → α → 𝕜) (x : α)
    (hfinite : scalarSquareSup f x ≠ ⊤) (n : ℕ) :
    scalarSquarePartial f n x ≤ scalarSquareEnvelope f x :=
  (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
    (le_iSup (fun k => ENNReal.ofReal (scalarSquarePartial f k x)) n)

omit [MeasurableSpace α] in
theorem tendsto_scalarSquarePartial_of_sup_finite (f : ℕ → α → 𝕜) (x : α)
    (hfinite : scalarSquareSup f x ≠ ⊤) :
    Tendsto (fun n => scalarSquarePartial f n x) atTop (𝓝 (scalarSquareEnvelope f x)) := by
  have hmono : Monotone (fun n => ENNReal.ofReal (scalarSquarePartial f n x)) :=
    fun n m hnm => ENNReal.ofReal_le_ofReal (monotone_scalarSquarePartial f x hnm)
  have h := (ENNReal.tendsto_toReal hfinite).comp (tendsto_atTop_iSup hmono)
  simpa only [Function.comp_def, scalarSquarePartial, scalarSquareEnvelope,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using h

theorem memLp_scalarSquareEnvelope (f : ℕ → α → 𝕜)
    (hf : ∀ n, StronglyMeasurable (f n)) (hp : 1 ≤ p)
    {R : ℝ≥0} (hsign : ∀ (n : ℕ) (ε : Fin n → Bool),
      eLpNorm (fun x => ∑ i, signedValue (ε i) (f i.val x)) p μ ≤ R) :
    MemLp (scalarSquareEnvelope f) p μ := by
  refine ⟨(measurable_scalarSquareEnvelope f hf).stronglyMeasurable.aestronglyMeasurable, ?_⟩
  have ht : ∀ᵐ x ∂μ, Tendsto (fun n => scalarSquarePartial f n x) atTop
      (𝓝 (scalarSquareEnvelope f x)) :=
    (ae_scalarSquareSup_lt_top f hf hp hsign).mono
      (fun x hx => tendsto_scalarSquarePartial_of_sup_finite f x hx.ne)
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p)
    (fun n => (measurable_scalarSquarePartial f hf n).stronglyMeasurable.aestronglyMeasurable)
    (scalarSquareEnvelope f) ht
  exact (hfatou.trans (liminf_le_of_frequently_le'
    (Frequently.of_forall (fun n => eLpNorm_scalarSquarePartial_le f hf hp hsign n)))).trans_lt
    ENNReal.coe_lt_top

omit [MeasurableSpace α] in
theorem square_sum_le_envelope_sq (f : ℕ → α → 𝕜) (x : α)
    (hfinite : scalarSquareSup f x ≠ ⊤) (n : ℕ) :
    (∑ i ∈ Finset.range n, ‖f i x‖ ^ 2) ≤ scalarSquareEnvelope f x ^ 2 := by
  have hle := scalarSquarePartial_le_envelope f x hfinite n
  have hs := Real.sq_sqrt (show 0 ≤ ∑ i : Fin n, ‖f i.val x‖ ^ 2 from
    Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  change (Real.sqrt (∑ i : Fin n, ‖f i.val x‖ ^ 2)) ^ 2 = _ at hs
  rw [Fin.sum_univ_eq_sum_range (fun i => ‖f i x‖ ^ 2) n] at hs
  unfold scalarSquarePartial at hle
  rw [Fin.sum_univ_eq_sum_range (fun i => ‖f i x‖ ^ 2) n] at hle
  have henv : 0 ≤ scalarSquareEnvelope f x := ENNReal.toReal_nonneg
  nlinarith [Real.sqrt_nonneg (∑ i ∈ Finset.range n, ‖f i x‖ ^ 2)]

omit [MeasurableSpace α] in
theorem scalar_norm_le_envelope (f : ℕ → α → 𝕜) (x : α)
    (hfinite : scalarSquareSup f x ≠ ⊤) (n : ℕ) :
    ‖f n x‖ ≤ scalarSquareEnvelope f x := by
  have hterm : ‖f n x‖ ^ 2 ≤ ∑ i ∈ Finset.range (n + 1), ‖f i x‖ ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg ‖f i x‖)
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have hle := hterm.trans (square_sum_le_envelope_sq f x hfinite (n + 1))
  have henv : 0 ≤ scalarSquareEnvelope f x := ENNReal.toReal_nonneg
  nlinarith [norm_nonneg (f n x)]

omit [MeasurableSpace α] in
theorem tendsto_scalar_zero_of_sup_finite (f : ℕ → α → 𝕜) (x : α)
    (hfinite : scalarSquareSup f x ≠ ⊤) :
    Tendsto (fun n => f n x) atTop (𝓝 0) := by
  have hs : Summable (fun n => ‖f n x‖ ^ 2) :=
    summable_of_sum_range_le (fun _ => sq_nonneg _) (square_sum_le_envelope_sq f x hfinite)
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs.tendsto_atTop_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

variable [Fact (1 ≤ p)]

/-- Representatives of an Lp finite sum agree with the pointwise finite sum
almost everywhere. -/
theorem lp_coeFn_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Lp 𝕜 p μ) :
    (fun x => (∑ i ∈ s, f i) x) =ᵐ[μ] (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero 𝕜 p μ
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hx hsum
    simpa only [Pi.add_apply, hsum] using hx

/-- Uniformly bounded finite signed sums of scalar Lp elements force their
norms to tend to zero, including the endpoint p = 1. -/
theorem scalarLp_norm_tendsto_zero_of_sign_bounded (f : ℕ → Lp 𝕜 p μ)
    (hp : p ≠ ∞) {R : ℝ≥0}
    (hsign : ∀ (n : ℕ) (ε : Fin n → Bool),
      ‖∑ i, signedValue (ε i) (f i.val)‖ ≤ R) :
    Tendsto (fun n => ‖f n‖) atTop (𝓝 0) := by
  classical
  let a (n : ℕ) : α → 𝕜 := (Lp.aestronglyMeasurable (f n)).mk (f n)
  have ha : ∀ n, StronglyMeasurable (a n) :=
    fun n => (Lp.aestronglyMeasurable (f n)).stronglyMeasurable_mk
  have haeq : ∀ n, a n =ᵐ[μ] (f n : α → 𝕜) :=
    fun n => (Lp.aestronglyMeasurable (f n)).ae_eq_mk.symm
  have hasign : ∀ (n : ℕ) (ε : Fin n → Bool),
      eLpNorm (fun x => ∑ i, signedValue (ε i) (a i.val x)) p μ ≤ R := by
    intro n ε
    have heq : (fun x => ∑ i, signedValue (ε i) (a i.val x)) =ᵐ[μ]
        (fun x => (∑ i, signedValue (ε i) (f i.val)) x) := by
      have hi : ∀ i : Fin n,
          (fun x => signedValue (ε i) (a i.val x)) =ᵐ[μ]
          (↑(signedValue (ε i) (f i.val) : Lp 𝕜 p μ) : α → 𝕜) := by
        intro i
        cases hε : ε i
        · simpa only [signedValue, hε, Bool.false_eq_true, if_false] using
            (haeq i.val).neg.trans (Lp.coeFn_neg (f i.val)).symm
        · simpa only [signedValue, hε, if_true] using haeq i.val
      have hall : ∀ᵐ x ∂μ, ∀ i : Fin n,
          signedValue (ε i) (a i.val x) = (signedValue (ε i) (f i.val)) x :=
        ae_all_iff.mpr hi
      filter_upwards [hall,
        lp_coeFn_finset_sum Finset.univ (fun i => signedValue (ε i) (f i.val))] with x hx hsum
      exact (Finset.sum_congr rfl (fun i _ => hx i)).trans hsum.symm
    rw [eLpNorm_congr_ae heq, ← Lp.enorm_def]
    exact_mod_cast hsign n ε
  have hfinite := ae_scalarSquareSup_lt_top a ha Fact.out hasign
  have hg := memLp_scalarSquareEnvelope a ha Fact.out hasign
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ scalarSquareEnvelope a x := by
    intro n
    filter_upwards [hfinite, haeq n] with x hx heq
    rw [← heq]
    exact scalar_norm_le_envelope a x hx.ne n
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0) := by
    have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, a n x = f n x := ae_all_iff.mpr haeq
    filter_upwards [hfinite, hall] with x hx heq
    have ht := tendsto_scalar_zero_of_sup_finite a x hx.ne
    simpa only [heq] using ht
  exact lp_norm_tendsto_zero_of_dominated f hp hg hbound hlim

/-- For every measure and every finite Banach exponent, scalar Lp contains
no isomorphic copy of c₀. The proof uses actual coordinate vectors, finite
sign averages, Fatou, and dominated convergence. -/
theorem scalarLp_containsNoCZero (hp : p ≠ ∞) :
    ContainsNoCZero 𝕜 (Lp 𝕜 p μ) := by
  classical
  rintro ⟨J, c, hc, hJ⟩
  let f (n : ℕ) : Lp 𝕜 p μ := J (cZeroUnitVector (𝕜 := 𝕜) n)
  have hsign : ∀ (n : ℕ) (ε : Fin n → Bool),
      ‖∑ i, signedValue (ε i) (f i.val)‖ ≤ ‖J‖₊ := by
    intro n ε
    have heq : (∑ i, signedValue (ε i) (f i.val)) =
        J (∑ i, signedValue (ε i) (cZeroUnitVector (𝕜 := 𝕜) i.val)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      cases ε i <;> simp [signedValue, f]
    rw [heq]
    exact (J.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left (norm_signed_sum_cZeroUnitVector_le ε)
        (norm_nonneg J)).trans_eq (mul_one ‖J‖))
  have ht := scalarLp_norm_tendsto_zero_of_sign_bounded f hp hsign
  have hlower : ∀ n, c ≤ ‖f n‖ := by
    intro n
    simpa only [f, norm_cZeroUnitVector, mul_one] using hJ (cZeroUnitVector (𝕜 := 𝕜) n)
  obtain ⟨n, hn⟩ := ((ht.eventually (gt_mem_nhds hc)).and (Eventually.of_forall hlower)).exists
  exact (not_lt_of_ge hn.2) hn.1

end CKEUPFP
