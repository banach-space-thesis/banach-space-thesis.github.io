import CKEUPFP.NoCZero
import CKEUPFP.OperatorFields
import CKEUPFP.LocalDefect
import CKEUPFP.MainStatements
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Diagonal atoms on Cantor space without representing measures

Clopen cylinders replace metric cutoffs. The no-c₀ hypothesis gives
unconditional convergence on disjoint clopen annuli by `NoCZero.lean`.
This is an equivalent proof route for the atom and localization inputs to
the transfer theorem; no representing-measure theorem is assumed.
-/

noncomputable section

namespace CKEUPFP

open Filter Topology
open scoped BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section ClopenCut
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cutting a continuous function to a clopen set is a bounded linear
operator of norm at most one. -/
def clopenCut (U : Set K) (hU : IsClopen U) : C(K, E) →L[𝕜] C(K, E) :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨U.indicator f,
        continuous_indicator (by simp [hU.frontier_eq]) f.continuous.continuousOn⟩
      map_add' := by
        intro f g
        ext t
        by_cases ht : t ∈ U <;> simp [ht]
      map_smul' := by
        intro c f
        ext t
        by_cases ht : t ∈ U <;> simp [ht] }
    1 (by
      intro f
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro t
      by_cases ht : t ∈ U
      · simpa [ht] using f.norm_coe_le_norm t
      · simp [ht])

@[simp] theorem clopenCut_apply (U : Set K) (hU : IsClopen U)
    (f : C(K, E)) (t : K) :
    clopenCut (𝕜 := 𝕜) U hU f t = U.indicator f t := rfl

theorem norm_clopenCut_le (U : Set K) (hU : IsClopen U) :
    ‖clopenCut (𝕜 := 𝕜) (E := E) U hU‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem norm_clopenCut_apply_le (U : Set K) (hU : IsClopen U) (f : C(K, E)) :
    ‖clopenCut (𝕜 := 𝕜) U hU f‖ ≤ ‖f‖ := by
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_right (norm_clopenCut_le U hU) (norm_nonneg f)).trans_eq
      (one_mul _))

theorem clopenCut_vanishesOff (U : Set K) (hU : IsClopen U) (f : C(K, E)) :
    VanishesOff U (clopenCut (𝕜 := 𝕜) U hU f) := by
  intro t ht
  simp [ht]

theorem clopenCut_eq_of_vanishesOff (U : Set K) (hU : IsClopen U)
    (f : C(K, E)) (hf : VanishesOff U f) :
    clopenCut (𝕜 := 𝕜) U hU f = f := by
  ext t
  by_cases ht : t ∈ U
  · simp [ht]
  · simp [ht, hf t ht]

theorem norm_clopenCut_mono (U V : Set K) (hU : IsClopen U) (hV : IsClopen V)
    (hVU : V ⊆ U) (f : C(K, E)) :
    ‖clopenCut (𝕜 := 𝕜) V hV f‖ ≤ ‖clopenCut (𝕜 := 𝕜) U hU f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  by_cases ht : t ∈ V
  · simpa [ht, hVU ht] using
      (clopenCut (𝕜 := 𝕜) U hU f).norm_coe_le_norm t
  · simp [ht, norm_nonneg (clopenCut (𝕜 := 𝕜) U hU f)]

theorem clopenCut_diff (U V : Set K) (hU : IsClopen U) (hV : IsClopen V)
    (hVU : V ⊆ U) (f : C(K, E)) :
    clopenCut (𝕜 := 𝕜) (U \ V) (hU.diff hV) f =
      clopenCut (𝕜 := 𝕜) U hU f - clopenCut (𝕜 := 𝕜) V hV f := by
  ext t
  by_cases htV : t ∈ V
  · simp [htV, hVU htV]
  · by_cases htU : t ∈ U <;> simp [htV, htU]

end ClopenCut

/-- A cylinder is clopen in the binary product topology. -/
theorem isClopen_cantorCylinder (t : CantorSpace) (n : ℕ) :
    IsClopen (PiNat.cylinder t n) := by
  rw [PiNat.cylinder_eq_pi, Set.pi_def]
  apply isClopen_biInter_finset
  intro i _
  exact (isClopen_discrete ({t i} : Set (Fin 2))).preimage (continuous_apply i)

/-- Every neighborhood contains a prefix cylinder about the same point. -/
theorem exists_cantorCylinder_subset {t : CantorSpace} {U : Set CantorSpace}
    (hU : U ∈ 𝓝 t) : ∃ n : ℕ, PiNat.cylinder t n ⊆ U := by
  obtain ⟨V, hVU, hVopen, htV⟩ := mem_nhds_iff.mp hU
  obtain ⟨W, ⟨s, n, rfl⟩, htW, hWV⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => Fin 2)).exists_subset_of_mem_open htV hVopen
  refine ⟨n, ?_⟩
  rw [PiNat.mem_cylinder_iff_eq.mp htW]
  exact hWV.trans hVU

/-- A function vanishing at a point has arbitrarily small norm when cut
to a sufficiently short neighborhood of that point. -/
theorem exists_small_cantorCut (t : CantorSpace) (f : C(CantorSpace, E))
    (hf : f t = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ‖clopenCut (𝕜 := 𝕜) (PiNat.cylinder t n)
      (isClopen_cantorCylinder t n) f‖ < ε := by
  have hnear : {s : CantorSpace | ‖f s‖ < ε / 2} ∈ 𝓝 t := by
    have h := (f.continuous.norm.continuousAt).preimage_mem_nhds
      (Iio_mem_nhds (show ‖f t‖ < ε / 2 by rw [hf, norm_zero]; positivity))
    exact h
  obtain ⟨n, hn⟩ := exists_cantorCylinder_subset hnear
  refine ⟨n, ?_⟩
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (ContinuousMap.norm_le _ (half_pos hε).le).mpr
  intro s
  by_cases hs : s ∈ PiNat.cylinder t n
  · simpa [hs] using (hn hs).le
  · simp [hs, (half_pos hε).le]

theorem exists_small_cantorCut_after (t : CantorSpace) (f : C(CantorSpace, E))
    (hf : f t = 0) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, N < n ∧ ‖clopenCut (𝕜 := 𝕜) (PiNat.cylinder t n)
      (isClopen_cantorCylinder t n) f‖ < ε := by
  obtain ⟨n, hn⟩ := exists_small_cantorCut (𝕜 := 𝕜) t f hf hε
  refine ⟨max n (N + 1), by omega, ?_⟩
  apply lt_of_le_of_lt _ hn
  exact norm_clopenCut_mono (𝕜 := 𝕜) _ _ (isClopen_cantorCylinder t n)
    (isClopen_cantorCylinder t (max n (N + 1)))
    (PiNat.cylinder_anti t (le_max_left _ _)) f

variable [CompleteSpace E]

/-- A no-c₀ row is uniformly small on unit functions vanishing at t and
supported in a sufficiently small cylinder about t. A gliding-hump
argument turns any counterexample into disjoint functions, contradicting
the actual no-c₀ row-convergence theorem. -/
theorem exists_small_row_on_cantorCylinder (hE : ContainsNoCZero 𝕜 E)
    (R : C(CantorSpace, E) →L[𝕜] E) (t : CantorSpace)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ f : C(CantorSpace, E), ‖f‖ ≤ 1 →
      VanishesOff (PiNat.cylinder t n) f → f t = 0 → ‖R f‖ < ε := by
  classical
  by_contra h
  push_neg at h
  choose f hf hsupport hzero hlarge using h
  let δ := ε / (2 * (‖R‖ + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : ‖R‖ * δ < ε / 2 := by
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2 * (‖R‖ + 1))]
    nlinarith [norm_nonneg R]
  choose q hq hcut using fun n =>
    exists_small_cantorCut_after (𝕜 := 𝕜) t (f n) (hzero n) n hδ
  let g (n : ℕ) : C(CantorSpace, E) :=
    clopenCut (𝕜 := 𝕜) (PiNat.cylinder t n \ PiNat.cylinder t (q n))
      ((isClopen_cantorCylinder t n).diff (isClopen_cantorCylinder t (q n))) (f n)
  have hg (n : ℕ) : ‖g n‖ ≤ 1 :=
    (norm_clopenCut_apply_le (𝕜 := 𝕜) _ _ _).trans (hf n)
  have hdecomp (n : ℕ) : g n = f n -
      clopenCut (𝕜 := 𝕜) (PiNat.cylinder t (q n))
        (isClopen_cantorCylinder t (q n)) (f n) := by
    dsimp only [g]
    rw [clopenCut_diff (𝕜 := 𝕜) _ _ (isClopen_cantorCylinder t n)
      (isClopen_cantorCylinder t (q n)) (PiNat.cylinder_anti t (hq n).le)]
    rw [clopenCut_eq_of_vanishesOff (𝕜 := 𝕜) _ (isClopen_cantorCylinder t n)
      _ (hsupport n)]
  have hgl (n : ℕ) : ε / 2 < ‖R (g n)‖ := by
    have hrcut := R.le_opNorm
      (clopenCut (𝕜 := 𝕜) (PiNat.cylinder t (q n))
        (isClopen_cantorCylinder t (q n)) (f n))
    have hsmalln : ‖R (clopenCut (𝕜 := 𝕜) (PiNat.cylinder t (q n))
        (isClopen_cantorCylinder t (q n)) (f n))‖ < ε / 2 := by
      apply hrcut.trans_lt
      apply lt_of_le_of_lt _ hsmall
      exact mul_le_mul_of_nonneg_left (hcut n).le (norm_nonneg R)
    have htri := norm_sub_le (R (g n))
      (-R (clopenCut (𝕜 := 𝕜) (PiNat.cylinder t (q n))
        (isClopen_cantorCylinder t (q n)) (f n)))
    have heq : R (g n) -
        (-R (clopenCut (𝕜 := 𝕜) (PiNat.cylinder t (q n))
          (isClopen_cantorCylinder t (q n)) (f n))) = R (f n) := by
      rw [hdecomp n, map_sub]
      abel
    rw [heq, norm_neg] at htri
    have hln := hlarge n
    linarith
  let p (n : ℕ) : ℕ := q^[n] 0
  have hp (n : ℕ) : p (n + 1) = q (p n) := Function.iterate_succ_apply' q n 0
  have hpm : StrictMono p := strictMono_nat_of_lt_succ (fun n => by rw [hp]; exact hq _)
  have hdis : ∀ i j, i ≠ j → ∀ s : CantorSpace,
      g (p i) s = 0 ∨ g (p j) s = 0 := by
    intro i j hij s
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hle := hpm.monotone (Nat.succ_le_of_lt hij)
      rw [hp] at hle
      by_cases hs : s ∈ PiNat.cylinder t (q (p i))
      · left
        simp [g, hs]
      · right
        have hnot : s ∉ PiNat.cylinder t (p j) :=
          fun hs' => hs (PiNat.cylinder_anti t hle hs')
        simp [g, hnot]
    · have hle := hpm.monotone (Nat.succ_le_of_lt hji)
      rw [hp] at hle
      by_cases hs : s ∈ PiNat.cylinder t (q (p j))
      · right
        simp [g, hs]
      · left
        have hnot : s ∉ PiNat.cylinder t (p i) :=
          fun hs' => hs (PiNat.cylinder_anti t hle hs')
        simp [g, hnot]
  have ht := noCZero_disjoint_rows_tendsto_zero hE R (fun n => g (p n))
    zero_le_one (fun n => hg (p n)) hdis
  obtain ⟨n, hn⟩ := ((tendsto_order.mp ht).2 (ε / 2) (half_pos hε)).exists
  exact lt_asymm (hgl (p n)) hn

omit [CompleteSpace E] in
/-- The Nth clopen-cylinder approximation to the diagonal atom of a row. -/
def rowAtomApprox (R : C(CantorSpace, E) →L[𝕜] E) (t : CantorSpace) (n : ℕ) :
    E →L[𝕜] E :=
  R.comp ((clopenCut (PiNat.cylinder t n) (isClopen_cantorCylinder t n)).comp
    (ContinuousLinearMap.const 𝕜 CantorSpace))

omit [CompleteSpace E] in
@[simp] theorem rowAtomApprox_apply (R : C(CantorSpace, E) →L[𝕜] E)
    (t : CantorSpace) (n : ℕ) (x : E) :
    rowAtomApprox R t n x = R (clopenCut (𝕜 := 𝕜) (PiNat.cylinder t n)
      (isClopen_cantorCylinder t n) (ContinuousMap.const CantorSpace x)) := rfl

omit [CompleteSpace E] in
theorem norm_rowAtomApprox_le (R : C(CantorSpace, E) →L[𝕜] E)
    (t : CantorSpace) (n : ℕ) : ‖rowAtomApprox R t n‖ ≤ ‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R)
  intro x
  rw [rowAtomApprox_apply]
  have hc : ‖ContinuousMap.const CantorSpace x‖ ≤ ‖x‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
    intro s
    exact le_rfl
  exact (R.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left
      ((norm_clopenCut_apply_le (𝕜 := 𝕜) _ (isClopen_cantorCylinder t n)
        (ContinuousMap.const CantorSpace x)).trans hc) (norm_nonneg R))

omit [CompleteSpace E] in
theorem rowAtomApprox_dist_le (R : C(CantorSpace, E) →L[𝕜] E)
    (t : CantorSpace) {N m n : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hker : ∀ f : C(CantorSpace, E), ‖f‖ ≤ 1 →
      VanishesOff (PiNat.cylinder t N) f → f t = 0 → ‖R f‖ < ε)
    (hNm : N ≤ m) (hmn : m ≤ n) :
    dist (rowAtomApprox R t m) (rowAtomApprox R t n) ≤ ε := by
  rw [dist_eq_norm]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε
  intro x hx
  let g : C(CantorSpace, E) := clopenCut (𝕜 := 𝕜)
    (PiNat.cylinder t m \ PiNat.cylinder t n)
    ((isClopen_cantorCylinder t m).diff (isClopen_cantorCylinder t n))
    (ContinuousMap.const CantorSpace x)
  have hc : ‖ContinuousMap.const CantorSpace x‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro s
    exact hx.le
  have hgn : ‖g‖ ≤ 1 := (norm_clopenCut_apply_le (𝕜 := 𝕜) _ _ _).trans hc
  have hgs : VanishesOff (PiNat.cylinder t N) g :=
    vanishesOff_mono (Set.diff_subset.trans (PiNat.cylinder_anti t hNm))
      (clopenCut_vanishesOff (𝕜 := 𝕜) _ _ _)
  have hgt : g t = 0 := by simp [g]
  have heq : (rowAtomApprox R t m - rowAtomApprox R t n) x = R g := by
    change R (clopenCut (𝕜 := 𝕜) (PiNat.cylinder t m)
        (isClopen_cantorCylinder t m) (ContinuousMap.const CantorSpace x)) -
      R (clopenCut (𝕜 := 𝕜) (PiNat.cylinder t n)
        (isClopen_cantorCylinder t n) (ContinuousMap.const CantorSpace x)) = R g
    rw [← map_sub, ← clopenCut_diff (𝕜 := 𝕜) _ _ (isClopen_cantorCylinder t m)
      (isClopen_cantorCylinder t n) (PiNat.cylinder_anti t hmn)]
  rw [heq]
  exact (hker g hgn hgs hgt).le

theorem rowAtomApprox_cauchySeq (hE : ContainsNoCZero 𝕜 E)
    (R : C(CantorSpace, E) →L[𝕜] E) (t : CantorSpace) :
    CauchySeq (rowAtomApprox R t) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_small_row_on_cantorCylinder hE R t (half_pos hε)
  refine ⟨N, ?_⟩
  intro m hm n hn
  rcases le_total m n with hmn | hnm
  · exact (rowAtomApprox_dist_le R t (half_pos hε).le hN hm hmn).trans_lt
      (half_lt_self hε)
  · rw [dist_comm]
    exact (rowAtomApprox_dist_le R t (half_pos hε).le hN hn hnm).trans_lt
      (half_lt_self hε)

/-- The diagonal atom, constructed as the operator-norm limit of its
clopen-cylinder approximations. Existence is justified by the next theorem. -/
def rowAtom (R : C(CantorSpace, E) →L[𝕜] E) (t : CantorSpace) : E →L[𝕜] E :=
  limUnder atTop (rowAtomApprox R t)

theorem rowAtomApprox_tendsto (hE : ContainsNoCZero 𝕜 E)
    (R : C(CantorSpace, E) →L[𝕜] E) (t : CantorSpace) :
    Tendsto (rowAtomApprox R t) atTop (𝓝 (rowAtom R t)) :=
  (rowAtomApprox_cauchySeq hE R t).tendsto_limUnder

theorem norm_rowAtom_le (hE : ContainsNoCZero 𝕜 E)
    (R : C(CantorSpace, E) →L[𝕜] E) (t : CantorSpace) : ‖rowAtom R t‖ ≤ ‖R‖ :=
  le_of_tendsto (rowAtomApprox_tendsto hE R t).norm
    (Eventually.of_forall (norm_rowAtomApprox_le R t))

/-- The atom field of T, defined from its actual bounded rows. -/
def cantorAtomField (T : C(CantorSpace, E) →L[𝕜] C(CantorSpace, E)) :
    CantorSpace → E →L[𝕜] E :=
  fun t => rowAtom (rowOperator T t) t

theorem norm_cantorAtomField_le (hE : ContainsNoCZero 𝕜 E)
    (T : C(CantorSpace, E) →L[𝕜] C(CantorSpace, E)) (t : CantorSpace) :
    ‖cantorAtomField T t‖ ≤ ‖T‖ :=
  (norm_rowAtom_le hE (rowOperator T t) t).trans (norm_rowOperator_le T t)

omit [CompleteSpace E] in
def localizedZeroSubmodule (U : Set CantorSpace) (t : CantorSpace) :
    Submodule 𝕜 C(CantorSpace, E) where
  carrier := {f | VanishesOff U f ∧ f t = 0}
  zero_mem' := ⟨by intro s hs; rfl, rfl⟩
  add_mem' := by
    intro f g hf hg
    constructor
    · intro s hs
      change f s + g s = 0
      simp [hf.1 s hs, hg.1 s hs]
    · change f t + g t = 0
      simp [hf.2, hg.2]
  smul_mem' := by
    intro a f hf
    constructor
    · intro s hs
      change a • f s = 0
      simp [hf.1 s hs]
    · change a • f t = 0
      simp [hf.2]

omit [CompleteSpace E] in
/-- The unit-function kernel estimate extends to the usual homogeneous
operator bound on every localized function vanishing at t. -/
theorem row_kernel_bound (R : C(CantorSpace, E) →L[𝕜] E)
    (t : CantorSpace) (U : Set CantorSpace) {ε : ℝ} (hε : 0 ≤ ε)
    (hker : ∀ f : C(CantorSpace, E), ‖f‖ ≤ 1 → VanishesOff U f →
      f t = 0 → ‖R f‖ < ε) (f : C(CantorSpace, E))
    (hsupport : VanishesOff U f) (hzero : f t = 0) :
    ‖R f‖ ≤ ε * ‖f‖ := by
  let Z := localizedZeroSubmodule (𝕜 := 𝕜) (E := E) U t
  have hbound : ‖R.comp Z.subtypeL‖ ≤ ε := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hε
    intro g hg
    exact (hker g.val hg.le g.property.1 g.property.2).le
  have h := (R.comp Z.subtypeL).le_opNorm ⟨f, hsupport, hzero⟩
  exact h.trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg f))

/-- The local defect of the constructed atom field becomes arbitrarily
small on a shrinking clopen cylinder about each point. -/
theorem exists_cantorCylinder_localDefect_lt (hE : ContainsNoCZero 𝕜 E)
    (T : C(CantorSpace, E) →L[𝕜] C(CantorSpace, E)) (t : CantorSpace)
    {η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ, localDefect T (cantorAtomField T) (PiNat.cylinder t n) t < η := by
  let R := rowOperator T t
  obtain ⟨N, hN⟩ := exists_small_row_on_cantorCylinder hE R t
    (show 0 < η / 4 by positivity)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp (rowAtomApprox_tendsto hE R t)
    (η / 4) (by positivity)
  let n := max N M
  have hnN : N ≤ n := le_max_left _ _
  have hnM : M ≤ n := le_max_right _ _
  have hnear : ‖rowAtomApprox R t n - rowAtom R t‖ < η / 4 := by
    simpa only [dist_eq_norm] using hM n hnM
  refine ⟨n, ?_⟩
  apply lt_of_le_of_lt _ (show 3 * η / 4 < η by linarith)
  apply csSup_le (localDefect_set_nonempty T (cantorAtomField T) _ t)
  rintro r ⟨f, hf, hsupport, rfl⟩
  let c := clopenCut (𝕜 := 𝕜) (PiNat.cylinder t n)
    (isClopen_cantorCylinder t n) (ContinuousMap.const CantorSpace (f t))
  let g := f - c
  have hcn : ‖c‖ ≤ 1 := by
    apply (norm_clopenCut_apply_le (𝕜 := 𝕜) _ _ _).trans
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro s
    exact (f.norm_coe_le_norm t).trans hf
  have hgn : ‖g‖ ≤ 2 := by
    exact (norm_sub_le f c).trans ((add_le_add hf hcn).trans_eq (by norm_num))
  have hgs : VanishesOff (PiNat.cylinder t N) g := by
    apply vanishesOff_mono (PiNat.cylinder_anti t hnN)
    intro s hs
    change f s - c s = 0
    simp [c, hs, hsupport s hs]
  have hgt : g t = 0 := by simp [g, c]
  have hRg : ‖R g‖ ≤ η / 2 := by
    exact (row_kernel_bound R t _ (by positivity) hN g hgs hgt).trans
      ((mul_le_mul_of_nonneg_left hgn (by positivity : 0 ≤ η / 4)).trans_eq (by ring))
  have hdiff : ‖(rowAtomApprox R t n - rowAtom R t) (f t)‖ ≤ η / 4 := by
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul hnear.le ((f.norm_coe_le_norm t).trans hf) (norm_nonneg _)
        (by positivity : 0 ≤ η / 4)).trans_eq (mul_one _))
  have heq : T f t - cantorAtomField T t (f t) =
      R g + (rowAtomApprox R t n - rowAtom R t) (f t) := by
    change R f - rowAtom R t (f t) =
      R (f - c) + (rowAtomApprox R t n (f t) - rowAtom R t (f t))
    rw [map_sub]
    have hc : R c = rowAtomApprox R t n (f t) := rfl
    rw [hc]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hRg hdiff).trans_eq (by ring))

omit [CompleteSpace E] in
/-- For each fixed vector, the cylinder atom approximants depend
continuously on the base point. This is strong continuity, exactly the
topology used in the paper's Borel atom-field argument. -/
theorem continuous_rowAtomApprox_apply
    (T : C(CantorSpace, E) →L[𝕜] C(CantorSpace, E)) (n : ℕ) (x : E) :
    Continuous (fun t => rowAtomApprox (rowOperator T t) t n x) := by
  let F (t : CantorSpace) : C(CantorSpace, E) :=
    clopenCut (𝕜 := 𝕜) (PiNat.cylinder t n) (isClopen_cantorCylinder t n)
      (ContinuousMap.const CantorSpace x)
  have hF : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro t₀
    apply tendsto_const_nhds.congr'
    filter_upwards [((isClopen_cantorCylinder t₀ n).isOpen.mem_nhds
      (PiNat.self_mem_cylinder t₀ n))] with t ht
    have hset := PiNat.mem_cylinder_iff_eq.mp ht
    dsimp only [F]
    ext s
    simp only [clopenCut_apply]
    rw [hset]
  exact continuous_eval.comp ((T.continuous.comp hF).prodMk continuous_id)

theorem cantorAtomField_apply_tendsto (hE : ContainsNoCZero 𝕜 E)
    (T : C(CantorSpace, E) →L[𝕜] C(CantorSpace, E)) (t : CantorSpace) (x : E) :
    Tendsto (fun n => rowAtomApprox (rowOperator T t) t n x)
      atTop (𝓝 (cantorAtomField T t x)) := by
  have happ : Continuous (fun S : E →L[𝕜] E => S x) := by fun_prop
  exact (happ.tendsto _).comp (rowAtomApprox_tendsto hE (rowOperator T t) t)

theorem measurable_cantorAtomField_apply [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace CantorSpace] [BorelSpace CantorSpace]
    (hE : ContainsNoCZero 𝕜 E)
    (T : C(CantorSpace, E) →L[𝕜] C(CantorSpace, E)) (x : E) :
    Measurable (fun t => cantorAtomField T t x) := by
  apply measurable_of_tendsto_metrizable
    (fun n => (continuous_rowAtomApprox_apply T n x).measurable)
  exact tendsto_pi_nhds.mpr (fun t => cantorAtomField_apply_tendsto hE T t x)

end CKEUPFP
