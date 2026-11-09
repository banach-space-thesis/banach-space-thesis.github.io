import ThesisCommon.Analysis.SchauderSumMatrix
import ThesisCommon.Analysis.CompactScalarForward
import ThesisCommon.Analysis.SequenceOffDiagonal
import ThesisCommon.Analysis.SequenceBlockTailBounds

/-! Upper-triangular approximation for general one-unconditional basis sums.
The retained coordinates are a supported subspace, without an assumption
that the subsequence of the basis is equivalent to the whole basis. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace LPCK.Printed
open ThesisCommon
set_option synthInstance.maxHeartbeats 240000

variable {𝕜 E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {b : NormalizedSchauderBasis 𝕜 E} {hb : b.IsOneUnconditional}

private theorem compact_coordinate_norm (hb : b.IsOneUnconditional)
    {S : X →L[𝕜] E} (hS : IsCompactOperator S) :
    Tendsto (fun n => ‖(b.coord n).comp S‖) atTop (𝓝 0) := by
  obtain ⟨K, hK, hSK⟩ := hS.image_closedBall_subset_compact (f := S.toLinearMap) 1
  apply tendsto_order.2
  constructor
  · exact fun a ha => Eventually.of_forall (fun _ => ha.trans_le (norm_nonneg _))
  · intro ε hε
    have hquarter : 0 < ε/4 := by positivity
    obtain ⟨s, _, hfin, hcover⟩ := hK.finite_cover_balls hquarter
    have hs : ∀ᶠ n in atTop, ∀ y ∈ s, ‖b.coord n y‖ < ε/4 :=
      (hfin.eventually_all).2 (fun y _ =>
        (by simpa using (b.coord_tendsto_zero y).norm : Tendsto (fun n => ‖b.coord n y‖)
          atTop (𝓝 0)).eventually_lt_const hquarter)
    filter_upwards [hs] with n hn
    apply lt_of_le_of_lt _ (half_lt_self hε)
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (half_pos hε).le
    intro x hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (hcover (hSK
      ⟨x, by simp [Metric.mem_closedBall, dist_zero_right, hx], rfl⟩))
    obtain ⟨hys, hxy⟩ := Set.mem_iUnion.1 hy
    have hdist : ‖S x - y‖ < ε/4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hxy
    have hnorm : ‖b.coord n (S x) - b.coord n y‖ ≤ ‖S x - y‖ := by
      simpa only [map_sub, b.norm_coord_eq_one hb n, one_mul] using
        (b.coord n).le_opNorm (S x - y)
    exact (norm_le_norm_sub_add _ _).trans
      ((add_le_add hnorm le_rfl).trans (by linarith [hn y hys]))

private theorem norm_coordinate_comp_tendsto_zero
    (hcompact : ∀ S : X →L[𝕜] E, IsCompactOperator S)
    (T : X →L[𝕜] SchauderSum b hb X) :
    Tendsto (fun n => ‖(SchauderSum.coordinate n).comp T‖) atTop (𝓝 0) := by
  classical
  choose f hf hnorm using fun n => exists_norming_postcomposition
    ((SchauderSum.coordinate n).comp T)
  have hd (y : SchauderSum b hb X) :
      ∃ z : E, (∀ n, b.coord n z = f n (y n)) ∧ ‖z‖ ≤ ‖y‖ := by
    apply b.exists_of_coord_domination hb (SchauderSum.normVector y)
    intro n
    rw [SchauderSum.coord_normVector, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    exact ((f n).le_opNorm _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hf n) (norm_nonneg (y n)))
  let D : SchauderSum b hb X →L[𝕜] E := LinearMap.mkContinuous
    { toFun := fun y => (hd y).choose
      map_add' := fun x y => b.ext (fun n => by
        rw [(hd (x + y)).choose_spec.1, map_add, (hd x).choose_spec.1, (hd y).choose_spec.1,
          SchauderSum.add_apply, map_add])
      map_smul' := fun c x => b.ext (fun n => by
        rw [(hd (c • x)).choose_spec.1, RingHom.id_apply, map_smul,
          (hd x).choose_spec.1, SchauderSum.smul_apply, map_smul]) }
    1 (fun y => by simpa only [one_mul] using (hd y).choose_spec.2)
  let S := D.comp T
  have ht := compact_coordinate_norm hb (hcompact S)
  have heq (n : ℕ) : (b.coord n).comp S = (f n).comp ((SchauderSum.coordinate n).comp T) := by
    ext x : 1
    exact (hd (T x)).choose_spec.1 n
  have hbound (n : ℕ) : ‖(SchauderSum.coordinate n).comp T‖ ≤ 2 * ‖(b.coord n).comp S‖ := by
    rw [heq n]
    exact hnorm n
  exact squeeze_zero (fun _ => norm_nonneg _) hbound (by simpa using ht.const_mul 2)

/-- The actual supported subspace with its inherited Schauder-sum norm. -/
def schauderSupported (M : Set ℕ) : Submodule 𝕜 (SchauderSum b hb X) where
  carrier := {x | ∀ i ∉ M, x i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
  smul_mem' := by intro c x hx i hi; simp [hx i hi]

private theorem schauderSupported_closed (M : Set ℕ) :
    IsClosed (schauderSupported (b := b) (hb := hb) (X := X) M :
      Set (SchauderSum b hb X)) := by
  change IsClosed {x : SchauderSum b hb X | ∀ i ∉ M, x i = 0}
  rw [show {x : SchauderSum b hb X | ∀ i ∉ M, x i = 0} =
    ⋂ i : {i // i ∉ M}, {x : SchauderSum b hb X | x i.val = 0} by ext x; simp]
  exact isClosed_iInter (fun i => isClosed_eq (SchauderSum.coordinate i.val).continuous continuous_const)

/-- The canonical coordinate projection onto the supported subspace. -/
def schauderProject (M : Set ℕ) :
    SchauderSum b hb X →L[𝕜] schauderSupported (b := b) (hb := hb) (X := X) M := by
  classical
  let A := SchauderSum.diagonal (b := b) (hb := hb)
    (fun n => if n ∈ M then ContinuousLinearMap.id 𝕜 X else 0) 1 zero_le_one
    (fun n => by
      dsimp only
      split_ifs
      · exact ContinuousLinearMap.norm_id_le
      · simp)
  exact A.codRestrict (schauderSupported (b := b) (hb := hb) (X := X) M)
    (fun x n hn => by simp [A, hn])

@[simp] theorem schauderProject_apply (M : Set ℕ) (x : SchauderSum b hb X)
    {n : ℕ} (hn : n ∈ M) : (schauderProject (b := b) (hb := hb) (X := X) M x).val n = x n := by
  classical
  unfold schauderProject
  simp only [ContinuousLinearMap.coe_codRestrict_apply, SchauderSum.diagonal_apply, if_pos hn,
    ContinuousLinearMap.id_apply]

/-- Insertion in a retained coordinate, with the inherited norm. -/
def schauderSupportedSingle {M : Set ℕ} {n : ℕ} (hn : n ∈ M) :
    X →L[𝕜] schauderSupported (b := b) (hb := hb) (X := X) M :=
  (SchauderSum.singleL (b := b) (hb := hb) (Y := X) n).codRestrict
    (schauderSupported (b := b) (hb := hb) (X := X) M) (fun x i hi => by
    have hin : i ≠ n := fun h => hi (h ▸ hn)
    simp [SchauderSum.single_apply, hin])

private theorem norm_schauderSupportedSingle_le {M : Set ℕ} {n : ℕ} (hn : n ∈ M) :
    ‖schauderSupportedSingle (b := b) (hb := hb) (X := X) hn‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖SchauderSum.single (b := b) (hb := hb) n x‖ ≤ 1 * ‖x‖
  simp

set_option maxHeartbeats 1400000 in
/-- Proposition 3.5 in normalized coordinates. For a general basis, storing
coordinate n multiplied by ‖eₙ‖ is the isometric realization of its sum;
this rescaling commutes with support projections and preserves upper entries. -/
theorem proposition_3_5 (hcompact : ∀ S : X →L[𝕜] E, IsCompactOperator S)
    (T : SchauderSum b hb X →L[𝕜] SchauderSum b hb X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : ℕ ↪ ℕ) (U : schauderSupported (b := b) (hb := hb) (X := X) (Set.range f) →L[𝕜]
        schauderSupported (b := b) (hb := hb) (X := X) (Set.range f)),
      StrictMono f ∧
      ‖((schauderProject (Set.range f)).comp T).comp (schauderSupported (Set.range f)).subtypeL - U‖ < ε ∧
      ∀ i j (x : X),
        (U (schauderSupportedSingle (b := b) (hb := hb) (Set.mem_range_self j) x)).val (f i) =
          if i ≤ j then SchauderSum.block T (f i) (f j) x else 0 := by
  classical
  let β (i : ℕ) := (ε / 4) * (1 / 2 : ℝ)^i
  let δ (i : ℕ) := β i / ((i : ℝ) + 1)
  have ht (j : ℕ) : Tendsto (fun i => ‖SchauderSum.block T i j‖) atTop (𝓝 0) := by
    simpa only [SchauderSum.block, ContinuousLinearMap.comp_assoc] using
      norm_coordinate_comp_tendsto_zero hcompact (T.comp (SchauderSum.singleL j))
  have cut (m i : ℕ) : ∃ N, ∀ n ≥ N, ∀ j ≤ m, ‖SchauderSum.block T n j‖ < δ i := by
    have hδ : 0 < δ i := by dsimp [δ, β]; positivity
    have ev : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range (m + 1),
        ‖SchauderSum.block T n j‖ < δ i := by
      exact (Finset.eventually_all _).2 (fun j _ => (ht j).eventually_lt_const hδ)
    obtain ⟨N, hN⟩ := eventually_atTop.1 ev
    exact ⟨N, fun n hn j hj => hN n hn j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))⟩
  choose N hN using cut
  let g : ℕ → ℕ := fun k => Nat.rec 0 (fun i m => max (m + 1) (N m (i + 1))) k
  have hg : StrictMono g := strictMono_nat_of_lt_succ (fun i =>
    (Nat.lt_succ_self (g i)).trans_le (le_max_left _ _))
  let f : ℕ ↪ ℕ := ⟨g, hg.injective⟩
  let M := Set.range f
  let Z := schauderSupported (b := b) (hb := hb) (X := X) M
  letI : NormedSpace 𝕜 ↥Z := inferInstanceAs (NormedSpace 𝕜
    ↥(schauderSupported (b := b) (hb := hb) (X := X) M))
  letI : CompleteSpace Z := (schauderSupported_closed (b := b) (hb := hb) (X := X) M).completeSpace_coe
  let J (i : ℕ) : X →L[𝕜] Z := schauderSupportedSingle (Set.mem_range_self i)
  let R (j : ℕ) : Z →L[𝕜] X := (SchauderSum.coordinate (f j)).comp Z.subtypeL
  have hJ (i : ℕ) : ‖J i‖ ≤ 1 := norm_schauderSupportedSingle_le _
  have hR (j : ℕ) : ‖R j‖ ≤ 1 :=
    (norm_comp_right_contraction _ _ (Submodule.norm_subtypeL_le Z)).trans
      (SchauderSum.norm_coordinate_le _)
  let C : Z →L[𝕜] Z := ((schauderProject M).comp T).comp Z.subtypeL
  let term (i j : ℕ) : Z →L[𝕜] Z :=
    (J i).comp ((SchauderSum.block T (f i) (f j)).comp (R j))
  let row (i : ℕ) : Z →L[𝕜] Z := ∑ j ∈ Finset.range i, term i j
  have hterm (i j : ℕ) (hji : j < i) : ‖term i j‖ ≤ δ i := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hji))
    exact ((norm_comp_left_contraction (J (k+1)) (hJ (k+1)) _).trans
      (norm_comp_right_contraction _ _ (hR j))).trans
      ((hN (g k) (k+1) (g (k+1)) (le_max_right _ _) (g j)
        (hg.monotone (Nat.le_of_lt_succ hji))).le)
  have hrow (i : ℕ) : ‖row i‖ ≤ β i := by
    calc
      ‖row i‖ ≤ ∑ j ∈ Finset.range i, ‖term i j‖ := norm_sum_le (Finset.range i) (term i)
      _ ≤ ∑ j ∈ Finset.range i, δ i :=
        Finset.sum_le_sum fun j hj => hterm i j (Finset.mem_range.mp hj)
      _ = (i : ℝ) * δ i := by simp
      _ ≤ ((i : ℝ) + 1) * δ i := by
        apply mul_le_mul_of_nonneg_right (by linarith)
        dsimp [δ, β]; positivity
      _ = β i := by dsimp [δ]; field_simp
  have hβ : HasSum β (ε / 4 * 2) := hasSum_geometric_two.mul_left (ε/4)
  have hsum : Summable row := hβ.summable.of_norm_bounded hrow
  let A := ∑' i, row i
  have hnA : ‖A‖ < ε := by
    have hn := hβ.summable.of_nonneg_of_le (fun i => norm_nonneg (row i)) hrow
    refine (norm_tsum_le_tsum_norm hn).trans_lt ?_
    exact (hn.tsum_le_tsum hrow hβ.summable).trans_lt (by rw [hβ.tsum_eq]; linarith)
  refine ⟨f, C - A, hg, ?_, ?_⟩
  · change ‖C - (C - A)‖ < ε
    rwa [sub_sub_cancel]
  · intro i j x
    have hj (k : ℕ) : (J j x).val (f k) = if k = j then x else 0 := by
      change SchauderSum.single (b := b) (hb := hb) (f j) x (f k) = _
      simp only [SchauderSum.single_apply, f.injective.eq_iff]
    have hC : (C (J j x)).val (f i) = SchauderSum.block T (f i) (f j) x := by
      change (schauderProject (b := b) (hb := hb) (X := X) M
        (T (SchauderSum.single (f j) x))).val (f i) = _
      rw [schauderProject_apply M _ (Set.mem_range_self i), SchauderSum.block_apply]
    have hterm_eval (k l : ℕ) : ((term k l) (J j x)).val (f i) =
        if i = k then SchauderSum.block T (f k) (f l) (R l (J j x)) else 0 := by
      change SchauderSum.single (b := b) (hb := hb) (f k)
        (SchauderSum.block T (f k) (f l) (R l (J j x))) (f i) = _
      by_cases hk : i = k
      · subst k; simp [SchauderSum.single_apply]
      · simp [SchauderSum.single_apply, hk, f.injective.ne hk]
    have hread (l : ℕ) : R l (J j x) = if l = j then x else 0 := hj l
    have hA : (A (J j x)).val (f i) =
        if j < i then SchauderSum.block T (f i) (f j) x else 0 := by
      let ev := ((SchauderSum.coordinate (f i)).comp Z.subtypeL).comp
        (ContinuousLinearMap.apply 𝕜 Z (J j x))
      change ev (∑' k, row k) = _
      rw [ev.map_tsum hsum, tsum_eq_single i]
      · simp only [row, map_sum, ev, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
        change (∑ l ∈ Finset.range i, ((term i l) (J j x)).val (f i)) = _
        simp only [hterm_eval, if_pos rfl, hread, apply_ite, map_zero]
        by_cases hji : j < i <;> simp [Finset.sum_ite_eq', Finset.mem_range, hji]
      · intro k hki
        simp only [row, map_sum, ev, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
        change (∑ l ∈ Finset.range k, ((term k l) (J j x)).val (f i)) = 0
        apply Finset.sum_eq_zero
        intro l _
        simp [hterm_eval, Ne.symm hki]
    change (C (J j x)).val (f i) - (A (J j x)).val (f i) = _
    rw [hC, hA]
    by_cases h : i ≤ j <;> simp [h, Nat.lt_of_not_ge, Nat.not_lt_of_ge]

end LPCK.Printed
