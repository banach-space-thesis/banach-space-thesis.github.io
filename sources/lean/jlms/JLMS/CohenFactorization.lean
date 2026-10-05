import JLMS.CohenSequenceSpace

/-!
# Constructive simultaneous Cohen factorization

The construction takes place in an ambient unital Banach algebra. This is
the setting needed for Ogden's closed ideal of operators. The factors are
constructed as limits of products of invertible convex combinations of the
identity and elements of a bounded right approximate identity.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Filter Topology
open scoped ZeroAtInfty
namespace JLMS

variable {𝕜 B : Type*} [RCLike 𝕜] [NormedRing B] [NormedAlgebra 𝕜 B]
  [CompleteSpace B]

/-- The limiting step in the constructive factorization: the scalar
quotients of the units vanish, while the transformed null sequences converge
in the Banach space of null sequences. -/
theorem nullSequence_factor_of_cauchy_units (P : Submodule 𝕜 B)
    (hclosed : IsClosed (P : Set B)) (x : C₀(ℕ, B))
    {q : ℝ} (hq : 0 ≤ q) (hqone : q < 1) (u : ℕ → Bˣ)
    (huP : ∀ n, (u n : B) - ((q ^ n : ℝ) : 𝕜) • (1 : B) ∈ P)
    (hu : CauchySeq (fun n => (u n : B)))
    (hy : CauchySeq (fun n => cohenSequenceMulRight x (↑(u n)⁻¹ : B))) :
    ∃ a ∈ P, ∃ y : C₀(ℕ, B), ∀ k, x k = y k * a := by
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hu
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hy
  have hqzero := tendsto_pow_atTop_nhds_zero_of_lt_one hq hqone
  have hscalar : Tendsto (fun n => ((q ^ n : ℝ) : 𝕜) • (1 : B)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun n => ((q ^ n : ℝ) : 𝕜)) atTop (𝓝 0) := by
      simpa only [RCLike.ofReal_zero] using
        (RCLike.continuous_ofReal.tendsto (0 : ℝ)).comp hqzero
    simpa using hcast.smul_const (1 : B)
  have haP : a ∈ P := hclosed.mem_of_tendsto
    (by simpa using ha.sub hscalar) (Filter.Eventually.of_forall huP)
  refine ⟨a, haP, y, fun k => ?_⟩
  have heval : Continuous (fun z : C₀(ℕ, B) => z k) :=
    BoundedContinuousFunction.continuous_eval_const.comp
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous
  have hlim := ((heval.tendsto y).comp hy).mul ha
  have hconst : (fun n => cohenSequenceMulRight x (↑(u n)⁻¹ : B) k * (u n : B)) =
      fun _ : ℕ => x k := by
    funext n
    simp [mul_assoc]
  simp only [Function.comp_def] at hlim
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- A Neumann inverse bound specialized to the uniform bound used in Cohen's
construction. Both inverse identities are carried by the returned unit. -/
theorem exists_cohen_unit [NormOneClass B] (t : B) (ht : ‖t‖ ≤ (1 / 2 : ℝ)) :
    ∃ u : Bˣ, (u : B) = 1 - t ∧ ‖(↑u⁻¹ : B)‖ ≤ 2 := by
  have htone : ‖t‖ < 1 := ht.trans_lt (by norm_num)
  let u := Units.oneSub t htone
  refine ⟨u, rfl, ?_⟩
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hpow (n : ℕ) : ‖t ^ n‖ ≤ (1 / 2 : ℝ) ^ n :=
    (norm_pow_le t n).trans (pow_le_pow_left₀ (norm_nonneg t) ht n)
  have hs := hgeom.of_nonneg_of_le (fun _ => norm_nonneg _) hpow
  change ‖∑' n : ℕ, t ^ n‖ ≤ 2
  calc
    _ ≤ ∑' n, ‖t ^ n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n := hs.tsum_le_tsum hpow hgeom
    _ = 2 := by rw [tsum_geometric_of_abs_lt_one (by norm_num)]; norm_num

/-- One recursive step of Cohen's construction. The two error budgets control
the product in the algebra and the transformed sequence independently. -/
theorem exists_cohen_step [NormOneClass B] (P : Submodule 𝕜 B)
    (hleft : ∀ a b : B, b ∈ P → a * b ∈ P) {M : ℝ} (hM : 0 ≤ M)
    (hAI : HasBoundedRightApproximation P M) (x : C₀(ℕ, B)) (hx : ∀ k, x k ∈ P)
    {r : ℝ} (hr : 0 < r) (hrone : r < 1) (hrM : r * (M + 1) ≤ 1 / 2)
    (n : ℕ) (u : Bˣ)
    (huP : (u : B) - (((1 - r) ^ n : ℝ) : 𝕜) • (1 : B) ∈ P) :
    ∃ v : Bˣ,
      (v : B) - (((1 - r) ^ (n + 1) : ℝ) : 𝕜) • (1 : B) ∈ P ∧
      ‖(v : B) - (u : B)‖ ≤ r * ((1 - r) ^ n * (M + 1) + (1 / 2 : ℝ) ^ n) ∧
      ‖cohenSequenceMulRight x (↑v⁻¹ : B) -
        cohenSequenceMulRight x (↑u⁻¹ : B)‖ ≤ (1 / 2 : ℝ) ^ n := by
  let δ : ℝ := (1 / 2 : ℝ) ^ n
  have hδ : 0 < δ := by positivity
  let ε : ℝ := δ / (2 * r * (‖(↑u⁻¹ : B)‖ + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  let s : P := ⟨(u : B) - (((1 - r) ^ n : ℝ) : 𝕜) • (1 : B), huP⟩
  obtain ⟨e, he, heM, hs, hxapp⟩ := exists_rightApproximation_nullSequence P hM hAI x hx s hδ hε
  have hnorme : ‖(1 : B) - e‖ ≤ M + 1 := by
    calc
      _ ≤ ‖(1 : B)‖ + ‖e‖ := norm_sub_le _ _
      _ ≤ M + 1 := by simpa only [norm_one] using (add_le_add_left heM 1).trans_eq (by ring)
  have ht : ‖(r : 𝕜) • ((1 : B) - e)‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hnorme hr.le).trans hrM
  obtain ⟨b, hb, hbinv⟩ := exists_cohen_unit ((r : 𝕜) • ((1 : B) - e)) ht
  have hb' : (b : B) = ((1 - r : ℝ) : 𝕜) • (1 : B) + (r : 𝕜) • e := by
    rw [hb, RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul, one_smul, smul_sub]
    abel
  let v : Bˣ := u * b
  have hv : (v : B) - (u : B) = (r : 𝕜) • ((u : B) * e - (u : B)) := by
    change (u : B) * (b : B) - (u : B) = _
    simp only [hb, mul_sub, mul_one, mul_smul_comm, smul_sub]
    abel
  have hdecomp : (u : B) * e - (u : B) =
      (s.val * e - s.val) + (((1 - r) ^ n : ℝ) : 𝕜) • (e - 1) := by
    dsimp [s]
    simp only [sub_mul, smul_mul_assoc, one_mul, smul_sub]
    abel
  have hqnorm : ‖(((1 - r) ^ n : ℝ) : 𝕜)‖ = (1 - r) ^ n := by
    rw [RCLike.norm_ofReal, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr hrone.le) n)]
  have hvnorm : ‖(v : B) - (u : B)‖ ≤
      r * ((1 - r) ^ n * (M + 1) + δ) := by
    rw [hv, norm_smul, RCLike.norm_ofReal, abs_of_pos hr, hdecomp]
    apply mul_le_mul_of_nonneg_left _ hr.le
    calc
      _ ≤ ‖s.val * e - s.val‖ + ‖(((1 - r) ^ n : ℝ) : 𝕜) • (e - 1)‖ := norm_add_le _ _
      _ ≤ δ + (1 - r) ^ n * (M + 1) := by
        rw [norm_smul, hqnorm]
        exact add_le_add (by simpa only [norm_sub_rev] using hs)
          (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hnorme)
            (pow_nonneg (sub_nonneg.mpr hrone.le) n))
      _ = _ := add_comm _ _
  have hvP : (v : B) - (((1 - r) ^ (n + 1) : ℝ) : 𝕜) • (1 : B) ∈ P := by
    have heq : (v : B) - (((1 - r) ^ (n + 1) : ℝ) : 𝕜) • (1 : B) =
        ((1 - r : ℝ) : 𝕜) • s.val + (r : 𝕜) • ((u : B) * e) := by
      change (u : B) * (b : B) - _ = _
      rw [hb']
      dsimp [s]
      rw [mul_add, mul_smul_comm, mul_one, mul_smul_comm, smul_sub, smul_smul]
      simp only [pow_succ, RCLike.ofReal_mul]
      rw [mul_comm (((1 - r : ℝ) : 𝕜))]
      abel
    rw [heq]
    exact P.add_mem (P.smul_mem _ s.property) (P.smul_mem _ (hleft _ _ he))
  have hid : cohenSequenceMulRight x (↑v⁻¹ : B) - cohenSequenceMulRight x (↑u⁻¹ : B) =
      (r : 𝕜) • cohenSequenceMulRight
        (cohenSequenceMulRight (x - cohenSequenceMulRight x e) (↑b⁻¹ : B)) (↑u⁻¹ : B) := by
    ext k
    change x k * (↑v⁻¹ : B) - x k * (↑u⁻¹ : B) =
      (r : 𝕜) • (((x k - x k * e) * (↑b⁻¹ : B)) * (↑u⁻¹ : B))
    have hxb : x k - x k * (b : B) = (r : 𝕜) • (x k - x k * e) := by
      rw [hb, mul_sub, mul_one, mul_smul_comm, mul_sub, mul_one]
      abel
    calc
      _ = ((x k - x k * (b : B)) * (↑b⁻¹ : B)) * (↑u⁻¹ : B) := by
        have hcancel : (x k * (b : B)) * (↑b⁻¹ : B) = x k := by
          exact Units.mul_inv_cancel_right _ _
        simp only [v, mul_inv_rev, Units.val_mul, sub_mul, hcancel, mul_assoc]
      _ = _ := by rw [hxb, smul_mul_assoc, smul_mul_assoc]
  have hproduct : r * (ε * 2 * ‖(↑u⁻¹ : B)‖) ≤ δ := by
    calc
      _ ≤ r * (ε * 2 * (‖(↑u⁻¹ : B)‖ + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hr.le
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = δ := by
        dsimp [ε]
        field_simp
  refine ⟨v, hvP, hvnorm, ?_⟩
  rw [hid, norm_smul, RCLike.norm_ofReal, abs_of_pos hr]
  apply le_trans _ hproduct
  apply mul_le_mul_of_nonneg_left _ hr.le
  exact (norm_cohenSequenceMulRight_le _ _).trans (mul_le_mul_of_nonneg_right
    ((norm_cohenSequenceMulRight_le _ _).trans
      (mul_le_mul hxapp hbinv (norm_nonneg _) hε.le)) (norm_nonneg _))

/-- Simultaneous Cohen factorization of a Banach-valued null sequence in a
closed left ideal with a bounded right approximate identity. -/
theorem cohen_factor_nullSequence [NormOneClass B] (P : Submodule 𝕜 B)
    (hclosed : IsClosed (P : Set B))
    (hleft : ∀ a b : B, b ∈ P → a * b ∈ P) {M : ℝ} (hM : 0 ≤ M)
    (hAI : HasBoundedRightApproximation P M) (x : C₀(ℕ, B)) (hx : ∀ k, x k ∈ P) :
    ∃ a ∈ P, ∃ y : C₀(ℕ, B), ∀ k, x k = y k * a := by
  let r : ℝ := 1 / (2 * (M + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrhalf : r ≤ 1 / 2 := by
    dsimp [r]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have hrone : r < 1 := hrhalf.trans_lt (by norm_num)
  have hrM : r * (M + 1) ≤ 1 / 2 := by
    dsimp [r]
    have hMp : M + 1 ≠ 0 := by positivity
    field_simp
    norm_num
  let V (n : ℕ) := {u : Bˣ |
    (u : B) - (((1 - r) ^ n : ℝ) : 𝕜) • (1 : B) ∈ P}
  have hex (n : ℕ) (u : V n) := exists_cohen_step P hleft hM hAI x hx hr hrone hrM n u.val u.property
  let advance (n : ℕ) (u : V n) : V (n + 1) :=
    ⟨Classical.choose (hex n u), (Classical.choose_spec (hex n u)).1⟩
  let initial : V 0 := ⟨1, by
    change (1 : B) - (((1 - r) ^ 0 : ℝ) : 𝕜) • (1 : B) ∈ P
    simpa using P.zero_mem⟩
  let w : (n : ℕ) → V n := fun n => Nat.rec initial advance n
  let u : ℕ → Bˣ := fun n => (w n).val
  have huP (n : ℕ) : (u n : B) - (((1 - r) ^ n : ℝ) : 𝕜) • (1 : B) ∈ P := (w n).property
  have hstepA (n : ℕ) : ‖(u (n + 1) : B) - (u n : B)‖ ≤
      r * ((1 - r) ^ n * (M + 1) + (1 / 2 : ℝ) ^ n) :=
    (Classical.choose_spec (hex n (w n))).2.1
  have hstepX (n : ℕ) : ‖cohenSequenceMulRight x (↑(u (n + 1))⁻¹ : B) -
      cohenSequenceMulRight x (↑(u n)⁻¹ : B)‖ ≤ (1 / 2 : ℝ) ^ n :=
    (Classical.choose_spec (hex n (w n))).2.2
  have hq : 0 ≤ 1 - r := sub_nonneg.mpr hrone.le
  have hqone : 1 - r < 1 := by linarith
  have hgeomq : Summable (fun n : ℕ => (1 - r) ^ n) :=
    summable_geometric_of_lt_one hq hqone
  have hgeomhalf : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have huC : CauchySeq (fun n => (u n : B)) :=
    cauchySeq_of_dist_le_of_summable _
      (fun n => by
        rw [dist_eq_norm, norm_sub_rev]
        exact hstepA n)
      (((hgeomq.mul_right (M + 1)).add hgeomhalf).mul_left r)
  have hxC : CauchySeq (fun n => cohenSequenceMulRight x (↑(u n)⁻¹ : B)) :=
    cauchySeq_of_dist_le_of_summable _
      (fun n => by
        rw [dist_eq_norm, norm_sub_rev]
        exact hstepX n) hgeomhalf
  exact nullSequence_factor_of_cauchy_units P hclosed x hq hqone u huP huC hxC

/-- The sequence form used by the automatic-continuity argument. Its
factorization property is concluded from the approximate identity. -/
theorem cohen_factor_tendsto_zero [NormOneClass B] (P : Submodule 𝕜 B)
    (hclosed : IsClosed (P : Set B))
    (hleft : ∀ a b : B, b ∈ P → a * b ∈ P) {M : ℝ} (hM : 0 ≤ M)
    (hAI : HasBoundedRightApproximation P M) (x : ℕ → P) (hx : Tendsto x atTop (𝓝 0)) :
    ∃ a ∈ P, ∃ y : ℕ → B, Tendsto y atTop (𝓝 0) ∧ ∀ k, (x k).val = y k * a := by
  have hxB : Tendsto (fun k => (x k).val) atTop (𝓝 0) := by
    simpa using P.subtypeL.continuous.tendsto (0 : P) |>.comp hx
  let X := cohenNullSequence (fun k => (x k).val) hxB
  obtain ⟨a, ha, y, hy⟩ := cohen_factor_nullSequence P hclosed hleft hM hAI X (fun k => (x k).property)
  refine ⟨a, ha, y, ?_, hy⟩
  simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using y.zero_at_infty'

end JLMS
