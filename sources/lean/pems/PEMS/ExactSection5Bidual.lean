import PEMS.DeBlasiResiduum
import ThesisCommon.Analysis.RCLikeEllOneSchurFunctional

/-! The two bidual measures in Corollary 5.14, on actual weak-star closures
and cluster sets. For operator images the sharp ℓ¹ factorization supplies
the lower bound directly: every cluster of the factored unit vectors stays
at the full factorization distance from the canonical image of the range. -/

noncomputable section
open Set Filter Topology ThesisCommon
open scoped BigOperators

namespace PEMS

set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

local instance : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

local instance : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 E) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

local instance : HasQuotient (StrongDual 𝕜 (StrongDual 𝕜 E))
    (Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))) :=
  @Submodule.hasQuotient 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E))
    inferInstance inferInstance inferInstance

private abbrev WeakStarBidual (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] := WeakDual 𝕜 (StrongDual 𝕜 E)

def section5BidualEmbed (x : E) : WeakStarBidual 𝕜 E :=
  weakBidualInclusion (toWeakSpace 𝕜 E x)

@[simp] theorem section5BidualEmbed_toStrongDual (x : E) :
    WeakDual.toStrongDual (section5BidualEmbed (𝕜 := 𝕜) x) =
      NormedSpace.inclusionInDoubleDual 𝕜 E x := rfl

/-- Norm distance to the canonical image of E, expressed as the norm in the
actual quotient of the strong bidual. The argument has the weak-star topology. -/
def section5BidualDistance (ξ : WeakStarBidual 𝕜 E) : ℝ :=
  ‖(Submodule.Quotient.mk (WeakDual.toStrongDual ξ) : ResiduumSpace 𝕜 E)‖

theorem section5BidualDistance_eq_infDist (ξ : WeakStarBidual 𝕜 E) :
    section5BidualDistance ξ = Metric.infDist (WeakDual.toStrongDual ξ)
      (Set.range (NormedSpace.inclusionInDoubleDual 𝕜 E)) := by
  change ‖(QuotientAddGroup.mk (WeakDual.toStrongDual ξ) :
    StrongDual 𝕜 (StrongDual 𝕜 E) ⧸ (bidualImage 𝕜 E).toAddSubgroup)‖ = _
  exact QuotientAddGroup.norm_mk _

def section5WeakStarClusters (u : ℕ → E) : Set (WeakStarBidual 𝕜 E) :=
  {ξ | MapClusterPt ξ atTop (section5BidualEmbed ∘ u)}

def section5SequenceClusterDistance (u : ℕ → E) : ℝ :=
  sInf (section5BidualDistance '' section5WeakStarClusters (𝕜 := 𝕜) u)

/-- The paper's wk quantity, the supremal bidual distance on the weak-star
closure. Adjoining zero makes the empty-set convention explicit. -/
def section5Wk (A : Set E) : ℝ :=
  sSup (insert 0 (section5BidualDistance '' closure (section5BidualEmbed (𝕜 := 𝕜) '' A)))

/-- The paper's wck quantity, using the infimal distance of each sequential
cluster set to the canonical image of E. -/
def section5Wck (A : Set E) : ℝ :=
  sSup (insert 0 {r : ℝ | ∃ u : ℕ → E, (∀ n, u n ∈ A) ∧
    r = section5SequenceClusterDistance (𝕜 := 𝕜) u})

private theorem section5_cluster_exists (u : ℕ → E) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C) :
    (section5WeakStarClusters (𝕜 := 𝕜) u).Nonempty := by
  let B : Set (WeakStarBidual 𝕜 E) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C
  have hB : IsCompact B :=
    WeakDual.isCompact_closedBall 𝕜 (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) C
  have hmem : ∀ n, (section5BidualEmbed (𝕜 := 𝕜) ∘ u) n ∈ B := by
    intro n
    change dist (WeakDual.toStrongDual (section5BidualEmbed (𝕜 := 𝕜) (u n))) 0 ≤ C
    rw [dist_zero_right, section5BidualEmbed_toStrongDual]
    change ‖NormedSpace.inclusionInDoubleDualLi 𝕜 (u n)‖ ≤ C
    simpa only [LinearIsometry.norm_map] using hu n
  obtain ⟨ξ, _, hξ⟩ := hB.exists_mapClusterPt
    (Filter.le_principal_iff.mpr (show ∀ᶠ n in atTop,
      (section5BidualEmbed (𝕜 := 𝕜) ∘ u) n ∈ B from Filter.Eventually.of_forall hmem))
  exact ⟨ξ, hξ⟩

private theorem section5_cluster_mem_closure {A : Set E} {u : ℕ → E}
    (hu : ∀ n, u n ∈ A) {ξ : WeakStarBidual 𝕜 E}
    (hξ : ξ ∈ section5WeakStarClusters u) :
    ξ ∈ closure (section5BidualEmbed '' A) := by
  change MapClusterPt ξ atTop (section5BidualEmbed ∘ u) at hξ
  exact (hξ.clusterPt.mono (Filter.le_principal_iff.mpr
    (show ∀ᶠ n in atTop, (section5BidualEmbed (𝕜 := 𝕜) ∘ u) n ∈ section5BidualEmbed '' A
      from Filter.Eventually.of_forall (fun n => ⟨u n, hu n, rfl⟩)))).mem_closure

private theorem section5_wk_term_le_residuum (T : E →L[𝕜] F)
    {ξ : WeakStarBidual 𝕜 F}
    (hξ : ξ ∈ closure (section5BidualEmbed '' (T '' Metric.closedBall 0 1))) :
    section5BidualDistance ξ ≤ residuumNorm T := by
  let B : Set (WeakStarBidual 𝕜 E) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1
  have hB : IsCompact B :=
    WeakDual.isCompact_closedBall 𝕜 (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) 1
  have hs : section5BidualEmbed '' (T '' Metric.closedBall 0 1) ⊆ weakStarBidualMap T '' B := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨section5BidualEmbed (𝕜 := 𝕜) x, ?_, weakStarBidualMap_inclusion T x⟩
    change dist (WeakDual.toStrongDual (section5BidualEmbed (𝕜 := 𝕜) x)) 0 ≤ 1
    rw [dist_zero_right, section5BidualEmbed_toStrongDual]
    change ‖NormedSpace.inclusionInDoubleDualLi 𝕜 x‖ ≤ 1
    simpa using hx
  obtain ⟨η, hη, rfl⟩ := closure_minimal hs (hB.image (weakStarBidualMap T).continuous).isClosed hξ
  have hη' : ‖WeakDual.toStrongDual η‖ ≤ 1 := by
    simpa only [B, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hη
  change ‖residuumOperator T (Submodule.Quotient.mk (WeakDual.toStrongDual η))‖ ≤ residuumNorm T
  exact ((residuumOperator T).le_opNorm _).trans
    (mul_le_of_le_one_right (norm_nonneg _) ((Submodule.Quotient.norm_mk_le _ _).trans hη'))

private theorem section5_wk_values_bddAbove (T : E →L[𝕜] F) :
    BddAbove (insert 0 (section5BidualDistance '' closure
      (section5BidualEmbed (𝕜 := 𝕜) '' (T '' Metric.closedBall 0 1)))) := by
  refine ⟨residuumNorm T, ?_⟩
  rintro _ (rfl | ⟨ξ, hξ, rfl⟩)
  · exact residuumNorm_nonneg T
  · exact section5_wk_term_le_residuum T hξ

theorem section5Wk_le_deBlasiOperator (T : E →L[𝕜] F) :
    section5Wk (𝕜 := 𝕜) (T '' Metric.closedBall 0 1) ≤ deBlasiOperator T := by
  apply le_trans _ (residuumNorm_le_deBlasiOperator T)
  apply csSup_le (insert_nonempty _ _)
  rintro _ (rfl | ⟨ξ, hξ, rfl⟩)
  · exact residuumNorm_nonneg T
  · exact section5_wk_term_le_residuum T hξ

private theorem section5_wck_term_le_wk (T : E →L[𝕜] F) (u : ℕ → F)
    (hu : ∀ n, u n ∈ T '' Metric.closedBall 0 1) :
    section5SequenceClusterDistance (𝕜 := 𝕜) u ≤ section5Wk (𝕜 := 𝕜) (T '' Metric.closedBall 0 1) := by
  have hb (n : ℕ) : ‖u n‖ ≤ ‖T‖ := by
    obtain ⟨x, hx, he⟩ := hu n
    rw [← he]
    exact (T.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg _) (by simpa using hx))
  obtain ⟨ξ, hξ⟩ := section5_cluster_exists (𝕜 := 𝕜) u hb
  have hbd : BddBelow (section5BidualDistance '' section5WeakStarClusters (𝕜 := 𝕜) u) :=
    ⟨0, by rintro _ ⟨η, _, rfl⟩; exact norm_nonneg _⟩
  exact (csInf_le hbd (mem_image_of_mem section5BidualDistance hξ)).trans
    (le_csSup (section5_wk_values_bddAbove T)
      (mem_insert_of_mem _ (mem_image_of_mem section5BidualDistance (section5_cluster_mem_closure hu hξ))))

private theorem section5_wck_values_bddAbove (T : E →L[𝕜] F) :
    BddAbove (insert 0 {r : ℝ | ∃ u : ℕ → F, (∀ n, u n ∈ T '' Metric.closedBall 0 1) ∧
      r = section5SequenceClusterDistance (𝕜 := 𝕜) u}) := by
  refine ⟨section5Wk (𝕜 := 𝕜) (T '' Metric.closedBall 0 1), ?_⟩
  rintro _ (rfl | ⟨u, hu, rfl⟩)
  · exact le_csSup (section5_wk_values_bddAbove T) (mem_insert _ _)
  · exact section5_wck_term_le_wk T u hu

theorem section5Wck_le_wkOperator (T : E →L[𝕜] F) :
    section5Wck (𝕜 := 𝕜) (T '' Metric.closedBall 0 1) ≤
      section5Wk (𝕜 := 𝕜) (T '' Metric.closedBall 0 1) := by
  apply csSup_le (insert_nonempty _ _)
  rintro _ (rfl | ⟨u, hu, rfl⟩)
  · exact le_csSup (section5_wk_values_bddAbove T) (mem_insert _ _)
  · exact section5_wck_term_le_wk T u hu

private theorem section5_test_single_nat (b : ℕ → 𝕜) (hb : ∀ n, ‖b n‖ ≤ 1)
    (i : ℕ) (a : 𝕜) : scalarEllOneTest b hb (lp.single 1 i a) = b i * a := by
  have h := scalarEllOneTest_single b hb i a
  rw [show Classical.decEq ℕ = instDecidableEqNat from Subsingleton.elim _ _] at h
  exact h

private theorem section5_scaled_ellOne_cluster_distance (a : 𝕜)
    {ξ : WeakStarBidual 𝕜 (EllOne 𝕜)}
    (hξ : ξ ∈ section5WeakStarClusters (fun n : ℕ => lp.single 1 n a)) :
    ‖a‖ ≤ section5BidualDistance ξ := by
  rw [section5BidualDistance_eq_infDist]
  apply (Metric.le_infDist (range_nonempty _)).mpr
  rintro _ ⟨x, rfl⟩
  rw [dist_eq_norm]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨s, hs⟩ := scalar_ellOne_exists_finite_approx x hε
  rw [show Classical.decEq ℕ = instDecidableEqNat from Subsingleton.elim _ _] at hs
  let b (n : ℕ) : 𝕜 := if n ∈ s then 0 else 1
  have hb (n : ℕ) : ‖b n‖ ≤ 1 := by by_cases hn : n ∈ s <;> simp [b, hn]
  let g := scalarEllOneTest b hb
  have hg : ‖g‖ ≤ 1 := g.opNorm_le_bound zero_le_one (fun y => by
    simpa only [one_mul, g] using scalarEllOneTest_bound b hb y)
  have hfinite : g (∑ i ∈ s, lp.single 1 i (x i)) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero (fun i hi => by simp [g, section5_test_single_nat, b, hi])
  have hsmall : ‖g x‖ < ε := by
    have hn := scalarEllOneTest_bound b hb (x - ∑ i ∈ s, lp.single 1 i (x i))
    change ‖g (x - ∑ i ∈ s, lp.single 1 i (x i))‖ ≤ _ at hn
    rw [map_sub, hfinite, sub_zero] at hn
    exact hn.trans_lt hs
  have ha : ξ g = a := by
    change MapClusterPt ξ atTop (section5BidualEmbed ∘ fun n : ℕ => lp.single 1 n a) at hξ
    have hcomp := hξ.continuousAt_comp (WeakDual.eval_continuous g).continuousAt
    have he : (fun n : ℕ => (section5BidualEmbed (𝕜 := 𝕜) (lp.single 1 n a)) g) =ᶠ[atTop]
        fun _ => a := by
      filter_upwards [eventually_gt_atTop (s.sup id)] with n hn
      have hns : n ∉ s := fun h => (not_lt_of_ge (Finset.le_sup (f := id) h)) hn
      change g (lp.single 1 n a) = a
      simp [g, section5_test_single_nat, b, hns]
    have hc := he.mapClusterPt_iff.mp hcomp
    have hp : Filter.map (fun _ : ℕ => a) atTop ≤ 𝓟 ({a} : Set 𝕜) :=
      Filter.le_principal_iff.mpr (show ∀ᶠ n : ℕ in atTop, (fun _ : ℕ => a) n ∈ ({a} : Set 𝕜)
        from Filter.Eventually.of_forall (fun _ => Set.mem_singleton a))
    have hs : ClusterPt (ξ g) (𝓟 ({a} : Set 𝕜)) := hc.clusterPt.mono
      hp
    simpa only [isClosed_singleton.closure_eq, mem_singleton_iff] using hs.mem_closure
  have heval : ‖a - g x‖ ≤ ‖WeakDual.toStrongDual ξ - NormedSpace.inclusionInDoubleDual 𝕜 _ x‖ := by
    have hh := ((WeakDual.toStrongDual ξ - NormedSpace.inclusionInDoubleDual 𝕜 _ x).le_opNorm g).trans
      (mul_le_of_le_one_right (norm_nonneg _) hg)
    change ‖ξ g - g x‖ ≤ _ at hh
    simpa only [ha] using hh
  linarith [norm_le_norm_sub_add a (g x)]

theorem section5_ellOne_factorization_constant_le_wck
    (T : E →L[𝕜] F) (U : F →L[𝕜] EllOne 𝕜) (V : EllOne 𝕜 →L[𝕜] E)
    (hfac : U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 (EllOne 𝕜)) :
    ‖U‖⁻¹ * ‖V‖⁻¹ ≤ section5Wck (𝕜 := 𝕜) (T '' Metric.closedBall 0 1) := by
  have h0 : 0 ≤ section5Wck (𝕜 := 𝕜) (T '' Metric.closedBall 0 1) :=
    le_csSup (section5_wck_values_bddAbove T) (mem_insert _ _)
  by_cases hU : ‖U‖ = 0
  · simpa [hU] using h0
  by_cases hV : ‖V‖ = 0
  · simpa [hV] using h0
  have hUp : 0 < ‖U‖ := lt_of_le_of_ne (norm_nonneg U) (Ne.symm hU)
  let a : 𝕜 := (‖V‖⁻¹ : ℝ)
  have ha : ‖a‖ = ‖V‖⁻¹ := by simp [a]
  let x (n : ℕ) := a • V (lp.single 1 n 1)
  let u (n : ℕ) := T (x n)
  have hx (n : ℕ) : ‖x n‖ ≤ 1 := by
    have h := V.le_opNorm (lp.single 1 n 1)
    rw [lp.norm_single (by simp : (0 : ENNReal) < 1), norm_one, mul_one] at h
    rw [show ‖x n‖ = ‖a‖ * ‖V (lp.single 1 n 1)‖ by rw [norm_smul], ha]
    exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (norm_nonneg V))).trans_eq
      (inv_mul_cancel₀ hV)
  have hux (n : ℕ) : U (u n) = lp.single 1 n a := by
    have h := DFunLike.congr_fun hfac (lp.single 1 n 1)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    simp only [u, x, map_smul, h]
    apply Subtype.ext
    funext i
    by_cases hi : i = n <;> simp [lp.single_apply, Pi.single_apply, hi]
  have hb (n : ℕ) : ‖u n‖ ≤ ‖T‖ :=
    (T.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) (hx n))
  have hu (n : ℕ) : u n ∈ T '' Metric.closedBall 0 1 := ⟨x n, by simpa using hx n, rfl⟩
  apply le_trans _ (le_csSup (section5_wck_values_bddAbove T) (mem_insert_of_mem _ ⟨u, hu, rfl⟩))
  apply le_csInf ((section5_cluster_exists (𝕜 := 𝕜) u hb).image _)
  rintro _ ⟨ξ, hξ, rfl⟩
  have hm : weakStarBidualMap U ξ ∈ section5WeakStarClusters (fun n : ℕ => lp.single 1 n a) := by
    change MapClusterPt ξ atTop (section5BidualEmbed ∘ u) at hξ
    have h := hξ.continuousAt_comp (weakStarBidualMap U).continuous.continuousAt
    have he : (weakStarBidualMap U : _ → _) ∘ (section5BidualEmbed ∘ u) =
        section5BidualEmbed ∘ (fun n : ℕ => lp.single 1 n a) := by
      funext n
      simp only [Function.comp_apply, section5BidualEmbed, weakStarBidualMap_inclusion, hux]
    rw [he] at h
    exact h
  have hle := section5_scaled_ellOne_cluster_distance a hm
  have hnorm : section5BidualDistance (weakStarBidualMap U ξ) ≤ ‖U‖ * section5BidualDistance ξ := by
    change ‖residuumOperator U (Submodule.Quotient.mk (WeakDual.toStrongDual ξ))‖ ≤
      ‖U‖ * section5BidualDistance ξ
    exact ((residuumOperator U).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (residuumNorm_le_norm U) (norm_nonneg _))
  rw [ha] at hle
  have hdiv : ‖V‖⁻¹ / ‖U‖ ≤ section5BidualDistance ξ :=
    (div_le_iff₀ hUp).mpr (by simpa only [mul_comm ‖U‖] using hle.trans hnorm)
  simpa only [div_eq_inv_mul] using hdiv

theorem section5_factorizationSup_le_wckOperator (T : E →L[𝕜] F) :
    factorizationSup (EllOne 𝕜) T ≤ section5Wck (𝕜 := 𝕜) (T '' Metric.closedBall 0 1) := by
  apply csSup_le (insert_nonempty _ _)
  rintro _ (rfl | ⟨U, V, hfac, rfl⟩)
  · exact le_csSup (section5_wck_values_bddAbove T) (mem_insert _ _)
  · exact section5_ellOne_factorization_constant_le_wck T U V hfac

end PEMS
