import ThesisCommon.Analysis.GowersMaureySimultaneousAverages
import ThesisCommon.Analysis.CommonFunctionalPartition

/-! Source Lemma 9's actual continuous bad-vector selection on a compact
operator set. The finite cover, all RIS averages and the common detecting
functional are constructed from the genuine block operator seminorm. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_continuous_bad_vectors_on_compact
    (D : ConstructionData 𝕜) (Y : Submodule 𝕜 (ShiftSpace D))
    (T : Y →L[𝕜] ShiftSpace D) (A : Set (Y →L[𝕜] ShiftSpace D)) (hA : IsCompact A)
    {ε : ℝ} (hε : 0 < ε)
    (hbad : ∀ U ∈ A, 17*ε < blockOperatorSeminorm D Y (T-U))
    (B n : ℕ) (hn : 0 < n) :
    ∃ y : C(A,Y), ∀ U : A, ∃ z : C00 𝕜,
      (y U : ShiftSpace D) = denseEmbedding D z ∧
      z ∈ afterCutoff B ∧ intervalNorm D n z ≤ 8 ∧
      8*ε < ‖(T-U.val) (y U)‖ := by
  classical
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  obtain ⟨s,p₀,hp₀,hs₀,hnear₀⟩ := exists_finite_metric_partition (K := A)
    (ε := ε/8) (by positivity)
  let k := Fintype.card s
  let e : Fin k ≃ s := (Fintype.equivFin s).symm
  let p (i : Fin k) := p₀ (e i)
  let U₀ (i : Fin k) : Y →L[𝕜] ShiftSpace D := (e i).val.val
  have hp (i : Fin k) (x : A) : 0 ≤ p i x := hp₀ _ _
  have hs (x : A) : ∑ i, p i x = 1 := by
    exact (e.sum_comp (fun i => p₀ i x)).trans (hs₀ x)
  let m := max k (n^2)
  have hindex : m ≤ D.j (2*m+1) := (by omega : m ≤ 2*m+1).trans (D.j_strict.id_le _)
  have hk : k ≤ D.j (2*m+1) := (le_max_left _ _).trans hindex
  have hnN : (n : ℝ) ≤ Real.sqrt (D.j (2*m+1) : ℝ) := by
    have hsquare : (n : ℝ)^2 ≤ (D.j (2*m+1) : ℝ) := by
      exact_mod_cast (le_max_right k (n^2)).trans hindex
    have hsqrt := Real.sq_sqrt (Nat.cast_nonneg (D.j (2*m+1)))
    have hsqrt0 := Real.sqrt_nonneg (D.j (2*m+1) : ℝ)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  obtain ⟨z,v,φ,hval,hzB,hv,hinterval,hφ,hdet⟩ := exists_simultaneous_bad_averages
    D Y (fun i => T-U₀ i) (by positivity : 0 ≤ 17*ε)
    (show 0 < ε/4 by positivity) (fun i => hbad _ (e i).val.property) B m hk
  let y : C(A,Y) := partitionWeightedVector (𝕜 := 𝕜) p v
  have hnear (x : A) (i : Fin k) (hi : 0 < p i x) : ‖U₀ i-x.val‖ ≤ ε/16 := by
    have hh := hnear₀ (e i) x (ne_of_gt hi)
    change ‖x.val-U₀ i‖ < (ε/8)/2 at hh
    rw [norm_sub_rev x.val (U₀ i)] at hh
    convert hh.le using 1; ring
  have hdetect (i : Fin k) :
      16*ε+2*(ε/16)*4 < RCLike.re (φ ((T-U₀ i) (v i))) := by
    have hh := hdet i
    linarith
  refine ⟨y,?_⟩
  intro U
  let w : C00 𝕜 := ∑ i, (p i U : ℝ) • z i
  have hsm (c : ℝ) (x : C00 𝕜) : c • x = (c : 𝕜) • x := by
    ext j
    simp only [Finsupp.smul_apply,smul_eq_mul,RCLike.real_smul_eq_coe_mul]
  have hw : (y U : ShiftSpace D) = denseEmbedding D w := by
    change Y.subtypeL (partitionWeightedVector (𝕜 := 𝕜) p v U) = _
    simp only [partitionWeightedVector_apply,map_sum,map_smul,Submodule.subtypeL_apply,hval,
      w,hsm]
  have hwB : w ∈ afterCutoff B :=
    Submodule.sum_mem _ (fun i _ => (afterCutoff B).smul_mem _ (hzB i))
  have hwn : intervalNorm D n w ≤ 8 := by
    simp only [w,hsm]
    exact seminorm_positive_weighted_sum_le (intervalNorm D n) (fun i => p i U) z
      (fun i => hp i U) (hs U) (fun i => hinterval i n hn hnN)
  have hnorm := norm_partition_operator_gt_of_common_functional p v T U₀ Subtype.val φ
    (by norm_num : (0 : ℝ)<2) (show 0 ≤ ε/16 by positivity) hφ hp hs hv hnear hdetect U
  refine ⟨w,hw,hwB,hwn,?_⟩
  convert hnorm using 1; ring

end ThesisCommon.GowersMaurey
