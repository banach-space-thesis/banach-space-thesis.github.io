import ThesisCommon.Analysis.GowersMaureySeparatedOrbitWitnesses
import ThesisCommon.Analysis.GowersMaureyNPairConstruction
import ThesisCommon.Analysis.GowersMaureyNPairOperatorBounds

/-! Genuine detecting N-pairs for every odd construction size, after any
specified coordinate cutoff. Both the detecting operator and the finite
spread orbit are evaluated on actual vectors of the original subspace.
All off-diagonal estimates come from the constructed witness sequence. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_detecting_NPair
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (hne : ∀ i, u.vector i ≠ 0)
    (T : Y →L[𝕜] ShiftSpace D) (q : ℕ → ℕ) (hq : StrictMono q)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ i, ∀ z ∈ spreadVectorOrbit D (u.vector i) (q i),
      ε ≤ ‖T (u.inSubspace i)-z‖) (m B : ℕ) :
    ∃ x : C00 𝕜, ∃ hx : denseEmbedding D x ∈ Y, ∃ a : C00 𝕜,
      x ∈ afterCutoff B ∧ a ∈ afterCutoff B ∧ implicitNorm D x ≤ 4 ∧
      (∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.sqrt (D.j (2*m+1) : ℝ) →
        intervalNorm D n x ≤ 8) ∧
      AveragedFunctional (implicitNorm D) (D.j (2*m+1)) a ∧ a ≠ 0 ∧
      ε/8 < RCLike.re (completedPairing D a (T ⟨denseEmbedding D x,hx⟩)) ∧
      ∀ z ∈ spreadParameterSquare (D.j (2*m+1)),
        ‖pairing a (spread z.1 z.2 x)‖ ≤ ‖T‖ / (D.j (2*m+1) : ℝ)^2 := by
  classical
  let N := D.j (2*m+1)
  have hN : 0 < N := D.j_positive _
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let η : ℝ := ε / (16*N)
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hNr)
  let weight (_ : ℕ) := Real.sqrt η
  obtain ⟨S⟩ := exists_separated_orbit_witness_sequence u hne T q hq hε hsep weight
    (fun _ => Real.sqrt_pos.mpr hη)
  let L := N^2+B+1
  let v (i : ℕ) := u.vector (S.index (L+i))
  let a (i : ℕ) := S.functional (L+i)
  have hv : ∀ i j, i < j → Before (v i) (v j) :=
    fun i j hij => u.successive _ _ (S.index_strict (Nat.add_lt_add_left hij L))
  have ha : ∀ i j, i < j → Before (a i) (a j) :=
    fun i j hij => S.successive _ _ (Nat.add_lt_add_left hij L)
  have hvnorm (i : ℕ) : intervalNorm D (i+1) (v i) ≤ 1 := by
    apply (intervalNorm_mono D (show i+1 ≤ S.index (L+i)+1 from ?_) _).trans
      (u.norm_bound _)
    have hh : L+i ≤ S.index (L+i) := S.index_strict.id_le (L+i)
    omega
  obtain ⟨b,hb,hRIS,hnorm,hinterval,havg,_⟩ := exists_NPair_subsequence D v a hv ha
    (fun i => hne _) hvnorm (fun i => S.dualUnit _) m
  let c (i : Fin N) := L+b i
  have hc : StrictMono c := fun i j hij => Nat.add_lt_add_left (hb hij) L
  let U (i : Fin N) : Y := u.inSubspace (S.index (c i))
  let A (i : Fin N) := S.functional (c i)
  let x := normalizedPairVector (fun i : Fin N => v (b i))
  let f := averagedPairFunctional A
  let xY : Y := normalizedPairSum (𝕜 := 𝕜) U
  have hxY : (xY : ShiftSpace D) = denseEmbedding D x :=
    normalizedPairSum_subspace_value D Y U (fun i : Fin N => v (b i)) (fun _ => rfl)
  have hx : denseEmbedding D x ∈ Y := hxY ▸ xY.property
  have hxYe : xY = (⟨denseEmbedding D x,hx⟩ : Y) := Subtype.ext hxY
  have hvB (i : Fin N) : v (b i) ∈ afterCutoff B := by
    intro j hj
    apply Finsupp.notMem_support_iff.mp
    intro hji
    have h1 := block_index_le_support u.vector u.successive hne (S.index (c i)) j hji
    have h2 : c i ≤ S.index (c i) := S.index_strict.id_le (c i)
    have h3 : B < c i := by dsimp only [c,L]; omega
    omega
  have haB (i : Fin N) : A i ∈ afterCutoff B := by
    intro j hj
    apply Finsupp.notMem_support_iff.mp
    intro hji
    have hh := block_index_le_support S.functional S.successive S.nonzero (c i) j hji
    dsimp only [c,L] at hh
    omega
  have hxB : x ∈ afterCutoff B :=
    (afterCutoff B).smul_mem _ (Submodule.sum_mem _ (fun i _ => hvB i))
  have hfB : f ∈ afterCutoff B :=
    (afterCutoff B).smul_mem _ (Submodule.sum_mem _ (fun i _ => haB i))
  have hentry (i j : Fin N) (hij : i ≠ j) :
      ‖completedPairing D (A i) (T (U j))‖ ≤ η := by
    have he : weight (S.rank (c i)) * weight (S.rank (c j)) = η := Real.mul_self_sqrt hη.le
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ((S.cross_image _ _ (hc hlt)).1).le.trans_eq he
    · have hh := ((S.cross_image _ _ (hc hgt)).2).le
      simpa only [weight, Real.mul_self_sqrt hη.le] using hh
  have hrow (i : Fin N) :
      ∑ j ∈ Finset.univ.erase i, ‖completedPairing D (A i) (T (U j))‖ ≤ ε/16 := by
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, η := Finset.sum_le_sum (fun j hj =>
        hentry i j (Finset.ne_of_mem_erase hj).symm)
      _ ≤ ∑ _j : Fin N, η := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset i Finset.univ) (fun _ _ _ => hη.le)
      _ = ε/16 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, η]; field_simp
  have hdetect : ε/8 < RCLike.re (completedPairing D f (T xY)) := by
    have hh := normalizedPairSum_re_lower_bound D hN A U T
      (fun i => (S.detected (c i)).le) hrow
    change ε/4-ε/16 ≤ RCLike.re (completedPairing D f (T xY)) at hh
    linarith
  have hf0 : f ≠ 0 := by
    intro hz
    have hh : RCLike.re (completedPairing D f (T xY)) = 0 := by simp [hz]
    rw [hh] at hdetect
    linarith
  refine ⟨x,hx,f,hxB,hfB,hnorm,hinterval,havg,hf0,?_,?_⟩
  · simpa only [hxYe] using hdetect
  intro z hz
  let V : Y →L[𝕜] ShiftSpace D := (completedSpread D z.1 z.2).comp Y.subtypeL
  have hvpair (i j : Fin N) : completedPairing D (A i) (V (U j)) =
      pairing (S.functional (c i)) (spread z.1 z.2 (u.vector (S.index (c j)))) := by
    change completedPairing D (A i)
      (completedSpread D z.1 z.2 (denseEmbedding D (u.vector (S.index (c j))))) = _
    rw [completedSpread_denseEmbedding, completedPairing_denseEmbedding]
    rfl
  have hrank (i : Fin N) : N^2 ≤ S.rank (c i) := by
    have hh : c i ≤ S.rank (c i) := S.rank_strict.id_le (c i)
    exact (show N^2 ≤ c i by dsimp only [c,L]; omega).trans hh
  have hrankN (i : Fin N) : N ≤ S.rank (c i) := by
    have hh := hrank i
    nlinarith
  have hdiag (i : Fin N) : ‖completedPairing D (A i) (V (U i))‖ ≤ ‖T‖/(N : ℝ)^2 := by
    rw [hvpair]
    apply (S.orbit_small (c i) z (spreadParameterSquare_mono (hrankN i) hz)).trans
    apply div_le_div_of_nonneg_left (norm_nonneg T) (sq_pos_of_pos hNr)
    exact_mod_cast hrank i
  have hzero (i j : Fin N) (hij : i ≠ j) : completedPairing D (A i) (V (U j)) = 0 := by
    rw [hvpair]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (S.cross_spread _ _ (hc hlt) z
        (spreadParameterSquare_mono (hrankN i) hz)).1
    · exact (S.cross_spread _ _ (hc hgt) z
        (spreadParameterSquare_mono (hrankN j) hz)).2
  have hrowV (i : Fin N) :
      ∑ j ∈ Finset.univ.erase i, ‖completedPairing D (A i) (V (U j))‖ ≤ 0 := by
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro j hj
    rw [hzero i j (Finset.ne_of_mem_erase hj).symm, norm_zero]
  have hh := normalizedPairSum_norm_le_of_row_bounds D hN A U V hdiag hrowV
  change ‖completedPairing D f (V xY)‖ ≤ ‖T‖/(N : ℝ)^2+0 at hh
  have he : completedPairing D f (V xY) = pairing f (spread z.1 z.2 x) := by
    change completedPairing D f (completedSpread D z.1 z.2 (xY : ShiftSpace D)) = _
    rw [hxY, completedSpread_denseEmbedding, completedPairing_denseEmbedding]
    rfl
  simpa only [he, add_zero] using hh

end ThesisCommon.GowersMaurey
