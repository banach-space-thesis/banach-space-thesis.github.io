import CKEUPFP.CantorShells
import ThesisCommon.Analysis.CZeroStrongRows
import ThesisCommon.Analysis.CZeroColumnOperators
import ThesisCommon.Analysis.IntervalCZeroEquiv

/-! An explicit complemented copy of `c₀(C(Cantor,E))` inside
`C(Cantor,E)`. The read map subtracts the value at the zero sequence and
has norm at most two. The insert map pastes functions onto the disjoint
clopen shells and has norm at most one. Uniformly null inputs give a
convergent series in the actual supremum norm. -/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace CKEUPFP

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def cantorAnchor : C(CantorSpace, E) →L[𝕜] C(CantorSpace, E) :=
  LinearMap.mkContinuous
    { toFun := fun f => ContinuousMap.const CantorSpace (f 0)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun f => by
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
      intro t
      exact f.norm_coe_le_norm 0)

@[simp] theorem cantorAnchor_apply (f : C(CantorSpace, E)) (t : CantorSpace) :
    cantorAnchor (𝕜 := 𝕜) f t = f 0 := rfl

theorem norm_cantorAnchor_le : ‖cantorAnchor (𝕜 := 𝕜) (E := E)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def cantorShellRead (n : ℕ) : C(CantorSpace, E) →L[𝕜] C(CantorSpace, E) :=
  compactPullback (cantorShellEmbedding n) - cantorAnchor

@[simp] theorem cantorShellRead_apply (n : ℕ) (f : C(CantorSpace, E)) (t : CantorSpace) :
    cantorShellRead (𝕜 := 𝕜) n f t = f (cantorShellEmbedding n t) - f 0 := rfl

theorem norm_cantorShellRead_le (n : ℕ) :
    ‖cantorShellRead (𝕜 := 𝕜) (E := E) n‖ ≤ 2 := by
  have h₁ := norm_compactPullback_le (𝕜 := 𝕜) (E := E) (cantorShellEmbedding n)
  have h₂ := norm_cantorAnchor_le (𝕜 := 𝕜) (E := E)
  exact (norm_sub_le _ _).trans (by linarith)

theorem cantorShellRead_tendsto_zero (f : C(CantorSpace, E)) :
    Tendsto (fun n => cantorShellRead (𝕜 := 𝕜) n f) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  let V : Set CantorSpace := {x | ‖f x - f 0‖ < ε / 2}
  have hV : IsOpen V := isOpen_lt (f.continuous.sub continuous_const).norm continuous_const
  have hz : (0 : CantorSpace) ∈ V := by dsimp [V]; simp; positivity
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hV 0 hz
  refine ⟨I.sup id + 1, ?_⟩
  intro n hn
  rw [dist_zero_right]
  apply lt_of_le_of_lt ?_ (by linarith : ε / 2 < ε)
  apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ ε / 2)).2
  intro t
  have ht : cantorShellEmbedding n t ∈ V := by
    apply hsub
    intro k hk
    have hkI : k ∈ I := hk
    have hkN : k ≤ I.sup id := Finset.le_sup (f := id) hkI
    have hkn : k < n := by omega
    change (if k < n then 0 else if k = n then 1 else _) ∈ u k
    rw [if_pos hkn]
    exact (hu k hkI).2
  exact ht.le

def cantorCZeroRead : C(CantorSpace, E) →L[𝕜]
    ThesisCommon.CZeroSum C(CantorSpace, E) :=
  ThesisCommon.cZeroStrongRows cantorShellRead 2 (by norm_num)
    norm_cantorShellRead_le cantorShellRead_tendsto_zero

@[simp] theorem cantorCZeroRead_apply (f : C(CantorSpace, E)) (n : ℕ) :
    cantorCZeroRead (𝕜 := 𝕜) f n = cantorShellRead (𝕜 := 𝕜) n f := rfl

theorem norm_cantorCZeroRead_le :
    ‖cantorCZeroRead (𝕜 := 𝕜) (E := E)‖ ≤ 2 := ThesisCommon.norm_cZeroStrongRows_le ..

def cantorShellInsert (n : ℕ) : C(CantorSpace, E) →L[𝕜] C(CantorSpace, E) :=
  (cantorSupportedExtend (isClosed_cantorShell n) (cantorShell_nonempty n)
    (isOpen_cantorShell n) (Set.Subset.refl _)).comp
    (compactPullback (cantorShellRestrictedTail n))

theorem norm_cantorShellInsert_le (n : ℕ) :
    ‖cantorShellInsert (𝕜 := 𝕜) (E := E) n‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul (norm_cantorSupportedExtend_le (𝕜 := 𝕜) (E := E)
    (isClosed_cantorShell n) (cantorShell_nonempty n) (isOpen_cantorShell n)
      (Set.Subset.refl _)) (norm_compactPullback_le (𝕜 := 𝕜) (E := E) _)
    (norm_nonneg _) zero_le_one).trans (by norm_num)

theorem cantorShellInsert_zero (n : ℕ) (f : C(CantorSpace, E))
    {t : CantorSpace} (ht : t ∉ cantorShell n) :
    cantorShellInsert (𝕜 := 𝕜) n f t = 0 :=
  cantorSupportedExtend_vanishesOff (isClosed_cantorShell n) (cantorShell_nonempty n)
    (isOpen_cantorShell n) (Set.Subset.refl _)
      (compactPullback (𝕜 := 𝕜) (cantorShellRestrictedTail n) f) t ht

@[simp] theorem cantorShellInsert_embedding (n : ℕ) (f : C(CantorSpace, E))
    (t : CantorSpace) :
    cantorShellInsert (𝕜 := 𝕜) n f (cantorShellEmbedding n t) = f t := by
  change cantorSupportedExtend (𝕜 := 𝕜) _ _ _ _
    (compactPullback (cantorShellRestrictedTail n) f)
      (⟨cantorShellEmbedding n t, cantorShellEmbedding_mem n t⟩ : cantorShell n) = f t
  rw [cantorSupportedExtend_on_subset]
  change f (cantorShellTail n (cantorShellEmbedding n t)) = f t
  rw [cantorShellTail_embedding]

theorem cantorShellInsert_disjoint (i j : ℕ) (hij : i ≠ j)
    (f g : C(CantorSpace, E)) (t : CantorSpace) :
    cantorShellInsert (𝕜 := 𝕜) i f t = 0 ∨ cantorShellInsert (𝕜 := 𝕜) j g t = 0 := by
  by_cases hi : t ∈ cantorShell i
  · right
    exact cantorShellInsert_zero j g
      (fun hj => Set.disjoint_left.mp (cantorShell_disjoint hij) hi hj)
  · exact Or.inl (cantorShellInsert_zero i f hi)

theorem vectorContinuousMap_disjoint_finiteColumnBound
    {X K : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [TopologicalSpace K] [CompactSpace K]
    (F : ℕ → X →L[𝕜] C(K, E)) (hF : ∀ n, ‖F n‖ ≤ 1)
    (hdis : ∀ i j, i ≠ j → ∀ (x y : X) t, F i x t = 0 ∨ F j y t = 0) :
    ThesisCommon.CZeroFiniteColumnBound F 1 := by
  classical
  intro s x b hb hx
  simp only [one_mul]
  apply (ContinuousMap.norm_le _ hb).2
  intro t
  change ‖(ContinuousMap.evalCLM 𝕜 t) (∑ i ∈ s, F i (x i))‖ ≤ b
  rw [map_sum]
  change ‖∑ i ∈ s, F i (x i) t‖ ≤ b
  by_cases h : ∃ i ∈ s, F i (x i) t ≠ 0
  · obtain ⟨i, hi, hne⟩ := h
    rw [Finset.sum_eq_single_of_mem i hi]
    · calc
        ‖F i (x i) t‖ ≤ ‖F i (x i)‖ := (F i (x i)).norm_coe_le_norm t
        _ ≤ ‖F i‖ * ‖x i‖ := (F i).le_opNorm _
        _ ≤ 1 * ‖x i‖ := mul_le_mul_of_nonneg_right (hF i) (norm_nonneg (x i))
        _ ≤ b := by simpa using hx i hi
    · intro j _hj hji
      exact (hdis i j hji.symm (x i) (x j) t).resolve_left hne
  · have hz : ∀ i ∈ s, F i (x i) t = 0 := by simpa using h
    rw [Finset.sum_eq_zero hz, norm_zero]
    exact hb

variable [CompleteSpace E]

def cantorCZeroInsert : ThesisCommon.CZeroSum C(CantorSpace, E) →L[𝕜]
    C(CantorSpace, E) :=
  ThesisCommon.cZeroColumns (cantorShellInsert (𝕜 := 𝕜) (E := E)) 1 zero_le_one
    (vectorContinuousMap_disjoint_finiteColumnBound (𝕜 := 𝕜) (E := E) cantorShellInsert
      norm_cantorShellInsert_le cantorShellInsert_disjoint)

theorem norm_cantorCZeroInsert_le :
    ‖cantorCZeroInsert (𝕜 := 𝕜) (E := E)‖ ≤ 1 := ThesisCommon.norm_cZeroColumns_le ..

omit [CompleteSpace E] in
theorem cantorShellRead_comp_insert (m n : ℕ) :
    (cantorShellRead (𝕜 := 𝕜) (E := E) m).comp (cantorShellInsert n) =
      if m = n then ContinuousLinearMap.id 𝕜 C(CantorSpace, E) else 0 := by
  ext f t
  have hz := cantorShellInsert_zero (𝕜 := 𝕜) n f (zero_not_mem_cantorShell n)
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl]
    change cantorShellInsert n f (cantorShellEmbedding n t) - cantorShellInsert n f 0 = f t
    rw [hz, sub_zero, cantorShellInsert_embedding]
  · rw [if_neg hmn]
    change cantorShellInsert n f (cantorShellEmbedding m t) - cantorShellInsert n f 0 = 0
    rw [hz, sub_zero]
    exact cantorShellInsert_zero n f
      (fun hn => Set.disjoint_left.mp (cantorShell_disjoint hmn)
        (cantorShellEmbedding_mem m t) hn)

private theorem strongRows_columns_identity
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (R : ℕ → Y →L[𝕜] X) (F : ℕ → X →L[𝕜] Y)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hR : ∀ n, ‖R n‖ ≤ a) (hz : ∀ y, Tendsto (fun n => R n y) atTop (𝓝 0))
    (hF : ThesisCommon.CZeroFiniteColumnBound F b)
    (hRF : ∀ m n, (R m).comp (F n) = if m = n then ContinuousLinearMap.id 𝕜 X else 0) :
    (ThesisCommon.cZeroStrongRows R a ha hR hz).comp
      (ThesisCommon.cZeroColumns F b hb hF) =
        ContinuousLinearMap.id 𝕜 (ThesisCommon.CZeroSum X) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ZeroAtInftyContinuousMap.ext
  intro n
  change R n (∑' i, F i (x i)) = x n
  have hs := ThesisCommon.cZero_columns_summable F hb hF x
  rw [(R n).map_tsum hs, tsum_eq_single n]
  · rw [← ContinuousLinearMap.comp_apply, hRF, if_pos rfl, ContinuousLinearMap.id_apply]
  · intro i hin
    rw [← ContinuousLinearMap.comp_apply, hRF, if_neg hin.symm, ContinuousLinearMap.zero_apply]

theorem cantorCZeroRead_comp_insert :
    (cantorCZeroRead (𝕜 := 𝕜) (E := E)).comp (cantorCZeroInsert (𝕜 := 𝕜)) =
      ContinuousLinearMap.id 𝕜 (ThesisCommon.CZeroSum C(CantorSpace, E)) := by
  unfold cantorCZeroRead cantorCZeroInsert
  exact strongRows_columns_identity (𝕜 := 𝕜)
    (cantorShellRead (E := E)) cantorShellInsert 2 1 (by norm_num) zero_le_one
    norm_cantorShellRead_le cantorShellRead_tendsto_zero
    (vectorContinuousMap_disjoint_finiteColumnBound (𝕜 := 𝕜) (E := E) cantorShellInsert
      norm_cantorShellInsert_le cantorShellInsert_disjoint) cantorShellRead_comp_insert

/-- A proved isomorphism, obtained from the explicit two bounded maps. -/
def cantorCZeroEquiv : C(CantorSpace, E) ≃L[𝕜]
    ThesisCommon.CZeroSum C(CantorSpace, E) :=
  ThesisCommon.cZeroEquivOfRetraction (cantorCZeroRead (𝕜 := 𝕜) (E := E))
    (cantorCZeroInsert (𝕜 := 𝕜))
    (fun x => DFunLike.congr_fun (cantorCZeroRead_comp_insert (𝕜 := 𝕜) (E := E)) x)

end CKEUPFP
