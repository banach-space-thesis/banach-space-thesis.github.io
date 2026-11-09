import CKEUPFP.OperatorFields
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.UrysohnsLemma

/-!
# Contractive vector-valued extension on the Cantor set

Mathlib constructs a continuous retraction onto every nonempty closed subset
of a countable product of discrete spaces. Composition with this retraction
extends vector-valued continuous functions and has norm at most one. A Urysohn
cutoff gives the supported extension used in the paper's Cantor-set proof.
This construction uses no scalar extension theorem and requires no completeness
or separability assumption on the range space.
-/

noncomputable section

namespace CKEUPFP

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section Pullback

variable {K L : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace L] [CompactSpace L]

/-- Pullback along a continuous map between compact spaces is contractive. -/
def compactPullback (g : C(K, L)) : C(L, E) →L[𝕜] C(K, E) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.comp g
      map_add' := by intro f h; ext k; rfl
      map_smul' := by intro c f; ext k; rfl }
    1 (fun f => by
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
      intro k
      exact f.norm_coe_le_norm (g k))

@[simp]
theorem compactPullback_apply (g : C(K, L)) (f : C(L, E)) (k : K) :
    compactPullback (𝕜 := 𝕜) g f k = f (g k) := rfl

theorem norm_compactPullback_le (g : C(K, L)) :
    ‖compactPullback (𝕜 := 𝕜) (E := E) g‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Pullback

section Cantor

variable {D : Set (ℕ → Fin 2)}

/-- A continuous retraction onto a nonempty closed Cantor subset. -/
def cantorClosedRetraction (hD : IsClosed D) (hne : D.Nonempty) : C((ℕ → Fin 2), D) :=
  ⟨(PiNat.exists_retraction_subtype_of_isClosed hD hne).choose,
    (PiNat.exists_retraction_subtype_of_isClosed hD hne).choose_spec.2.2⟩

@[simp]
theorem cantorClosedRetraction_fixed (hD : IsClosed D) (hne : D.Nonempty) (d : D) :
    cantorClosedRetraction hD hne d = d :=
  (PiNat.exists_retraction_subtype_of_isClosed hD hne).choose_spec.1 d

variable [CompactSpace D]

/-- Restrict a continuous function to the compact subtype. -/
def cantorRestriction : C((ℕ → Fin 2), E) →L[𝕜] C(D, E) :=
  compactPullback ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem cantorRestriction_apply (f : C((ℕ → Fin 2), E)) (d : D) :
    cantorRestriction (𝕜 := 𝕜) f d = f d := rfl

theorem norm_cantorRestriction_le :
    ‖cantorRestriction (𝕜 := 𝕜) (D := D) (E := E)‖ ≤ 1 :=
  norm_compactPullback_le _

/-- Contractive linear extension obtained by composition with the retraction. -/
def cantorClosedExtend (hD : IsClosed D) (hne : D.Nonempty) :
    C(D, E) →L[𝕜] C((ℕ → Fin 2), E) :=
  compactPullback (cantorClosedRetraction hD hne)

theorem norm_cantorClosedExtend_le (hD : IsClosed D) (hne : D.Nonempty) :
    ‖cantorClosedExtend (𝕜 := 𝕜) (E := E) hD hne‖ ≤ 1 :=
  norm_compactPullback_le _

@[simp]
theorem cantorClosedExtend_on_subset (hD : IsClosed D) (hne : D.Nonempty)
    (f : C(D, E)) (d : D) :
    cantorClosedExtend (𝕜 := 𝕜) hD hne f d = f d := by
  change f (cantorClosedRetraction hD hne d) = f d
  rw [cantorClosedRetraction_fixed]

theorem cantorClosedExtend_right_inverse (hD : IsClosed D) (hne : D.Nonempty) :
    (cantorRestriction (𝕜 := 𝕜)).comp (cantorClosedExtend hD hne) =
      ContinuousLinearMap.id 𝕜 C(D, E) := by
  ext f d
  exact cantorClosedExtend_on_subset (𝕜 := 𝕜) hD hne f d

variable {O : Set (ℕ → Fin 2)}

omit [CompactSpace D] in
theorem cantorSupportedCutoff_exists (hD : IsClosed D) (hO : IsOpen O) (hDO : D ⊆ O) :
    ∃ φ : C((ℕ → Fin 2), ℝ),
      Set.EqOn φ 0 Oᶜ ∧ Set.EqOn φ 1 D ∧ ∀ k, φ k ∈ Set.Icc (0 : ℝ) 1 := by
  apply exists_continuous_zero_one_of_isClosed hO.isClosed_compl hD
  exact Set.disjoint_left.mpr (fun _ hk hd => hk (hDO hd))

/-- A scalar cutoff equal to one on `D` and zero outside `O`. -/
def cantorSupportedCutoff (hD : IsClosed D) (hO : IsOpen O) (hDO : D ⊆ O) :
    C((ℕ → Fin 2), ℝ) :=
  (cantorSupportedCutoff_exists hD hO hDO).choose

omit [CompactSpace D] in
theorem cantorSupportedCutoff_spec (hD : IsClosed D) (hO : IsOpen O) (hDO : D ⊆ O) :
    Set.EqOn (cantorSupportedCutoff hD hO hDO) 0 Oᶜ ∧
      Set.EqOn (cantorSupportedCutoff hD hO hDO) 1 D ∧
      ∀ k, cantorSupportedCutoff hD hO hDO k ∈ Set.Icc (0 : ℝ) 1 :=
  (cantorSupportedCutoff_exists hD hO hDO).choose_spec

def cantorSupportedExtendValue (hD : IsClosed D) (hne : D.Nonempty)
    (hO : IsOpen O) (hDO : D ⊆ O) (f : C(D, E)) : C((ℕ → Fin 2), E) :=
  ⟨fun k => (cantorSupportedCutoff hD hO hDO k : 𝕜) •
      f (cantorClosedRetraction hD hne k),
    (RCLike.continuous_ofReal.comp (cantorSupportedCutoff hD hO hDO).continuous).smul
      (f.continuous.comp (cantorClosedRetraction hD hne).continuous)⟩

theorem norm_cantorSupportedExtendValue_le (hD : IsClosed D) (hne : D.Nonempty)
    (hO : IsOpen O) (hDO : D ⊆ O) (f : C(D, E)) :
    ‖cantorSupportedExtendValue (𝕜 := 𝕜) hD hne hO hDO f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
  intro k
  change ‖(cantorSupportedCutoff hD hO hDO k : 𝕜) •
    f (cantorClosedRetraction hD hne k)‖ ≤ ‖f‖
  have hφ := (cantorSupportedCutoff_spec hD hO hDO).2.2 k
  rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hφ.1]
  calc
    cantorSupportedCutoff hD hO hDO k * ‖f (cantorClosedRetraction hD hne k)‖ ≤
        1 * ‖f (cantorClosedRetraction hD hne k)‖ :=
      mul_le_mul_of_nonneg_right hφ.2 (norm_nonneg _)
    _ ≤ ‖f‖ := by simpa using f.norm_coe_le_norm (cantorClosedRetraction hD hne k)

/-- The paper's supported extension for a closed subset of the Cantor host. -/
def cantorSupportedExtend (hD : IsClosed D) (hne : D.Nonempty)
    (hO : IsOpen O) (hDO : D ⊆ O) : C(D, E) →L[𝕜] C((ℕ → Fin 2), E) :=
  LinearMap.mkContinuous
    { toFun := cantorSupportedExtendValue (𝕜 := 𝕜) hD hne hO hDO
      map_add' := by intro f g; ext k; simp [cantorSupportedExtendValue, smul_add]
      map_smul' := by
        intro c f
        ext k
        change (cantorSupportedCutoff hD hO hDO k : 𝕜) •
          (c • f (cantorClosedRetraction hD hne k)) =
          c • ((cantorSupportedCutoff hD hO hDO k : 𝕜) •
            f (cantorClosedRetraction hD hne k))
        exact smul_comm _ c _ }
    1 (fun f => by
      simpa using norm_cantorSupportedExtendValue_le (𝕜 := 𝕜) hD hne hO hDO f)

theorem norm_cantorSupportedExtend_le (hD : IsClosed D) (hne : D.Nonempty)
    (hO : IsOpen O) (hDO : D ⊆ O) :
    ‖cantorSupportedExtend (𝕜 := 𝕜) (E := E) hD hne hO hDO‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

@[simp]
theorem cantorSupportedExtend_on_subset (hD : IsClosed D) (hne : D.Nonempty)
    (hO : IsOpen O) (hDO : D ⊆ O) (f : C(D, E)) (d : D) :
    cantorSupportedExtend (𝕜 := 𝕜) hD hne hO hDO f d = f d := by
  change (cantorSupportedCutoff hD hO hDO d : 𝕜) •
    f (cantorClosedRetraction hD hne d) = f d
  rw [cantorClosedRetraction_fixed, (cantorSupportedCutoff_spec hD hO hDO).2.1 d.property]
  simp

theorem cantorSupportedExtend_right_inverse (hD : IsClosed D) (hne : D.Nonempty)
    (hO : IsOpen O) (hDO : D ⊆ O) :
    (cantorRestriction (𝕜 := 𝕜)).comp (cantorSupportedExtend hD hne hO hDO) =
      ContinuousLinearMap.id 𝕜 C(D, E) := by
  ext f d
  exact cantorSupportedExtend_on_subset (𝕜 := 𝕜) hD hne hO hDO f d

theorem cantorSupportedExtend_vanishesOff (hD : IsClosed D) (hne : D.Nonempty)
    (hO : IsOpen O) (hDO : D ⊆ O) (f : C(D, E)) :
    VanishesOff O (cantorSupportedExtend (𝕜 := 𝕜) hD hne hO hDO f) := by
  intro k hk
  change (cantorSupportedCutoff hD hO hDO k : 𝕜) •
    f (cantorClosedRetraction hD hne k) = 0
  rw [(cantorSupportedCutoff_spec hD hO hDO).1 hk]
  simp

/-- The supported Dugundji conclusion needed after reducing the host to Cantor. -/
theorem cantor_supported_contractive_extension (hD : IsClosed D) (hne : D.Nonempty)
    (hO : IsOpen O) (hDO : D ⊆ O) :
    ∃ J : C(D, E) →L[𝕜] C((ℕ → Fin 2), E),
      ‖J‖ ≤ 1 ∧ (cantorRestriction (𝕜 := 𝕜)).comp J =
        ContinuousLinearMap.id 𝕜 C(D, E) ∧ ∀ f, VanishesOff O (J f) :=
  ⟨cantorSupportedExtend hD hne hO hDO,
    norm_cantorSupportedExtend_le (𝕜 := 𝕜) hD hne hO hDO,
    cantorSupportedExtend_right_inverse (𝕜 := 𝕜) hD hne hO hDO,
    cantorSupportedExtend_vanishesOff (𝕜 := 𝕜) hD hne hO hDO⟩

/-- The same conclusion includes the empty closed subset. -/
theorem cantor_supported_contractive_extension_all (hD : IsClosed D)
    (hO : IsOpen O) (hDO : D ⊆ O) :
    ∃ J : C(D, E) →L[𝕜] C((ℕ → Fin 2), E),
      ‖J‖ ≤ 1 ∧ (cantorRestriction (𝕜 := 𝕜)).comp J =
        ContinuousLinearMap.id 𝕜 C(D, E) ∧ ∀ f, VanishesOff O (J f) := by
  classical
  rcases D.eq_empty_or_nonempty with hEmpty | hne
  · haveI : IsEmpty D := ⟨fun d => by simpa only [hEmpty, Set.mem_empty_iff_false] using d.property⟩
    refine ⟨0, by simp, ?_, ?_⟩
    · apply ContinuousLinearMap.ext
      intro f
      ext d
      exact isEmptyElim d
    · intro f k _
      rfl
  · exact cantor_supported_contractive_extension hD hne hO hDO

end Cantor

end CKEUPFP
