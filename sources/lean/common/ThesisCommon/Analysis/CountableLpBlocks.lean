import ThesisCommon.Analysis.CountableTriangularPartition
import ThesisCommon.Analysis.LpTriangularSupport

/-! Actual lp triangular block decompositions from countable outgoing
coordinate supports. Every invariance and compression assertion is proved
from the first-unused-point partition and the lp finite-sum expansion. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] Classical.decEq
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem exists_lp_triangular_countable_blocks (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (P : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p) (hP : P.comp P = P)
    (F : Γ → Set Γ) (hF : ∀ α, (F α).Countable)
    (hsupport : ∀ α (x : X), ∀ β ∉ F α, P (lp.single p α x) β = 0) :
    ∃ B : (Cardinal.mk Γ).ord.toType → Set Γ,
      (Pairwise (fun α β => Disjoint (B α) (B β)) ∧
        (∀ α, (B α).Countable) ∧ (⋃ α, B α) = Set.univ) ∧
      (∀ α, ∀ x : lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (B α),
        ∀ γ ∉ ⋃ β ≤ α, B β, P x γ = 0) ∧
      (∀ α, (lpBlockCompression p P (B α)).comp (lpBlockCompression p P (B α)) =
        lpBlockCompression p P (B α)) ∧
      (∀ α, {β : (Cardinal.mk Γ).ord.toType | β < α ∧
        ((lpCoordinateProjection (𝕜 := 𝕜) p (B β)).comp P).comp
          (lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (B α)).subtypeL ≠ 0}.Countable) := by
  classical
  obtain ⟨B, hdisj, hcount, hcover, htri⟩ := countable_triangular_partition F hF
  let D (i : (Cardinal.mk Γ).ord.toType) : Set Γ := ⋃ j < i, B j
  have hprev (i : (Cardinal.mk Γ).ord.toType) (x : Γ) (hx : x ∈ D i) : F x ⊆ D i := by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hji, hxj⟩ := Set.mem_iUnion.mp hj
    intro y hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (htri j x hxj hy)
    obtain ⟨hkj, hyk⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hkj.trans_lt hji, hyk⟩⟩
  have hcurrent (i : (Cardinal.mk Γ).ord.toType) (x : Γ) (hx : x ∈ B i) :
      F x ⊆ B i ∪ D i := by
    intro y hy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (htri i x hx hy)
    obtain ⟨hji, hyj⟩ := Set.mem_iUnion.mp hj
    rcases lt_or_eq_of_le hji with hji | rfl
    · exact Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hji, hyj⟩⟩)
    · exact Or.inl hyj
  have hBD (i : (Cardinal.mk Γ).ord.toType) : Disjoint (B i) (D i) := by
    apply Set.disjoint_left.mpr
    intro x hxi hxD
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxD
    obtain ⟨hji, hxj⟩ := Set.mem_iUnion.mp hj
    exact Set.disjoint_left.mp (hdisj hji.ne') hxi hxj
  have hcurrentP (i : (Cardinal.mk Γ).ord.toType) :
      ∀ x : lp (fun _ : Γ => X) p, (∀ γ ∉ B i, x γ = 0) →
        ∀ γ ∉ B i ∪ D i, P x γ = 0 := by
    apply lp_operator_supported_of_single p hp P (B i) (B i ∪ D i)
    intro α hα x β hβ
    exact hsupport α x β (fun h => hβ (hcurrent i α hα h))
  have hprevP (i : (Cardinal.mk Γ).ord.toType) :
      ∀ x : lp (fun _ : Γ => X) p, (∀ γ ∉ D i, x γ = 0) →
        ∀ γ ∉ D i, P x γ = 0 := by
    apply lp_operator_supported_of_single p hp P (D i) (D i)
    intro α hα x β hβ
    exact hsupport α x β (fun h => hβ (hprev i α hα h))
  refine ⟨B, ⟨hdisj, hcount, hcover⟩, ?_, ?_, ?_⟩
  · intro i x
    apply lp_operator_supported_of_single p hp P (B i) (⋃ j ≤ i, B j) ?_ x.val x.property
    intro α hα y β hβ
    exact hsupport α y β (fun h => hβ (htri i α hα h))
  · intro i
    exact lpBlockCompression_idempotent_of_triangular p P hP (B i) (D i) (hBD i)
      (hcurrentP i) (hprevP i)
  · intro i
    let S : Set Γ := ⋃ α ∈ B i, F α
    have hS : S.Countable := (hcount i).biUnion (fun α _ => hF α)
    have hPS : ∀ x : lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (B i),
        ∀ γ ∉ S, P x γ = 0 := by
      intro x
      apply lp_operator_supported_of_single p hp P (B i) S ?_ x.val x.property
      intro α hα y β hβ
      exact hsupport α y β (fun h => hβ (Set.mem_iUnion.mpr
        ⟨α, Set.mem_iUnion.mpr ⟨hα, h⟩⟩))
    exact (countable_lp_block_entries p P (B i) B hdisj S hS hPS).mono (fun _ h => h.2)

end ThesisCommon
