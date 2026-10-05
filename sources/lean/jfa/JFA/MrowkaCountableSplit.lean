import JFA.CountableMrowkaTails
import JFA.MrowkaFamilyCoordinates
import JFA.MrowkaNaturalKernel

/-! A concrete bounded splitting for functions whose family-point support is
contained in a countable subfamily. Disjoint tails lift the family values;
the remainder vanishes on the whole family and is read on the natural points.
Joining the two discrete C₀ coordinates reproduces the original function. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Set
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}
variable {D : Type*} [TopologicalSpace D] [DiscreteTopology D]
variable (S : Set 𝒜) [Countable S]
local instance countableSplitSelectedTopology : TopologicalSpace S := ⊥
local instance countableSplitSelectedDiscrete : DiscreteTopology S := ⟨rfl⟩
variable (h𝒜 : IsAlmostDisjoint 𝒜)

def mrowkaSelectedTail : S → Finset ℕ :=
  Classical.choose (exists_pairwise_disjoint_mrowka_tails h𝒜 (Subtype.val : S → 𝒜)
    Subtype.val_injective)

theorem mrowkaSelectedTail_disjoint : Pairwise fun A B : S =>
    Disjoint (mrowkaNeighborhood 𝒜 A.val (mrowkaSelectedTail S h𝒜 A))
      (mrowkaNeighborhood 𝒜 B.val (mrowkaSelectedTail S h𝒜 B)) :=
  Classical.choose_spec (exists_pairwise_disjoint_mrowka_tails h𝒜 (Subtype.val : S → 𝒜)
    Subtype.val_injective)

def mrowkaFamilyIndicator (q : D × S) : C₀(D × Mrowka 𝒜, 𝕜) :=
  JLMS.clopenIndicator ({q.1} ×ˢ mrowkaNeighborhood 𝒜 q.2.val (mrowkaSelectedTail S h𝒜 q.2))
    ((isClopen_discrete _).prod (mrowka_isClopen_neighborhood h𝒜 _ _))
    (isCompact_singleton.prod (mrowka_isCompact_neighborhood _ _))

theorem mrowkaFamilyIndicator_unit (q : D × S) :
    ‖mrowkaFamilyIndicator (𝕜 := 𝕜) S h𝒜 q‖ ≤ 1 := JLMS.norm_clopenIndicator_le _ _ _

theorem mrowkaFamilyIndicator_disjoint : Pairwise fun q r : D × S =>
    Disjoint (Function.support (mrowkaFamilyIndicator (𝕜 := 𝕜) S h𝒜 q))
      (Function.support (mrowkaFamilyIndicator (𝕜 := 𝕜) S h𝒜 r)) := by
  intro q r hqr
  have hs (q : D × S) : Function.support (mrowkaFamilyIndicator (𝕜 := 𝕜) S h𝒜 q) ⊆
      {q.1} ×ˢ mrowkaNeighborhood 𝒜 q.2.val (mrowkaSelectedTail S h𝒜 q.2) := by
    intro p hp
    by_contra hpq
    exact hp (by simp only [mrowkaFamilyIndicator, JLMS.clopenIndicator_apply, if_neg hpq])
  apply disjoint_left.mpr
  intro p hpq hpr
  have hq := hs q hpq
  have hr := hs r hpr
  have hfirst : q.1 = r.1 := hq.1.symm.trans hr.1
  by_cases hsecond : q.2 = r.2
  · exact hqr (Prod.ext hfirst hsecond)
  · exact disjoint_left.mp (mrowkaSelectedTail_disjoint S h𝒜 hsecond) hq.2 hr.2

def mrowkaFamilyLift : C₀(D × S, 𝕜) →L[𝕜] C₀(D × Mrowka 𝒜, 𝕜) :=
  disjointCzeroSynthesis (mrowkaFamilyIndicator (𝕜 := 𝕜) (D := D) S h𝒜)
    (mrowkaFamilyIndicator_unit (𝕜 := 𝕜) (D := D) S h𝒜)
    (mrowkaFamilyIndicator_disjoint (𝕜 := 𝕜) (D := D) S h𝒜)

@[simp] theorem mrowkaFamilyLift_selected (a : C₀(D × S, 𝕜)) (q : D × S) :
    mrowkaFamilyLift (𝕜 := 𝕜) S h𝒜 a (q.1, Sum.inr q.2.val) = a q := by
  classical
  apply disjointCzeroSynthesis_apply_coordinate
  intro r
  have hmem : (q.1, Sum.inr q.2.val) ∈
      ({r.1} ×ˢ mrowkaNeighborhood 𝒜 r.2.val (mrowkaSelectedTail S h𝒜 r.2)) ↔ r = q := by
    simp only [mem_prod, mem_singleton_iff]
    constructor
    · rintro ⟨hf, hs⟩
      have hvals := (mrowka_inr_mem r.2.val q.2.val (mrowkaSelectedTail S h𝒜 r.2)).mp hs
      exact Prod.ext hf.symm (Subtype.ext hvals.symm)
    · intro h
      cases h
      exact ⟨rfl, (mrowka_inr_mem _ _ _).mpr rfl⟩
  simp only [mrowkaFamilyIndicator, JLMS.clopenIndicator_apply, hmem]
  split_ifs <;> rfl

@[simp] theorem mrowkaFamilyLift_outside (a : C₀(D × S, 𝕜)) (d : D) (B : 𝒜)
    (hB : B ∉ S) : mrowkaFamilyLift (𝕜 := 𝕜) S h𝒜 a (d, Sum.inr B) = 0 := by
  apply disjointCzeroSynthesis_apply_zero
  intro q
  have hp : (d, Sum.inr B) ∉ {q.1} ×ˢ
      mrowkaNeighborhood 𝒜 q.2.val (mrowkaSelectedTail S h𝒜 q.2) := by
    intro hp
    have heq := (mrowka_inr_mem _ _ _).mp hp.2
    exact hB (heq.symm ▸ q.2.property)
  simp only [mrowkaFamilyIndicator, JLMS.clopenIndicator_apply, if_neg hp]

def mrowkaSupportedSubmodule : Submodule 𝕜 C₀(D × Mrowka 𝒜, 𝕜) where
  carrier := {f | ∀ d A, A ∉ S → f (d, Sum.inr A) = 0}
  zero_mem' := by
    change ∀ d A, A ∉ S → (0 : C₀(D × Mrowka 𝒜, 𝕜)) (d, Sum.inr A) = 0
    intros; rfl
  add_mem' := by intro f g hf hg d A hA; change f (d, Sum.inr A) + g (d, Sum.inr A) = 0; rw [hf d A hA, hg d A hA, add_zero]
  smul_mem' := by intro a f hf d A hA; change a • f (d, Sum.inr A) = 0; rw [hf d A hA, smul_zero]

omit [DiscreteTopology D] [Countable S] in
theorem mrowkaSupportedSubmodule_isClosed :
    IsClosed (mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S :
      Set C₀(D × Mrowka 𝒜, 𝕜)) := by
  have heq : (mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S :
      Set C₀(D × Mrowka 𝒜, 𝕜)) =
      ⋂ d : D, ⋂ A : 𝒜, ⋂ (_hA : A ∉ S), {f | f (d, Sum.inr A) = 0} := by
    ext f
    simp only [mem_iInter, mem_setOf_eq]
    rfl
  rw [heq]
  apply isClosed_iInter
  intro d
  apply isClosed_iInter
  intro A
  apply isClosed_iInter
  intro _hA
  exact isClosed_eq
    (BoundedContinuousFunction.continuous_eval_const.comp
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous) continuous_const

theorem mrowkaFamilyRemainder_mem_naturalKernel
    (f : mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S) :
    f.val - mrowkaFamilyLift S h𝒜 (mrowkaFamilyRead S f.val) ∈
      mrowkaNaturalKernel (𝕜 := 𝕜) (𝒜 := 𝒜) (D := D) := by
  change ∀ d A, f.val (d, Sum.inr A) -
    mrowkaFamilyLift S h𝒜 (mrowkaFamilyRead S f.val) (d, Sum.inr A) = 0
  intro d A
  by_cases hA : A ∈ S
  · have h := mrowkaFamilyLift_selected S h𝒜 (mrowkaFamilyRead S f.val) (d, ⟨A, hA⟩)
    rw [h]
    exact sub_self _
  · rw [mrowkaFamilyLift_outside S h𝒜 _ d A hA, f.property d A hA, sub_self]

def mrowkaFamilyRemainderL : mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S →L[𝕜]
    mrowkaNaturalKernel (𝕜 := 𝕜) (𝒜 := 𝒜) (D := D) :=
  ((mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S).subtypeL -
    (mrowkaFamilyLift S h𝒜).comp ((mrowkaFamilyRead S).comp
      (mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S).subtypeL)).codRestrict _
      (mrowkaFamilyRemainder_mem_naturalKernel S h𝒜)

def mrowkaSupportSplit : mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S →L[𝕜]
    (C₀(D × ℕ, 𝕜) × C₀(D × S, 𝕜)) :=
  (mrowkaNaturalRead.comp (mrowkaFamilyRemainderL S h𝒜)).prod
    ((mrowkaFamilyRead S).comp (mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S).subtypeL)

def mrowkaSupportJoin : (C₀(D × ℕ, 𝕜) × C₀(D × S, 𝕜)) →L[𝕜] C₀(D × Mrowka 𝒜, 𝕜) :=
  (mrowkaNaturalLift h𝒜).coprod (mrowkaFamilyLift S h𝒜)

theorem mrowkaSupportJoin_split :
    (mrowkaSupportJoin (𝕜 := 𝕜) (D := D) S h𝒜).comp (mrowkaSupportSplit S h𝒜) =
      (mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := D) S).subtypeL := by
  apply ContinuousLinearMap.ext
  intro f
  change mrowkaNaturalLift (𝕜 := 𝕜) h𝒜 (mrowkaNaturalRead (mrowkaFamilyRemainderL S h𝒜 f)) +
    mrowkaFamilyLift S h𝒜 (mrowkaFamilyRead S f.val) = f.val
  rw [mrowkaNaturalLift_read]
  exact sub_add_cancel _ _

end JFA
