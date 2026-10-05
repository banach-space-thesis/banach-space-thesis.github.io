import Sigma.Topology
import Sigma.JLAlgebra
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.DenseEmbedding

/-! Identification of JL(B) with C(K_B) by restriction to the isolated base. -/
noncomputable section
open Set Topology
namespace SigmaNonprimarity
attribute [local instance] Classical.propDecidable Classical.decEq

def restrictToBase (B : Set (Set Point)) : C(AUCompactum B, ℝ) →ₐ[ℝ] Ambient where
  toFun f := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun p => f (↑(Sum.inl p : MrowkaBase B))) ‖f‖ (fun p => f.norm_coe_le_norm _)
  map_zero' := by ext p; rfl
  map_one' := by ext p; rfl
  map_add' := by intros; ext p; rfl
  map_mul' := by intros; ext p; rfl
  commutes' := by intro r; ext p; rfl

@[simp] theorem restrictToBase_apply (B : Set (Set Point)) (f : C(AUCompactum B, ℝ)) (p : Point) :
    restrictToBase B f p = f (↑(Sum.inl p : MrowkaBase B)) := rfl

theorem restrictToBase_norm_le (B : Set (Set Point)) (f : C(AUCompactum B, ℝ)) :
    ‖restrictToBase B f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr (fun p => f.norm_coe_le_norm _)

def restrictToBaseCLM (B : Set (Set Point)) : C(AUCompactum B, ℝ) →L[ℝ] Ambient :=
  (restrictToBase B).toLinearMap.mkContinuous 1 (by intro f; simpa using restrictToBase_norm_le B f)

theorem restrictToBase_norm {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (f : C(AUCompactum B, ℝ)) : ‖restrictToBase B f‖ = ‖f‖ := by
  apply le_antisymm (restrictToBase_norm_le B f)
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  exact (compactumBaseDense hB hInf).induction_on x
    (isClosed_le f.continuous.norm continuous_const)
    (fun p => (restrictToBase B f).norm_coe_le_norm p)

def restrictToBaseIsometry {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    C(AUCompactum B, ℝ) →ₗᵢ[ℝ] Ambient where
  toLinearMap := (restrictToBase B).toLinearMap
  norm_map' := restrictToBase_norm hB hInf

def liftedSingleton (B : Set (Set Point)) (p : Point) : Set (AUCompactum B) :=
  ((↑) : MrowkaBase B → AUCompactum B) '' {Sum.inl p}

def liftedTail (B : Set (Set Point)) (b : B) : Set (AUCompactum B) :=
  ((↑) : MrowkaBase B → AUCompactum B) '' tailNeighborhood B b ∅

theorem isClopen_liftedSingleton {B : Set (Set Point)} (hB : AlmostDisjoint B) (p : Point) :
    IsClopen (liftedSingleton B p) := by
  letI := mrowkaT2 hB
  exact ⟨(isCompact_singleton.image OnePoint.continuous_coe).isClosed,
    OnePoint.isOpen_image_coe.mpr (isOpen_base_singleton B p)⟩

theorem isClopen_liftedTail {B : Set (Set Point)} (hB : AlmostDisjoint B) (b : B) :
    IsClopen (liftedTail B b) := by
  letI := mrowkaT2 hB
  exact ⟨((isCompact_tail B b ∅).image OnePoint.continuous_coe).isClosed,
    OnePoint.isOpen_image_coe.mpr (isOpen_tail B b ∅)⟩

def singletonFunction {B : Set (Set Point)} (hB : AlmostDisjoint B) (p : Point) :
    C(AUCompactum B, ℝ) :=
  (BoundedContinuousFunction.indicator _ (isClopen_liftedSingleton hB p)).toContinuousMap

def tailFunction {B : Set (Set Point)} (hB : AlmostDisjoint B) (b : B) :
    C(AUCompactum B, ℝ) :=
  (BoundedContinuousFunction.indicator _ (isClopen_liftedTail hB b)).toContinuousMap

theorem restrict_singletonFunction {B : Set (Set Point)} (hB : AlmostDisjoint B) (p : Point) :
    restrictToBase B (singletonFunction hB p) = characteristic {p} := by
  classical
  ext q
  change (liftedSingleton B p).indicator (fun _ => (1 : ℝ)) (↑(Sum.inl q : MrowkaBase B)) = _
  simp [liftedSingleton, Set.indicator_apply]

theorem restrict_tailFunction {B : Set (Set Point)} (hB : AlmostDisjoint B) (b : B) :
    restrictToBase B (tailFunction hB b) = characteristic b.val := by
  classical
  ext q
  change (liftedTail B b).indicator (fun _ => (1 : ℝ)) (↑(Sum.inl q : MrowkaBase B)) = _
  simp [liftedTail, Set.indicator_apply]

theorem jl_le_restriction_range {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (hInf : B.Infinite) : JL B ≤ LinearMap.range (restrictToBase B).toLinearMap := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    intro f hf
    rcases hf with (⟨p, rfl⟩ | ⟨b, hb, rfl⟩) | rfl
    · exact ⟨singletonFunction hB p, restrict_singletonFunction hB p⟩
    · exact ⟨tailFunction hB ⟨b, hb⟩, restrict_tailFunction hB ⟨b, hb⟩⟩
    · exact ⟨1, by simp⟩
  · exact (restrictToBaseIsometry hB hInf).isometry.isClosedEmbedding.isClosed_range

@[simp] theorem singletonFunction_apply {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (p : Point) (x : AUCompactum B) :
    singletonFunction hB p x =
      if x = (↑(Sum.inl p : MrowkaBase B) : AUCompactum B) then 1 else 0 := by
  classical
  change (liftedSingleton B p).indicator (fun _ => (1 : ℝ)) x = _
  simp [liftedSingleton, Set.indicator_apply]

@[simp] theorem tailFunction_infty {B : Set (Set Point)} (hB : AlmostDisjoint B) (b : B) :
    tailFunction hB b OnePoint.infty = 0 := by
  change (liftedTail B b).indicator (fun _ => (1 : ℝ)) OnePoint.infty = _
  simp [liftedTail]

@[simp] theorem tailFunction_inr {B : Set (Set Point)} (hB : AlmostDisjoint B) (b c : B) :
    tailFunction hB b (↑(Sum.inr c : MrowkaBase B)) = if c = b then 1 else 0 := by
  classical
  change (liftedTail B b).indicator (fun _ => (1 : ℝ)) (↑(Sum.inr c : MrowkaBase B)) = _
  simp [liftedTail, Set.indicator_apply]

def restrictionAlgebra {B : Set (Set Point)} (hB : AlmostDisjoint B) :
    Subalgebra ℝ C(AUCompactum B, ℝ) := (jlAlgebra hB).comap (restrictToBase B)

theorem restrictionAlgebra_separates {B : Set (Set Point)} (hB : AlmostDisjoint B) :
    (restrictionAlgebra hB).SeparatesPoints := by
  classical
  have hs (p : Point) : singletonFunction hB p ∈ restrictionAlgebra hB := by
    change restrictToBase B (singletonFunction hB p) ∈ JL B
    rw [restrict_singletonFunction]
    exact characteristic_singleton_mem_JL B p
  have ht (b : B) : tailFunction hB b ∈ restrictionAlgebra hB := by
    change restrictToBase B (tailFunction hB b) ∈ JL B
    rw [restrict_tailFunction]
    exact characteristic_mem_JL b.property
  have hbase (p : Point) (y : AUCompactum B)
      (hpy : (↑(Sum.inl p : MrowkaBase B) : AUCompactum B) ≠ y) :
      ∃ f ∈ restrictionAlgebra hB, f (↑(Sum.inl p : MrowkaBase B)) ≠ f y := by
    exact ⟨singletonFunction hB p, hs p, by simp [hpy.symm]⟩
  have hsep (x y : AUCompactum B) (hxy : x ≠ y) :
      ∃ f ∈ restrictionAlgebra hB, f x ≠ f y := by
    induction x using OnePoint.rec with
    | infty =>
      induction y using OnePoint.rec with
      | infty => exact False.elim (hxy rfl)
      | coe y =>
        rcases y with p | b
        · obtain ⟨f, hf, hne⟩ := hbase p OnePoint.infty hxy.symm
          exact ⟨f, hf, hne.symm⟩
        · exact ⟨tailFunction hB b, ht b, by simp⟩
    | coe x =>
      rcases x with p | b
      · exact hbase p y hxy
      · induction y using OnePoint.rec with
        | infty => exact ⟨tailFunction hB b, ht b, by simp⟩
        | coe y =>
          rcases y with p | c
          · obtain ⟨f, hf, hne⟩ := hbase p _ hxy.symm
            exact ⟨f, hf, hne.symm⟩
          · have hcb : c ≠ b := fun h => hxy (by subst c; rfl)
            exact ⟨tailFunction hB b, ht b, by simp [hcb]⟩
  intro x y hxy
  obtain ⟨f, hf, hne⟩ := hsep x y hxy
  exact ⟨f, ⟨f, hf, rfl⟩, hne⟩

theorem restrictToBase_mem_JL {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (f : C(AUCompactum B, ℝ)) : restrictToBase B f ∈ JL B := by
  have hclosed : IsClosed (restrictionAlgebra hB : Set C(AUCompactum B, ℝ)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (restrictToBaseCLM B).continuous
  have hf := ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints
    (restrictionAlgebra hB) (restrictionAlgebra_separates hB) f
  change f ∈ closure (restrictionAlgebra hB : Set C(AUCompactum B, ℝ)) at hf
  rw [hclosed.closure_eq] at hf
  exact hf

/-- The Section 3.1 representation is an isometry onto the actual closed span.
The infinitude hypothesis is satisfied by the paper's continuum-sized families. -/
def jlContinuousEquiv {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    JL B ≃ₗᵢ[ℝ] C(AUCompactum B, ℝ) := by
  let e : C(AUCompactum B, ℝ) →ₗᵢ[ℝ] JL B :=
    { toLinearMap := (restrictToBase B).toLinearMap.codRestrict (JL B) (restrictToBase_mem_JL hB)
      norm_map' := restrictToBase_norm hB hInf }
  refine (LinearIsometryEquiv.ofSurjective e ?_).symm
  intro f
  obtain ⟨g, hg⟩ := jl_le_restriction_range hB hInf f.property
  exact ⟨g, Subtype.ext hg⟩

@[simp] theorem jlContinuousEquiv_symm_apply {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (hInf : B.Infinite) (f : C(AUCompactum B, ℝ)) :
    ((jlContinuousEquiv hB hInf).symm f).val = restrictToBase B f := rfl

theorem jlContinuousEquiv_restrict {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (hInf : B.Infinite) (f : C(AUCompactum B, ℝ)) (hf : restrictToBase B f ∈ JL B) :
    jlContinuousEquiv hB hInf ⟨restrictToBase B f, hf⟩ = f :=
  (jlContinuousEquiv hB hInf).apply_symm_apply f

end SigmaNonprimarity
