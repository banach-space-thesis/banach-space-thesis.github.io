import Sigma.FunctionalCharge
import ThesisCommon.Analysis.UltrafilterBoolean

/-! The atomic charge agrees with the actual functional on the whole generated
Boolean algebra, not just on its displayed generators. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity

attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace

theorem atomCharge_is_ultrafilter {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (Uinf : Ultrafilter Point) (p : AUCompactum B) :
    ∃ U : Ultrafilter Point, atomCharge hB Uinf p = ultrafilterCharge U := by
  induction p using OnePoint.rec with
  | infty => exact ⟨Uinf,rfl⟩
  | coe q => cases q with
    | inl n => exact ⟨pure n,rfl⟩
    | inr b => exact ⟨freeUltrafilterOn b.val (hB.1 b.val b.property),rfl⟩

theorem atomCharge_union {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (Uinf : Ultrafilter Point) (p : AUCompactum B) (A D : Set Point) :
    atomCharge hB Uinf p (A ∪ D) = max (atomCharge hB Uinf p A) (atomCharge hB Uinf p D) := by
  obtain ⟨U,hU⟩ := atomCharge_is_ultrafilter hB Uinf p
  rw [hU]
  exact ultrafilterCharge_union U A D

theorem atomCharge_compl {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (Uinf : Ultrafilter Point) (p : AUCompactum B) (A : Set Point) :
    atomCharge hB Uinf p Aᶜ = 1 - atomCharge hB Uinf p A := by
  obtain ⟨U,hU⟩ := atomCharge_is_ultrafilter hB Uinf p
  rw [hU]
  exact ultrafilterCharge_compl U A

def AtomLiftable {B : Set (Set Point)} (hB : AlmostDisjoint B) (Uinf : Ultrafilter Point)
    (A : Set Point) : Prop := ∃ f : C(AUCompactum B, ℝ), ∀ p, atomCharge hB Uinf p A = f p

theorem atomLiftable_empty {B : Set (Set Point)} (hB : AlmostDisjoint B) (Uinf : Ultrafilter Point) :
    AtomLiftable hB Uinf ∅ := ⟨0,fun p => (atomCharge hB Uinf p).map_empty⟩

theorem atomLiftable_union {B : Set (Set Point)} (hB : AlmostDisjoint B) (Uinf : Ultrafilter Point)
    {A D : Set Point} (hA : AtomLiftable hB Uinf A) (hD : AtomLiftable hB Uinf D) :
    AtomLiftable hB Uinf (A ∪ D) := by
  obtain ⟨f,hf⟩ := hA
  obtain ⟨g,hg⟩ := hD
  exact ⟨f ⊔ g, fun p => by rw [atomCharge_union,hf,hg]; rfl⟩

theorem atomLiftable_compl {B : Set (Set Point)} (hB : AlmostDisjoint B) (Uinf : Ultrafilter Point)
    {A : Set Point} (hA : AtomLiftable hB Uinf A) : AtomLiftable hB Uinf Aᶜ := by
  obtain ⟨f,hf⟩ := hA
  exact ⟨1-f,fun p => by rw [atomCharge_compl,hf]; rfl⟩

theorem atomLiftable_finite {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (Uinf : Ultrafilter Point) (hUinf : (Uinf : Filter Point) ≤ Filter.cofinite)
    {A : Set Point} (hA : A.Finite) : AtomLiftable hB Uinf A := by
  classical
  have hfin (F : Finset Point) : AtomLiftable hB Uinf (↑F : Set Point) := by
    induction F using Finset.induction_on with
    | empty => simpa only [Finset.coe_empty] using atomLiftable_empty hB Uinf
    | @insert n F hn ih =>
      have hs : AtomLiftable hB Uinf {n} := ⟨singletonFunction hB n, atomCharge_singleton hB Uinf hUinf n⟩
      simpa only [Finset.coe_insert, Set.singleton_union] using atomLiftable_union hB Uinf hs ih
  simpa only [hA.coe_toFinset] using hfin hA.toFinset

theorem atomLiftable_generated {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (Uinf : Ultrafilter Point) (hUinf : (Uinf : Filter Point) ≤ Filter.cofinite)
    (havoid : ∀ b ∈ B, b ∉ Uinf) {A : Set Point} (hA : A ∈ generatedAlgebra B) :
    AtomLiftable hB Uinf A := by
  induction hA using BooleanSubalgebra.closure_bot_sup_induction with
  | mem A hA =>
    rcases hA with hA | hA
    · exact ⟨tailFunction hB ⟨A,hA⟩, atomCharge_family_set hB Uinf havoid ⟨A,hA⟩⟩
    · exact atomLiftable_finite hB Uinf hUinf hA
  | bot => exact atomLiftable_empty hB Uinf
  | sup A hA D hD ihA ihD => exact atomLiftable_union hB Uinf ihA ihD
  | compl A hA ih => exact atomLiftable_compl hB Uinf ih

theorem atomLift_restrict {B : Set (Set Point)} (hB : AlmostDisjoint B) (Uinf : Ultrafilter Point)
    {A : Set Point} {f : C(AUCompactum B, ℝ)} (hf : ∀ p, atomCharge hB Uinf p A = f p) :
    restrictToBase B f = characteristic A := by
  ext n
  have h := hf (↑(Sum.inl n : MrowkaBase B))
  simpa only [atomCharge_base, diracCharge_apply, restrictToBase_apply, characteristic_apply] using h.symm

theorem functionalCharge_generated {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (Uinf : Ultrafilter Point) (hUinf : (Uinf : Filter Point) ≤ Filter.cofinite)
    (havoid : ∀ b ∈ B, b ∉ Uinf) (φ : JL B →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    {A : Set Point} (hA : A ∈ generatedAlgebra B) :
    ∃ hmem : characteristic A ∈ JL B,
      functionalCharge hB hInf Uinf φ hφ A = φ ⟨characteristic A,hmem⟩ := by
  obtain ⟨f,hf⟩ := atomLiftable_generated hB Uinf hUinf havoid hA
  have hrestrict := atomLift_restrict hB Uinf hf
  have hmem : characteristic A ∈ JL B := hrestrict ▸ restrictToBase_mem_JL hB f
  exact ⟨hmem, functionalCharge_eq_of_lift hB hInf Uinf φ hφ A hmem f hrestrict hf⟩

end SigmaNonprimarity
