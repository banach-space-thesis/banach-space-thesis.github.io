import PosetsCommon.Algebra
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Closed nontrivial operator ideals of a complemented subspace inject into
those of the ambient space. The lifted ideal tests all bounded compressions. -/

noncomputable section
open Set ThesisCommon
namespace Posets
variable {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def compressionIdeal (I : ClosedIdeal 𝕜 (F →L[𝕜] F)) : ClosedIdeal 𝕜 (E →L[𝕜] E) := by
  refine ⟨{T | ∀ A : F →L[𝕜] E, ∀ B : E →L[𝕜] F, B.comp (T.comp A) ∈ I.val}, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hc : IsClosed (⋂ A : F →L[𝕜] E, ⋂ B : E →L[𝕜] F,
        (fun T : E →L[𝕜] E => B.comp (T.comp A)) ⁻¹' I.val) :=
      isClosed_iInter (fun A => isClosed_iInter (fun B =>
        I.property.1.preimage
          (((ContinuousLinearMap.compL 𝕜 F E F) B).continuous.comp
            (((ContinuousLinearMap.compL 𝕜 F E E).flip A).continuous))))
    convert hc using 1
    ext T
    simp only [mem_setOf_eq, mem_iInter, mem_preimage]
  · intro A B
    simpa using I.property.2.1
  · intro S hS T hT A B
    simpa only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add] using
      I.property.2.2.1 _ (hS A B) _ (hT A B)
  · intro c T hT A B
    simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul] using
      I.property.2.2.2.1 c _ (hT A B)
  · intro S T hT
    constructor
    · intro A B
      simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hT A (B.comp S)
    · intro A B
      simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hT (S.comp A) B

theorem compression_lift_eq (i : F →L[𝕜] E) (p : E →L[𝕜] F)
    (hp : p.comp i = ContinuousLinearMap.id 𝕜 F) (T : F →L[𝕜] F) :
    p.comp ((i.comp (T.comp p)).comp i) = T := by
  have hpi : ∀ y, p (i y) = y := fun y => congrArg (fun f : F →L[𝕜] F => f y) hp
  ext y
  change p (i (T (p (i y)))) = T y
  rw [hpi, hpi]

theorem compressionIdeal_mem_lift_iff (i : F →L[𝕜] E) (p : E →L[𝕜] F)
    (hp : p.comp i = ContinuousLinearMap.id 𝕜 F)
    (I : ClosedIdeal 𝕜 (F →L[𝕜] F)) (T : F →L[𝕜] F) :
    i.comp (T.comp p) ∈ (compressionIdeal (E := E) I).val ↔ T ∈ I.val := by
  constructor
  · intro h
    simpa only [compression_lift_eq i p hp T] using h i p
  · intro hT A B
    have hleft := (I.property.2.2.2.2 (B.comp i) T hT).1
    have hboth := (I.property.2.2.2.2 (p.comp A) ((B.comp i) * T) hleft).2
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hboth

theorem compressionIdeal_ne_zero (i : F →L[𝕜] E) (p : E →L[𝕜] F)
    (hp : p.comp i = ContinuousLinearMap.id 𝕜 F)
    (I : ClosedIdeal 𝕜 (F →L[𝕜] F)) (hI : I.val ≠ {0}) :
    (compressionIdeal (E := E) I).val ≠ {0} := by
  intro he
  apply hI
  apply Subset.antisymm
  · intro T hT
    have hlift := (compressionIdeal_mem_lift_iff i p hp I T).mpr hT
    rw [he] at hlift
    have hz : i.comp (T.comp p) = 0 := hlift
    have hcomp := compression_lift_eq i p hp T
    rw [hz] at hcomp
    simpa using hcomp.symm
  · rintro T rfl
    exact I.property.2.1

theorem compressionIdeal_ne_univ (i : F →L[𝕜] E) (p : E →L[𝕜] F)
    (hp : p.comp i = ContinuousLinearMap.id 𝕜 F)
    (I : ClosedIdeal 𝕜 (F →L[𝕜] F)) (hI : I.val ≠ univ) :
    (compressionIdeal (E := E) I).val ≠ univ := by
  intro he
  apply hI
  apply Set.eq_univ_of_forall
  intro T
  apply (compressionIdeal_mem_lift_iff i p hp I T).mp
  rw [he]
  exact mem_univ _

def nontrivialIdealEmbeddingOfRetraction (i : F →L[𝕜] E) (p : E →L[𝕜] F)
    (hp : p.comp i = ContinuousLinearMap.id 𝕜 F) :
    NontrivialClosedIdeals 𝕜 (F →L[𝕜] F) ↪ NontrivialClosedIdeals 𝕜 (E →L[𝕜] E) where
  toFun I := ⟨(compressionIdeal (E := E) ⟨I.val, I.property.1⟩).val,
    (compressionIdeal (E := E) ⟨I.val, I.property.1⟩).property,
    compressionIdeal_ne_zero i p hp _ I.property.2.1,
    compressionIdeal_ne_univ i p hp _ I.property.2.2⟩
  inj' := by
    intro I J he
    apply Subtype.ext
    ext T
    have hv := congrArg Subtype.val he
    have hi := compressionIdeal_mem_lift_iff i p hp ⟨I.val, I.property.1⟩ T
    have hj := compressionIdeal_mem_lift_iff i p hp ⟨J.val, J.property.1⟩ T
    exact hi.symm.trans ((Set.ext_iff.mp hv _).trans hj)

end Posets
