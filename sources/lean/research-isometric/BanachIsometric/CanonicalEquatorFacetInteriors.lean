import BanachIsometric.CanonicalEquatorAffine
import BanachIsometric.SimplexBoundarySphereHomeomorph
import BanachIsometric.SignedSimplexFaceGeometry

/-! The canonical radial equator facets have a unique interior preimage
where the boundary-simplex parameter has exactly one zero coordinate. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric SphereGenerator
open scoped Topology

def simplexFaceLift {n : ℕ} (i : Fin (n + 2)) (w : Simplex (n + 1)) (hw : w i = 0) : Simplex n :=
  ⟨fun j => w (i.succAbove j), fun j => stdSimplex.zero_le w (i.succAbove j), by
    have hs := stdSimplex.sum_eq_one w
    rw [Fin.sum_univ_succAbove _ i, hw, zero_add] at hs
    exact hs⟩

theorem face_simplexFaceLift {n : ℕ} (i : Fin (n + 2)) (w : Simplex (n + 1)) (hw : w i = 0) :
    face i (simplexFaceLift i w hw) = w := by
  apply Subtype.ext
  rw [signedFace_barycentric]
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · rw [Fin.insertNth_apply_same]
    exact hw.symm
  · rw [Fin.insertNth_apply_succAbove]
    rfl

theorem simplexFace_injective {n : ℕ} (i : Fin (n + 2)) : Function.Injective (face i) := by
  intro u w h
  apply Subtype.ext
  funext j
  have hcoord := congrArg (fun z : Simplex (n + 1) => z (i.succAbove j)) h
  change (face i u).val (i.succAbove j) = (face i w).val (i.succAbove j) at hcoord
  rw [signedFace_barycentric, signedFace_barycentric] at hcoord
  simpa only [Fin.insertNth_apply_succAbove] using hcoord

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def canonicalEquatorBoundaryPoint (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (z : EquatorSphere v) : SimplexBoundary n :=
  (simplexBoundarySphereHomeomorph n).symm (equatorStandardSphereHomeomorph v (n + 1) hdim z)

def canonicalEquatorOffSeam (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (z : EquatorSphere v) : Prop :=
  ∃! i, (canonicalEquatorBoundaryPoint v n hdim z).val i = 0

theorem canonicalEquatorFace_standard_coordinates (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) (u : Simplex (n + 1)) :
    equatorStandardSphereHomeomorph v (n + 1) hdim (canonicalEquatorFace v n hdim i u) =
      simplexBoundarySphereHomeomorph n (boundarySimplexFaceInclusion n i u) := by
  let e := equatorStandardSphereHomeomorph v (n + 1) hdim
  change e (e.symm (boundarySimplexSphereFace n i u)) = _
  rw [e.apply_symm_apply]
  have h := ContinuousMap.congr_fun (simplexBoundarySphereHomeomorph_face n i) u
  exact h.symm

theorem canonicalEquatorFace_eq_iff (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) (u : Simplex (n + 1)) (z : EquatorSphere v) :
    canonicalEquatorFace v n hdim i u = z ↔ face i u = (canonicalEquatorBoundaryPoint v n hdim z).val := by
  let e := equatorStandardSphereHomeomorph v (n + 1) hdim
  let B := simplexBoundarySphereHomeomorph n
  have hc : e (canonicalEquatorFace v n hdim i u) = B (boundarySimplexFaceInclusion n i u) :=
    canonicalEquatorFace_standard_coordinates v n hdim i u
  constructor
  · intro h
    have hp : B (boundarySimplexFaceInclusion n i u) = e z := hc.symm.trans (congrArg (fun x => e x) h)
    have hq := congrArg (fun x => B.symm x) hp
    change B.symm (B (boundarySimplexFaceInclusion n i u)) = B.symm (e z) at hq
    rw [B.symm_apply_apply] at hq
    exact congrArg Subtype.val hq
  · intro h
    have hp : boundarySimplexFaceInclusion n i u = canonicalEquatorBoundaryPoint v n hdim z := Subtype.ext h
    apply e.injective
    rw [hc, hp]
    exact B.apply_symm_apply (e z)

theorem exists_canonicalEquatorFace_interior_and_unique (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (z : EquatorSphere v) (hz : canonicalEquatorOffSeam v n hdim z) :
    ∃ a : Fin (n + 3) × Simplex (n + 1), canonicalEquatorFace v n hdim a.1 a.2 = z ∧
      (∀ j, 0 < a.2 j) ∧ ∀ b : Fin (n + 3) × Simplex (n + 1),
        canonicalEquatorFace v n hdim b.1 b.2 = z → b = a := by
  let p := canonicalEquatorBoundaryPoint v n hdim z
  obtain ⟨i, hi, hiUnique⟩ := hz
  let u := simplexFaceLift i p.val hi
  have hu : face i u = p.val := face_simplexFaceLift i p.val hi
  refine ⟨(i, u), (canonicalEquatorFace_eq_iff v n hdim i u z).mpr hu, ?_, ?_⟩
  · intro j
    change 0 < p.val (i.succAbove j)
    by_contra! h
    have hj := le_antisymm h (stdSimplex.zero_le p.val (i.succAbove j))
    exact Fin.succAbove_ne i j (hiUnique _ hj)
  · rintro ⟨k, w⟩ hw
    have hw' : face k w = p.val := (canonicalEquatorFace_eq_iff v n hdim k w z).mp hw
    have hk : p.val k = 0 := by rw [← hw', simplex_face_missing]
    have hki := hiUnique k hk
    subst k
    exact Prod.ext rfl (simplexFace_injective i (hw'.trans hu.symm))

theorem exists_canonicalEquatorFace_hit (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (z : EquatorSphere v) :
    ∃ (i : Fin (n + 3)) (u : Simplex (n + 1)), canonicalEquatorFace v n hdim i u = z := by
  let p := canonicalEquatorBoundaryPoint v n hdim z
  obtain ⟨i, hi⟩ := p.property
  exact ⟨i, simplexFaceLift i p.val hi,
    (canonicalEquatorFace_eq_iff v n hdim i _ z).mpr (face_simplexFaceLift i p.val hi)⟩

theorem canonicalEquatorOffSeam_of_positive_face (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (i : Fin (n + 3)) (u : Simplex (n + 1))
    (hu : ∀ j, 0 < u j) :
    canonicalEquatorOffSeam v n hdim (canonicalEquatorFace v n hdim i u) := by
  have h := (canonicalEquatorFace_eq_iff v n hdim i u (canonicalEquatorFace v n hdim i u)).mp rfl
  unfold canonicalEquatorOffSeam
  rw [← h]
  refine ⟨i, simplex_face_missing i u, ?_⟩
  intro j
  refine Fin.succAboveCases i (fun _ => rfl) (fun k hk => ?_) j
  change (face i u).val (i.succAbove k) = 0 at hk
  rw [signedFace_barycentric, Fin.insertNth_apply_succAbove] at hk
  exact ((hu k).ne' hk).elim

end BanachIsometric.SingularPrism
