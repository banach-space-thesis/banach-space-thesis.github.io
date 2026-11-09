# Statement correspondence and proof obligations

**Theorem A, Corollary B and Theorems C–E have unconditional Lean proofs.**
The main import is `BanachIsometric.MainResults`. This file compares the
production declarations with the manuscript and records the earlier staged
review of individual components.

Source: Acuaviva–Kania, arXiv:2608.18257v1, downloaded as
`source/main-isometric.tex`. The arXiv page showed v1 when checked on
28 October 2026. Compilation and axiom records are separate from this semantic
review. A detailed review is in `second-stage-statement-review.md`.

## Homological clutching integration, 9 November 2026

The alternative proof uses the rational singular image of the original
clutching map, in the identity component of the original operator body group.
`bodyIdentityComponent_rawDegreeHomologyBounded` and the spherical diagonal
identity in `SphericalGraphHomology` identify the clutching image as a positive
even primitive in bounded rational homology. The actual Pontryagin coproduct
then gives its vanishing. The Lipschitz comparison lifts the sphere cycle to
the original bundle and fills the difference of its projected representative
and the canonical cycle. The operator moment polynomial uses one extension
per simplex, shared across all evaluation vectors. The canonical coned cycle
has signed count one almost everywhere in the original gauge interior.
`ExactSectionHomologicalRigidity` combines these facts and recovers the
ambient quadratic form. It uses the original geometric hypotheses and
bypasses the finite-order pullback through rational singular homology.

The proved `complexTheoremA` and `Quaternionic.theoremA` use the target
definitions reviewed below. `complexCorollaryB` and `Quaternionic.corollaryB`
take bijective metric isometries of the actual subspaces via the original
`MetricSubspaceHomogeneity` predicates. The isometries may move zero.
The complex and quaternionic C declarations use the actual quotient norms.
Their tail declarations include dense range of every canonical completed
bonding map. The D declarations quantify one scalar-linear map for each pair
of subspaces and an individual positive factor for each family member.
They keep the manuscript's zero alternative. The E declarations use the
original distance and preserve the original scalar action. The real circled
star alternative is restricted to odd section dimension, while the convex
alternative covers both parities.

`MainResultsAudit.lean` prints the final declaration types and checks their
axioms from the production aggregate. The 9 November 2026
[audit log](main-results-audit.log) records 6,551 checked project declarations
and only `propext`, `Classical.choice`, and `Quot.sound`. Warnings were
treated as errors. The [certificate](main-results-certificate.json) records
the manuscript hash, toolchain pins, and the source and object hashes of
the audited project module closure.

The comparison below uses the statements in `source/main-isometric.tex`,
lines 108–181. All global dimension conditions use cardinal rank, so they
include infinite-dimensional spaces.

| Manuscript | Lean declarations and interpretation |
| --- | --- |
| A, complex and quaternionic | `complexTheoremA` and `Quaternionic.theoremA` use the original function on the original algebraic scalar module. Every scalar `(n+1)`-subspace has an auxiliary Euclidean sphere on which that function is Lipschitz. The `n`-subspace equivalences are real-linear. The positive Hermitian form has diagonal exactly `p x ^ 2`. |
| B, complex and quaternionic | `complexCorollaryB` and `Quaternionic.corollaryB` quantify over `Nonempty (E ≃ᵢ F)`. The norm and original scalar actions are retained in the Hermitian conclusion, in the actual norm completion, and on the original space when complete. |
| C, complex and quaternionic | `complexTheoremC` and `Quaternionic.theoremC` give both directions. The tail declarations apply to each reduced defining sequence. The norm of the class of `x` is exactly `p k x`. The completed bonding maps extend the quotient maps induced by the same representative and have dense range. The limit uses the original complete Hausdorff uniformity. |
| D, real, complex and quaternionic | `realTheoremD`, `complexTheoremD` and `Quaternionic.theoremD` choose one scalar-linear equivalence for each pair of subspaces before quantifying over all seminorms and their positive factors. The zero alternative is explicit. A nonzero family member supplies the common Hermitian norm, and the model declarations preserve the scalar action, generated topology and completeness. |
| E, real, complex and quaternionic | `MetricGeometry.realTheoremE`, `complexTheoremE` and `Quaternionic.theoremE` use the original distance and scalar-linear isometries, with the manuscript's two cofinal ball hypotheses. The radial alternative refers to the actual closed-ball sections. Only the real radial alternative requires odd `n`. The all-convex declarations express the original distance by the same complete Hermitian norm and a nondecreasing subadditive profile with the stated zero and positivity properties. |

Quaternionic right multiplication is the action of the opposite quaternion
algebra. Complex multiplication uses the equivalent left action. The
radial-star condition omits the zero-dimensional section, whose sole point is
automatic. For the metric results, translation invariance identifies the
original metric uniformity with the canonical additive uniformity used for
completeness.

The sections below record the earlier staged statement review. Their
historical proof statuses, including the final table, are superseded by the
checkpoint above and by `../RESUME.md`.

## Main targets: the specified function, norm, and scalar action

`ComplexFunctionalStatement` in `Functional.lean` expresses complex Theorem A.
Its ambient space has only an additive group and the original complex module
structure. It assumes nonnegativity, definiteness, and absolute homogeneity of
`p`; no triangle inequality, convexity, topology, norm, or completeness is
assumed. Its section maps are real-linear bijections preserving that same `p`.
`ComplexSphereLipschitz` allows arbitrary real Euclidean coordinates on every
complex `(n+1)`-dimensional subspace. The real dimension of the coordinate
space is `2*(n+1)`. `FunctionalStarBody` proves that these original hypotheses
actually give compact local bodies, a positive inner radius, regular-closedness,
and global Lipschitz regularity in complex-linear coordinates.

`PositiveHermitianForm` is Hermitian and linear in the second argument.
`HasHermitianSquare p` requires its diagonal to equal `(p x)^2` exactly,
including zero imaginary part. The ordinary complex left-module convention is
equivalent to the paper's right-module convention because the scalars commute.

`MetricSubspaceHomogeneity ℂ X n` quantifies over complex subspaces of scalar
cardinal rank `n`; `IsometryEquiv` means a bijective metric isometry without
assuming linearity or fixing zero. `ComplexCorollaryBAt` concludes
`HasInnerProductForGivenScalarAction ℂ X`, explicitly equating the witness's
`NormedSpace` structure with the original one. This fixes the original norm
and action. The weaker-looking intermediate bundled inner-product predicate
is proved equivalent by extracting the scalar-independent parallelogram law
and reconstructing with the original action. The completion reduction also
retains that original extended action.

The quaternionic counterparts in `QuaternionicStatements.lean` use modules
over the opposite quaternion algebra, so `rightMul x a = op a • x` has the
paper's exact right action. Right Hermitian forms are right-linear in their
second argument and conjugate-linear in their first. `NormSMulClass` expresses
the given norm's compatibility with the given right action; quaternions are
not treated as a commutative normed field. Real analytic structures in
`QuaternionicNormReduction` are obtained by restriction of that action.

`Module.rank` as a cardinal retains the infinite-dimensional ambient cases.
`finrank` is used after finiteness is established. Neither normed target adds
completeness. Mazur–Ulam supplies the required real-linear isometries, and norm
regularity is automatic, over both scalar fields.

`ComplexFunctionalStatement`, `Quaternionic.FunctionalStatement`,
`ComplexCorollaryBAt`, `Quaternionic.NormedCorollaryBAt`, and
`ComplexCodimensionOne` are **target proposition definitions**. The reductions
from A to B or from codimension one retain their unproved input as an explicit
argument. No unconditional theorem inhabiting these main targets exists yet.

## Lemma 2.1: actual covariance, moments, and local lifting

The normalized measure is `(μ S)⁻¹ • μ.restrict S`. Its integration formula
agrees with the paper's normalized set integral. The actual Haar transformation
law cancels the determinant factor; arbitrary linear maps are not assumed
measure preserving. `Covariance` takes covariance about the prescribed origin,
without subtracting a barycentre, and proves positivity, exact operator
transport `C(eS)=e C(S) e*`, and existence of covariance position. In that
position every real-linear body automorphism is proved orthogonal.
`OrthogonalStabilizer` proves the corresponding closed orthogonal body
stabiliser is a compact subgroup. These supply the substantive components of
Lemma 2.1(i); some coordinate-independent packaging remains separate.

`TensorMoments` defines actual moments by integrals of coordinate products.
Full ordered tensor arrays replace a bundled symmetric tensor space. Their
pure-tensor formula, matrix representation, and transport law are proved, so
the coordinate action really is the usual tensor-power action. Positive-degree
indices are `ℕ+`; odd degrees have not been discarded.

`MomentSeparation` proves polynomial moment determination using
Stone–Weierstrass and measure extensionality. Probability supplies degree zero.
For compact regular-closed bodies of positive volume, equality of the
normalized measures recovers the bodies exactly through their supports,
including boundaries. The required regular-closedness is independently proved
for the star bodies arising from the functional hypotheses.

`FiniteEquations` applies Noetherianity to the polynomial matrix equations.
`BodyMomentStabilizer` combines this with actual moment transport and separation
to prove that finitely many positive moment degrees detect every real-linear
body automorphism. This proves the finite-tuple assertion of Lemma 2.1(ii),
even before restricting to orthogonal maps. No moment-determination or
transformation conclusion is hidden as a hypothesis of this final result.

The orbit step follows an explicit alternative to the paper's quotient
manifold route. `TensorRepresentation`, `TensorGroupAction`, and
`InfinitesimalStabilizer` construct the smooth representation and integrate its
actual derivative kernel to stabilisers. `ExponentialLocal` and
`SkewFactorization` construct local skew factors for nearby actual unitaries.
`GenericUnitaryOrbit` constructs a complement to the derivative kernel and
combines the inverse function theorem with compact orbit representatives.
`TensorOrbitSection` instantiates it for the actual finite body-moment tuple.

Its endpoint `exists_lipschitz_bodyMoment_image_section` provides a finite tuple,
an ambient tuple neighbourhood, and a locally Lipschitz map into the orthogonal
group, equal to the identity at the reference tuple. Whenever a body is an
orthogonal image of the reference body and its actual moment tuple lies in
that neighbourhood, the chosen orthogonal map carries the reference body
exactly onto it. This proves the **local lifting consequence** needed later in
Proposition 4.2. It does not prove or assert that `O(E)/G` is diffeomorphic to a
compact embedded orbit manifold, the literal full assertion of Lemma 2.1(iii).

## Regularity and polynomial rigidity

`MomentRegularity` proves quantitative normalized-integral bounds from radial
sup-distance, including volumes, covariance, and every tensor degree. Common
positive inner and finite outer radii are explicit. Euclidean-input statements
use the actual norm-two Euclidean spheres. Ordinary coordinate/tensor arrays
may have a sup norm; orthogonal matrices are not asserted to preserve that norm.

`CovarianceNormalization` applies these bounds and the local square-map inverse
to actual radial families. Its strongest endpoint derives a locally Lipschitz
family of genuine real continuous linear equivalences putting every nearby
body in covariance position, without assuming reference normalization or a
covariance-regularity theorem. It retains the given auxiliary real inner
product. Applying these pieces to the paper's section field is still an
assembly obligation.

`LocalIsometricFrames` supplies another concrete local ingredient: for actual
equal-dimensional real subspaces with Lipschitz canonical orthogonal
projections, it constructs operator-norm locally Lipschitz isometric frames
whose ranges equal those subspaces. Reference frames are constructed from
orthonormal bases; no frame or projection identities are assumed in this final
subspace-family endpoint. The regularity of the paper's specific scalar
hyperplane projection field remains to be established.

`SectionRadialRegularity` derives the radial and moment hypotheses for actual
pulled-back sections of the original gauge. The radial function is precisely
`1 / p(J θ)`; isometric frames and the original sphere bounds yield common
positive inner and finite outer radii, compactness, and uniform Lipschitz
dependence on the parameter. Its final chart theorem composes the actual
projection-frame constructor with local covariance normalization. Thus no
moment regularity or arbitrary frame choice is a premise of this section
endpoint. The actual subspace field still has to satisfy the explicit
Lipschitz-projection hypothesis.

`NormalizedRadialLift` transports genuine Euclidean bodies and Haar measures
through the explicit coordinate equivalence and identifies the actual moment
tuple with an average of the Euclidean polynomial integrand. For an already
covariance-normalized radial family with common radii, radial parameter
regularity, and actual body equivalences, it constructs locally Lipschitz exact
Euclidean equivalences, equal to the identity at the reference body.
`NormalizedBodyLift` gives the same exact lifting conclusion for compact
normalized bodies with locally Lipschitz actual finite moment tuples.
The latter moment-regularity premise is explicit. Applying it after varying
covariance normalization is supported by `NormalizedImageMoments`: its exact
tensor transport law and smooth joint tensor action derive local regularity
of the actual image-body moments from original moment regularity and operator
regularity. The original radial function is not assumed to survive the
coordinate change. `LocalInverseFamily` proves local operator Lipschitz bounds
for inverses and compositions, deriving the needed norm bounds on a smaller
neighbourhood. These support the final chart-map composition rather than
postulating regularity of the inverse normalizers.

`NormalizedImageLift` composes this actual image-moment regularity with the
normalized-body lift. Its radial endpoint requires only the original compact
radial family's common bounds and parameter regularity, actual locally
Lipschitz normalizers putting the image bodies in covariance position, and
actual equivalences of the original bodies. It derives the tuple regularity
and returns exact locally Lipschitz equivalences between the normalized image
bodies. No transformed-radius or transformed-moment regularity premise is
left in that radial endpoint. `OriginalBodyLift` proves the exact
inverse-normalization map `e(a)⁻¹ q(a) e(a₀)`, including the identity at the base
point and local operator Lipschitz regularity. `RadialFamilyLift` constructs
the normalizers, restricts to the appropriate chart, and derives exact local
equivalences of the original bodies from only the original compact radial
family, common positive/finite radii, uniform radial parameter regularity,
reference regular-closedness, and real-linear equivalence. No covariance,
normalizer, moment-regularity, or orbit-section premise remains in that final
endpoint. The moving-frame section-field composition and global
principal-bundle packaging still need assembly for Proposition 4.2.

`StarBodyBoundary` proves actual Haar-nullity of star-body boundaries and their
homothetic copies by homothetic squeezing. It also proves nullity of boundary
images contained in a fixed positive gauge level. No convexity or symmetry is
introduced.

`LipschitzNullImages` proves the actual Lusin (N) property in equal finite real
dimensions: a map Lipschitz on a null set sends it to a Haar-null image,
without measurability assumptions on either set. It uses Hausdorff measure and
mutual absolute continuity of Haar measures. This is another analytic input to
the signed formula, not the formula itself.

`PolynomialIntegration` proves exact coefficientwise integration of polynomial
families. For fixed homogeneous degree and finitely many variables it derives
a common finite support automatically; integrability of the coefficients is
still required. This is a proved integration step, **not the signed area–degree
identity**.

`JacobianPolynomial` constructs the coordinate polynomial whose columns are
linear in the section vector and multiplies its determinant by the squared-
length weight. Its degree is exactly the homogeneous degree `N+2*k` (allowing
the zero polynomial), and evaluation is the exact numerical determinant/weight
expression. Its integral endpoint keeps coefficient integrability explicit.
The input matrices for the column coefficients have not yet been shown to come
from the required almost-everywhere derivative, nor are the needed analytic
bounds or the signed degree identity inferred from this algebraic construction.

`PolynomialRigidity` extracts the polynomial square from two consecutive even
polynomial powers, proves degree-two homogeneity from positive scaling, and
retains positivity. `PolynomialQuadratic` constructs an actual positive-definite
`QuadraticForm` with exactly those values. The two polynomial powers remain
explicit inputs. Theorem 3.1's implication from an exact family to those powers
is not yet proved.

## Scalar reconstruction and arbitrary ambient dimension

`ComplexPolarization` and `QuaternionicPolarization` prove exact Hermitian
polarisation and uniqueness on the original scalar modules. The quaternionic
existence theorem constructs the right Hermitian form from a positive symmetric
real bilinear form whose diagonal scales by quaternionic norm-squared.
`HermitianGluing` and `QuaternionicGluing` identify local forms by their diagonal
and glue them on fixed-dimensional subspaces containing any three vectors.
They introduce no ambient norm or topology. Their local geometric existence
premise is explicit and remains to be proved from section equivalence.

`HyperplanePairCoverage` proves that two vectors in the relevant finite scalar
dimension at least three lie in the kernel of a nonzero scalar functional,
whose quotient has dimension one. The algebraic argument works over any
division ring, including the opposite quaternion algebra. Over the real or
complex field it also constructs an actual unit normal for the given inner
product. It does not yet construct quaternionic Hermitian normal coordinates
or a smooth field of scalar hyperplane projections.

`CoordinateOrthogonality` explicitly transports genuine Euclidean vectors and
bodies to ordinary finite coordinate spaces with their sup norm. An actual
Euclidean isometry gives an orthogonal matrix with exactly the transported
action. Two linearly equivalent bodies in the same covariance position are
therefore orthogonal images in these coordinates. This supplies the missing
coordinate identification without installing an inner product on the sup-norm
target.

`ComplexScalarPolarization` proves existence and uniqueness of a positive
complex Hermitian form with diagonal `q` from an actual positive-definite real
`QuadraticForm` invariant under multiplication by `I`. It works on the original
algebraic complex module with its compatible real action and introduces no
norm or topology. Invariance under `I` alone suffices, so the paper's full
absolute homogeneity supplies more than this reconstruction needs.

## Theorem C prerequisites and Theorem D's eigenvalue core

`CofinalQuotientDimension` proves that decreasing kernels with intersection zero
give quotient dimensions eventually exceeding every finite threshold below the
ambient cardinal rank. The ambient dimension may be infinite.

`SeminormInverseLimit` constructs normed models of the actual quotients
`X/ker p`, algebraically equivalent to those quotients, with exact class norm
`p x`. For `p ≤ q`, the canonical identity on representatives gives a
surjective contraction of normed quotients. Its completion extension is a
contraction with dense range; surjectivity of the completed map is not assumed.
Reflexivity, composition, and canonical projection identities are proved.

For an increasing defining sequence on a complete Hausdorff complex module,
`WithSeminorms` identifies the pulled-back product uniformity with the original
uniformity. Completeness gives closed image and finite-coordinate approximation
gives density in compatible tuples. The resulting continuous linear equivalence
is the canonical one, as its coordinate formula proves. `SeminormTail` proves
that deleting any finite initial segment preserves the original defining
uniformity and gives the corresponding canonical tail equivalence.

These results do not assert normability or Hilbertianity of the quotients.
Theorem C still needs the substantive Corollary B input for eventual
Hilbertianity, the full equivalence, and the quaternionic analytic version.

`DeletionRigidity` proves that a finite family of at least three positive
numbers is constant if all its one-index-deletion multisets are positively
proportional. Multiplicities are retained. A common-maximum and deletion-sum
argument replaces the paper's ordered geometric-progression argument. This is
the genuine elementary eigenvalue core of Theorem D, not its spectral reduction
or global proportionality conclusion.

`KernelRigidity` proves the independent kernel-dimension argument over any
division ring, including arbitrary ambient cardinal dimension: for
`1 ≤ n < rank X`, a submodule with the same intersection dimension with every
`n`-dimensional subspace is zero or total. The proof restricts to an actual
`(n+1)`-dimensional subspace and constructs two hyperplanes using scalar
functionals; the Grassmann dimension identity gives the contradiction. The
uniform intersection-dimension hypothesis is explicit. Its derivation from
the paper's positive similarities is discharged in `SimilarityKernel`:
an actual `p`-similarity `T : E ≃ₗ[K] F` with positive factor restricts to an
actual linear equivalence `(E ∩ ker p) ≃ₗ[K] (F ∩ ker p)`. All fixed-dimensional
section similarities therefore force `ker p` to be zero or total, and `p` to
be definite or identically zero. This final similarity endpoint has no
uniform-dimension premise. It assumes only that the zero set is the specified
scalar submodule, as it is for a seminorm; no norm, homogeneity, or
Hilbertianity is assumed for this kernel argument.

## Remaining obligations

| Paper result | Precise current status |
| --- | --- |
| Lemma 2.1(i) | Covariance position, orthogonality, and compact orthogonal body stabilisers proved; final packaging separate. |
| Lemma 2.1(ii) | Finite tuple of actual positive-order moments detects body automorphisms. |
| Lemma 2.1(iii) | Required local Lipschitz lift proved directly; quotient diffeomorphism and compact embedded-manifold statement unproved. |
| Theorem 3.1 | Null-boundary, polynomial-integration and quadratic-extraction components proved; signed area–degree and exact-family polynomiality implication unproved. |
| Proposition 4.2 | Many concrete local ingredients proved; exact-section bundle and its full local assembly unproved. |
| Lemma 4.3 | Compact Lie-group homotopy finiteness, finite-order annihilation, and nonzero-degree pullback unproved. |
| Lemma 4.4, Proposition 4.5 | Required Lipschitz trivialisation and global exact-family construction unproved. |
| Theorem 4.1, Theorem 1.1 | Equivalent-section real ellipsoid and complex/quaternionic geometric rigidity unproved. |
| Theorem A, Corollary B | Both fields have faithful targets and conditional reductions; no unconditional proof. |
| Theorem C | Complex dimension, quotient/completion, canonical inverse-limit and tail prerequisites proved; eventual Hilbertianity and full theorem incomplete. |
| Theorem D | Deletion-multiset eigenvalue rigidity and the actual-similarity zero-or-definite kernel argument proved; Hilbertianity of nonzero seminorms, spectral reduction, and global proportionality incomplete. |
| Theorem E | Compatible-metric theorem unproved. |

No bundle annihilation or signed area–degree theorem should be inferred merely
from general Mathlib bundle, homotopy, differentiability, or integration APIs.
The current proof terms and this document deliberately retain these obligations.
