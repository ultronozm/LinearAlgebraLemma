# Proof of a linear algebra lemma, with links to the corresponding Lean 4 code

Paul D. Nelson

18 January 2024

We formalize in Lean 4 a proof of
<a href="#ref-2020arXiv201202187N" class="citation"
data-cites="2020arXiv201202187N">(Nelson 2023, Theorem 1.8)</a>:

**Theorem 1**. *(`MainConcrete'` in [MainConcrete](MainConcrete.lean))*

*Let <span class="math inline">\\M\_{n}\\</span> denote the space of
complex <span class="math inline">\\n \times n\\</span> matrices,
included in the space <span class="math inline">\\M\_{n+1}\\</span> of
<span class="math inline">\\(n+1) \times (n+1)\\</span> matrices as the
upper-left block, e.g., for <span class="math inline">\\n = 2\\</span>,
as <span class="math display">\\\begin{pmatrix} \ast & \ast & 0 \\ \ast
& \ast & 0 \\ 0 & 0 & 0 \end{pmatrix}.\\</span> Let
<span class="math inline">\\\tau\\</span> be an element of
<span class="math inline">\\M\_{n+1}\\</span> with the property that no
eigenvalue of <span class="math inline">\\\tau\\</span> is also an
eigenvalue of the upper-left <span class="math inline">\\n \times
n\\</span> submatrix <span class="math inline">\\\tau\_0\\</span> of
<span class="math inline">\\\tau\\</span>. Let
<span class="math inline">\\x \in M\_{n+1}\\</span> with
<span class="math inline">\\\[x,\tau\] = 0\\</span>, where
<span class="math inline">\\\[a,b\] := a b -b a\\</span>. Let
<span class="math inline">\\z\\</span> denote the image in
<span class="math inline">\\M\_{n+1}\\</span> of the identity element of
<span class="math inline">\\M\_n\\</span>, thus
<span class="math inline">\\z =
\mathop{\mathrm{diag}}(1,\dotsc,1,0)\\</span> with
<span class="math inline">\\n\\</span> ones. Suppose that
<span class="math display">\\\[x,\[z,\tau\]\] = \[y, \tau\]\\</span> for
some <span class="math inline">\\y \in M\_n\\</span>. Then
<span class="math inline">\\x\\</span> is a scalar matrix.*

Here is the corresponding statement in Lean:

    import Mathlib

    abbrev Mat (R : Type) [Ring R] (n : ℕ) := Matrix (Fin n) (Fin n) R

    def matrixIncl {R : Type} [Ring R] {n : ℕ}
      (x : Mat R n) : Mat R (n+1) := 
      fun i j ↦ if h : i  ≠ Fin.last n ∧ j ≠ Fin.last n
        then x ⟨i, Fin.val_lt_last h.1⟩ ⟨j, Fin.val_lt_last h.2⟩
        else 0

    example (n : ℕ)
      (τ : Mat ℂ (n+1)) (hτ : τ.charpoly.roots ⊓ (Matrix.subUpLeft τ).charpoly.roots = ⊥)
      (x : Mat ℂ (n+1)) (hx : ⁅x, τ⁆ = 0) (y : Mat ℂ n)
      (h : ⁅x, ⁅matrixIncl (1 : Mat ℂ n), τ⁆⁆ = ⁅matrixIncl y, τ⁆)
      : ∃ (r : ℂ), x = r • (1 : Mat ℂ (n+1)) := by sorry

This result is perhaps of little intrinsic interest – it is the “linear
algebra lemma” required at the end of a longer analytic argument – but I
was nevertheless motivated to formalize it as an educational project. In
this note, we record a proof and indicate which parts correspond to
which Lean files and theorems (it would presumably be better to use
[blueprint](https://github.com/PatrickMassot/leanblueprint) for this).

**Remark 2**. The original proof reduced to a determinental identity
<a href="#ref-2020arXiv201202187N" class="citation"
data-cites="2020arXiv201202187N">(Nelson 2023, Theorem 17.2)</a> that
was verified using some geometric invariant theory. We decided to
formalize a related but more elementary argument noted in
<a href="#ref-2023arXiv2309.06314" class="citation"
data-cites="2023arXiv2309.06314">(Hu and Nelson 2023, Remark 5.15)</a>.

Theorem <a href="#theorem:cnee1j2i90" data-reference-type="ref"
data-reference="theorem:cnee1j2i90">1</a> extends (with the same proof)
to algebraically closed fields of characteristic
<span class="math inline">\\\neq 2\\</span> (`MainConcrete` in
[MainConcrete](MainConcrete.lean)). It generalizes further to
commutative rings in which <span class="math inline">\\2\\</span> is a
unit, and may be formulated in the language of endomorphisms of finite
free modules (see <a href="#ref-2023arXiv2309.06314" class="citation"
data-cites="2023arXiv2309.06314">(Hu and Nelson 2023, Remark 5.15)</a>):

**Theorem 3**. *(`MainAbstract` in [MainAbstract](MainAbstract.lean))*

*Let <span class="math inline">\\R\\</span> be a nontrivial commutative
ring in which <span class="math inline">\\2\\</span> is a unit. Let
<span class="math inline">\\V\\</span> be a finite free module over
<span class="math inline">\\R\\</span>. Let
<span class="math inline">\\\tau \in {\mathop{\mathrm{End}}}\_R(V \times
R)\\</span>, with projection <span class="math inline">\\\tau\_0 \in
{\mathop{\mathrm{End}}}\_R(V)\\</span>. Assume that the characteristic
polynomials of <span class="math inline">\\\tau\\</span> and
<span class="math inline">\\\tau\_0\\</span> are coprime.*

*Let <span class="math inline">\\x \in {\mathop{\mathrm{End}}}\_R(V
\times R)\\</span> with <span class="math inline">\\\[x,\tau\] =
0\\</span>, let <span class="math inline">\\z\\</span> denote the image
under the extension-by-zero map
<span class="math inline">\\{\mathop{\mathrm{End}}}\_R(V) \rightarrow
{\mathop{\mathrm{End}}}\_R(V \times R)\\</span> of the identity
endomorphism of <span class="math inline">\\V\\</span> (corresponding to
the matrix
<span class="math inline">\\\mathop{\mathrm{diag}}(1,\dotsc,1,0)\\</span>),
and suppose that <span class="math display">\\\[x,\[z,\tau\]\] = \[y,
\tau\]\\</span> for some <span class="math inline">\\y \in
{\mathop{\mathrm{End}}}\_R(V)\\</span>, extended by zero to an element
of <span class="math inline">\\{\mathop{\mathrm{End}}}\_R(V \times
R)\\</span>. Then <span class="math inline">\\x\\</span> is a scalar
endomorphism.*

**Remark 4**. We have formalized only the special case of Theorem
<a href="#theorem:cnee1jt0hq" data-reference-type="ref"
data-reference="theorem:cnee1jt0hq">3</a> in which
<span class="math inline">\\R\\</span> is a field. This case suffices
for Theorem <a href="#theorem:cnee1j2i90" data-reference-type="ref"
data-reference="theorem:cnee1j2i90">1</a>, which was our motivating
goal. To deduce the general case would require one further
formalization, namely that of Lemma
<a href="#lemma:cnee1m7ggm" data-reference-type="ref"
data-reference="lemma:cnee1m7ggm">9</a>, below.

To verify that the hypotheses of Theorem
<a href="#theorem:cnee1j2i90" data-reference-type="ref"
data-reference="theorem:cnee1j2i90">1</a> translate to those of Theorem
<a href="#theorem:cnee1jt0hq" data-reference-type="ref"
data-reference="theorem:cnee1jt0hq">3</a>, we use the following:

**Lemma 5**. (`coprime_of_disjoint_roots` in
[CoprimeOfDisjointRoots](CoprimeOfDisjointRoots.lean))

Let <span class="math inline">\\R\\</span> be an algebraically closed
field. Let <span class="math inline">\\p, q \in R\[X\]\\</span> be
nonzero polynomials with no common root. Then
<span class="math inline">\\p\\</span> and
<span class="math inline">\\q\\</span> are coprime, that is to say, we
can write <span class="math inline">\\1 = a p + b q\\</span> with
<span class="math inline">\\a,b \in R\[X\]\\</span>.

Formalizing the passage from Theorem
<a href="#theorem:cnee1jt0hq" data-reference-type="ref"
data-reference="theorem:cnee1jt0hq">3</a> to
<a href="#theorem:cnee1j2i90" data-reference-type="ref"
data-reference="theorem:cnee1j2i90">1</a> requires checking that various
operations are compatible with the passage from
<span class="math inline">\\V \times R\\</span> to
<span class="math inline">\\R^{n+1}\\</span> obtained by choosing a
basis of <span class="math inline">\\V\\</span>. This is done,
laboriously, in [MainConcrete](MainConcrete.lean).

It remains to explain the proof of (the field case of) Theorem
<a href="#theorem:cnee1j2i90" data-reference-type="ref"
data-reference="theorem:cnee1j2i90">1</a>. This requires a couple
further lemmas.

**Lemma 6**. (`cyclic_e_of_coprime_charpoly` and
`cyclic_e'_of_coprime_charpoly` in
[CyclicOfCoprime](CyclicOfCoprime.lean))

Let <span class="math inline">\\R\\</span> be a nontrivial commutative
ring. Let <span class="math inline">\\V\\</span> be a finite free
<span class="math inline">\\R\\</span>-module. Let
<span class="math inline">\\\tau \in {\mathop{\mathrm{End}}}\_R(V \times
R)\\</span> have the property that its and its projection to
<span class="math inline">\\{\mathop{\mathrm{End}}}\_R(V)\\</span> have
coprime characteristic polynomials. Then the vector
<span class="math inline">\\(0,1) \in V \times R\\</span> and the dual
vector <span class="math inline">\\(0,1)^t \in (V \times R)^\*\\</span>
are cyclic with respect to <span class="math inline">\\\tau\\</span>,
i.e., we can write every vector in the respective module as a polynomial
in <span class="math inline">\\\tau\\</span> applied to those vectors.

**Remark 7**. For the same reasons as in Remark
<a href="#remark:cnee1noh9i" data-reference-type="ref"
data-reference="remark:cnee1noh9i">4</a>, Lemma
<a href="#lemma:cnee1nm8ia" data-reference-type="ref"
data-reference="lemma:cnee1nm8ia">6</a> has only been fully formalized
over a field.

<a href="#" class="toggle-proof"><em>Proof.</em></a>

Let us show that <span class="math inline">\\(0,1)^t\\</span> is cyclic;
a similar argument gives the other assertion. We may reduce to the case
that <span class="math inline">\\R\\</span> is a field using Lemma
<a href="#lemma:cnee1m7ggm" data-reference-type="ref"
data-reference="lemma:cnee1m7ggm">9</a>, below (that lemma has not yet
formalized, but is irrelevant if we restrict from the outset to the
field case).

Let <span class="math inline">\\W \leq (V \times R)^\*\\</span> denote
the <span class="math inline">\\R\[\tau\]\\</span>-submodule generated
by <span class="math inline">\\(0,1)^t\\</span>; our task is to show
that <span class="math inline">\\W = (V \times R)^\*\\</span>.

Let <span class="math inline">\\U \leq V \times R\\</span> denote the
coannihilator of <span class="math inline">\\W\\</span> (i.e., the
kernel of the natural map <span class="math inline">\\V \times R
\rightarrow W^\*\\</span>). By duality for finite free modules over
fields, it is equivalent to check that <span class="math inline">\\U =
0\\</span>. Since <span class="math inline">\\W\\</span> contains
<span class="math inline">\\(0,1)^t\\</span>, we see that
<span class="math inline">\\U\\</span> is contained in the first summand
<span class="math inline">\\V \hookrightarrow V \times R\\</span>.
Furthermore, it is clear by construction that
<span class="math inline">\\U\\</span> is an
<span class="math inline">\\R\[\tau\]\\</span>-submodule of
<span class="math inline">\\V \times R\\</span>.

We have reduced to verifying the following
(`no_invariant_subspaces_of_coprime_charpoly` in
[CyclicOfCoprime](CyclicOfCoprime.lean)):

-   if <span class="math inline">\\U\\</span> is an
    <span class="math inline">\\R\[\tau\]\\</span>-submodule of
    <span class="math inline">\\V \times R\\</span> contained in the
    first summand <span class="math inline">\\V \hookrightarrow V \times
    R\\</span>, then <span class="math inline">\\U = 0\\</span>.

To that end, let <span class="math inline">\\u \in U\\</span>; we must
show that <span class="math inline">\\u = 0\\</span>. Let
<span class="math inline">\\\tau\_0 \in
{\mathop{\mathrm{End}}}\_R(V)\\</span> denote the projection of
<span class="math inline">\\\tau\\</span>, and let
<span class="math inline">\\p, p\_0 \in R\[X\]\\</span> denote the
characteristic polynomials of <span class="math inline">\\\tau,
\tau\_0\\</span>. By hypothesis, we may write
<span class="math inline">\\1 = a p\_\tau + b p\_{\tau\_0}\\</span> for
some <span class="math inline">\\a, b \in R\[X\]\\</span>. By evaluating
this abstract identity of polynomials on
<span class="math inline">\\\tau\\</span> and appealing to the
consequence <span class="math inline">\\p(\tau) = 0\\</span> of the
Cayley–Hamilton theorem, we see that <span class="math inline">\\u =
b(\tau) p\_0(\tau) u\\</span>. On the other hand, since
<span class="math inline">\\u\\</span> lies in the
<span class="math inline">\\R\[\tau\]\\</span>-submodule
<span class="math inline">\\U\\</span> of <span class="math inline">\\V
\hookrightarrow V \times R\\</span>, we see by induction on the degree
of <span class="math inline">\\p\\</span> that
<span class="math inline">\\p\_0(\tau) u = p\_0(\tau\_0) u\\</span>. By
another appeal to Cayley–Hamilton, we have
<span class="math inline">\\p\_0(\tau\_0) = 0\\</span>. It follows that
<span class="math inline">\\u = 0\\</span>, as required. ◻

**Lemma 8**. (`injective_of_cyclic` and `injective_of_cyclic'` in
[InjectiveOfCyclic](InjectiveOfCyclic.lean))

Let <span class="math inline">\\R\\</span> be a nontrivial commutative
ring. Let <span class="math inline">\\V\\</span> be a finite free
<span class="math inline">\\R\\</span>-module (in practice, this will
play the role of the module “<span class="math inline">\\V \times
R\\</span>” appearing above). Let <span class="math inline">\\\tau \in
{\mathop{\mathrm{End}}}\_R(V)\\</span>

1.  <span id="enumerate:cnee1ov2p9" label="enumerate:cnee1ov2p9"></span>
    If <span class="math inline">\\e \in V\\</span> is cyclic with
    respect to <span class="math inline">\\\tau\\</span>, then the map
    <span class="math display">\\\left\\ x \in
    {\mathop{\mathrm{End}}}\_R(V) : \[x,\tau\] = 0 \right\\ \rightarrow
    V\\</span> <span class="math display">\\x \mapsto x e\\</span> is
    injective.

2.  Dually, if <span class="math inline">\\e^\* \in V^\*\\</span> is
    cyclic with respect to <span class="math inline">\\\tau\\</span>,
    then the map <span class="math display">\\\left\\ x \in
    {\mathop{\mathrm{End}}}\_R(V) : \[x,\tau\] = 0 \right\\ \rightarrow
    V^\*\\</span> <span class="math display">\\x \mapsto e^\* x\\</span>
    is injective.

<a href="#" class="toggle-proof"><em>Proof.</em></a>

We verify <a href="#enumerate:cnee1ov2p9" data-reference-type="eqref"
data-reference="enumerate:cnee1ov2p9">\((i)\)</a>, as the proof of
<a href="#enumerate:cnee1ov375" data-reference-type="eqref"
data-reference="enumerate:cnee1ov375">\((ii)\)</a> is similar. It is
enough to show that, for <span class="math inline">\\x \in
{\mathop{\mathrm{End}}}\_R(V)\\</span> with
<span class="math inline">\\\[x,\tau\] = 0\\</span> and
<span class="math inline">\\x e = 0\\</span>, we have
<span class="math inline">\\x = 0\\</span>. It is enough to show that
<span class="math inline">\\x v = 0\\</span> for each
<span class="math inline">\\v \in V\\</span>. By hypothesis, we may
write <span class="math inline">\\v = p(\tau) e\\</span> for some
<span class="math inline">\\p \in R\[X\]\\</span>. Since
<span class="math inline">\\x\\</span> commutes with
<span class="math inline">\\\tau\\</span>, we see by induction on the
degree of <span class="math inline">\\p\\</span> that it also commutes
with <span class="math inline">\\p(\tau)\\</span>. Thus
<span class="math inline">\\x v = x p(\tau) e = p(\tau) x e =
0\\</span>, as required. ◻

Having established Lemmas
<a href="#lemma:cnee1nts0y" data-reference-type="ref"
data-reference="lemma:cnee1nts0y">5</a> and
<a href="#lemma:cnee1nm8ia" data-reference-type="ref"
data-reference="lemma:cnee1nm8ia">6</a>, we are now in position to
complete the proof of Theorem
<a href="#theorem:cnee1jt0hq" data-reference-type="ref"
data-reference="theorem:cnee1jt0hq">3</a>.

*Proof of Theorem
<a href="#theorem:cnee1jt0hq" data-reference-type="ref"
data-reference="theorem:cnee1jt0hq">3</a>.* (see
[MainAbstract](MainAbstract.lean))

Set <span class="math inline">\\t := \[x,z\] - y\\</span>. Then
<span class="math inline">\\\[x,z\] = t + y\\</span>, and by
<a href="#theorem:cnee1jt0hq" data-reference-type="ref"
data-reference="theorem:cnee1jt0hq">3</a>, we have
<span class="math inline">\\\[t,\tau\] = 0\\</span>.

Recall that <span class="math inline">\\z \in
{\mathop{\mathrm{End}}}\_R(V \times R)\\</span> is the extension by zero
of the identity endomorphism of the first summand
<span class="math inline">\\V\\</span> (in matrix language, this is
<span class="math inline">\\\mathop{\mathrm{diag}}(1,\dotsc,1,0)\\</span>).
Let <span class="math inline">\\e := (0,1) \in V \times R\\</span> and
<span class="math inline">\\e^\* := (0,1)^t \in (V \times R)^\*\\</span>
denote, respectively, the inclusion of the identity element in the
second summand and the projection onto the second factor. We may
identify <span class="math inline">\\e e^\* := e \otimes e^\*\\</span>
with the endomorphism of <span class="math inline">\\V \times R\\</span>
given by extension by zero of the identity endomorphism of the second
summand <span class="math inline">\\R\\</span> (in matrix language, this
is
<span class="math inline">\\\mathop{\mathrm{diag}}(0,\dotsc,0,1)\\</span>).
It follows that <span class="math inline">\\z + e e^\*\\</span> is the
identity endomorphism of <span class="math inline">\\V \times
R\\</span>, and in particular, commutes with
<span class="math inline">\\x\\</span>. We thus have
<span class="math inline">\\\[x,e e^\*\] = - t - y\\</span>. Let us
evaluate this last identity on the vectors
<span class="math inline">\\e\\</span> and
<span class="math inline">\\e^\*\\</span>. Recalling that
<span class="math inline">\\y\\</span> is the extension by zero of an
endomorphism of <span class="math inline">\\V\\</span>, we have
<span class="math inline">\\y e = 0\\</span> and
<span class="math inline">\\e^\* y = 0\\</span>, hence
<span class="math display">\\e = - t e\\</span> and
<span class="math display">\\e^\* \[x, e e^\* \] = - e^\* t.\\</span> On
the other hand, by expanding commutator brackets and using that
<span class="math inline">\\e^\* e = 1\\</span>, we compute that
<span class="math display">\\e = x (e e^\*) e - (e e^\*) x e = (x e) - e
(e^\* x e) = (x - e^\* x e) e,\\</span> where here
<span class="math inline">\\e^\* x e \in R\\</span> is identified with a
scalar endomorphism of <span class="math inline">\\V \times R\\</span>,
and similarly <span class="math display">\\e^\* \[x, e e^\*\] = e^\* x
(e e^\*) - e^\* (e e^\*) x = (e^\* x e) e^\* - e^\* x = - e^\* (x - e^\*
x e).\\</span> By Lemmas
<a href="#lemma:cnee1nts0y" data-reference-type="ref"
data-reference="lemma:cnee1nts0y">5</a> and
<a href="#lemma:cnee1nm8ia" data-reference-type="ref"
data-reference="lemma:cnee1nm8ia">6</a>, the maps defined on the
centralizer of <span class="math inline">\\\tau\\</span> given by
multiplication against <span class="math inline">\\e\\</span> or
<span class="math inline">\\e^\*\\</span> are injective. Since both
<span class="math inline">\\x - e^\* x e\\</span> and
<span class="math inline">\\t\\</span> centralize
<span class="math inline">\\\tau\\</span>, we deduce from the above four
identities that <span class="math display">\\x - e^\* x e = - t = - (x -
e^\* x e),\\</span> which implies that <span class="math inline">\\2 x =
2 (e^\* x e)\\</span>. By our hypothesis that
<span class="math inline">\\2\\</span> is a unit, we conclude that
<span class="math inline">\\x\\</span> is a scalar endomorphism. ◻

This completes our discussion of the proof of the field case of Theorem
<a href="#theorem:cnee1jt0hq" data-reference-type="ref"
data-reference="theorem:cnee1jt0hq">3</a>, hence that of Theorem
<a href="#theorem:cnee1j2i90" data-reference-type="ref"
data-reference="theorem:cnee1j2i90">1</a>.

The following would suffice to extend the formalization of Theorem
<a href="#theorem:cnee1jt0hq" data-reference-type="ref"
data-reference="theorem:cnee1jt0hq">3</a> to a general commutative ring
in which <span class="math inline">\\2\\</span> is a unit:

**Lemma 9**. Let <span class="math inline">\\R\\</span> be a commutative
ring. Let <span class="math inline">\\M\\</span> be a finitely-generated
<span class="math inline">\\R\\</span>-module, and let
<span class="math inline">\\N \leq M\\</span> be a submodule. Assume
that <span class="math inline">\\N + \mathfrak{m} M = M\\</span> for
each maximal ideal <span class="math inline">\\\mathfrak{m}\\</span> of
<span class="math inline">\\R\\</span>. Then
<span class="math inline">\\N = M\\</span>.

<a href="#" class="toggle-proof"><em>Proof.</em></a>

We can check whether <span class="math inline">\\N = M\\</span> after
localizing at each maximal ideal
<span class="math inline">\\\mathfrak{m}\\</span> of
<span class="math inline">\\R\\</span>
<a href="#ref-MR3525784" class="citation" data-cites="MR3525784">(Atiyah
and Macdonald 2016, Prop 3.9)</a>, so it suffices to consider the case
of a local ring <span class="math inline">\\R\\</span> with maximal
ideal <span class="math inline">\\\mathfrak{m}\\</span>. We can then
appeal to Nakayama’s lemma
<a href="#ref-MR3525784" class="citation" data-cites="MR3525784">(Atiyah
and Macdonald 2016, Cor 2.7)</a>. ◻

**Remark 10**. Mathlib contains suitable formulations of Nakayama’s
lemma. The main outstanding ingredient needed to formalize Lemma
<a href="#lemma:cnee1m7ggm" data-reference-type="ref"
data-reference="lemma:cnee1m7ggm">9</a> is the generalization of
`ideal_eq_bot_of_localization` from ideals to modules.

Atiyah, M. F., and I. G. Macdonald. 2016. *Introduction to Commutative
Algebra*. Economy. Addison-Wesley Series in Mathematics. Westview Press,
Boulder, CO.

Hu, Yueke, and Paul D Nelson. 2023. “Subconvex Bounds for
<span class="math inline">\\U\_{n+1}\times U\_n\\</span> in Horizontal
Aspects,” September. <http://arxiv.org/abs/2309.06314v2>.

Nelson, Paul D. 2023. “Spectral Aspect Subconvex Bounds for
<span class="math inline">\\U\_{n+1} \times U\_n\\</span>.” *Invent.
Math.* 232 (3): 1273–1438. <https://doi.org/10.1007/s00222-023-01180-x>.
