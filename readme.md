---
author:
- Paul D. Nelson
date: 18 January 2024
title: Proof of a linear algebra lemma, with links to the corresponding
  Lean 4 code
---

We formalize in Lean 4 a proof of [@2020arXiv201202187N Theorem 1.8]:

::: {#theorem:cnee1j2i90 .theorem}
**Theorem 1**. *(`MainConcrete'` in [MainConcrete](MainConcrete.lean))*

*Let $M_{n}$ denote the space of complex $n \times n$ matrices, included
in the space $M_{n+1}$ of $(n+1) \times (n+1)$ matrices as the
upper-left block, e.g., for $n = 2$, as $$\begin{pmatrix}
      \ast & \ast & 0 \\
      \ast & \ast & 0 \\
      0 & 0 & 0
    \end{pmatrix}.$$ Let $\tau$ be an element of $M_{n+1}$ with the
property that no eigenvalue of $\tau$ is also an eigenvalue of the
upper-left $n \times n$ submatrix $\tau_0$ of $\tau$. Let
$x \in M_{n+1}$ with $[x,\tau] = 0$, where $[a,b] := a b -b a$. Let $z$
denote the image in $M_{n+1}$ of the identity element of $M_n$, thus
$z = \mathop{\mathrm{diag}}(1,\dotsc,1,0)$ with $n$ ones. Suppose that
$$[x,[z,\tau]] = [y, \tau]$$ for some $y \in M_n$. Then $x$ is a scalar
matrix.*
:::

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

This result is perhaps of little intrinsic interest -- it is the "linear
algebra lemma" required at the end of a longer analytic argument -- but
I was nevertheless motivated to formalize it as an educational project.
In this note, we record a proof and indicate which parts correspond to
which Lean files and theorems (it would presumably be better to use
[blueprint](https://github.com/PatrickMassot/leanblueprint) for this).

::: remark
**Remark 2**. The original proof reduced to a determinental identity
[@2020arXiv201202187N Theorem 17.2] that was verified using some
geometric invariant theory. We decided to formalize a related but more
elementary argument noted in [@2023arXiv2309.06314 Remark 5.15].
:::

Theorem [1](#theorem:cnee1j2i90){reference-type="ref"
reference="theorem:cnee1j2i90"} extends (with the same proof) to
algebraically closed fields of characteristic $\neq 2$ (`MainConcrete`
in [MainConcrete](MainConcrete.lean)). It generalizes further to
commutative rings in which $2$ is a unit, and may be formulated in the
language of endomorphisms of finite free modules (see
[@2023arXiv2309.06314 Remark 5.15]):

::: {#theorem:cnee1jt0hq .theorem}
**Theorem 3**. *(`MainAbstract` in [MainAbstract](MainAbstract.lean))*

*Let $R$ be a nontrivial commutative ring in which $2$ is a unit. Let
$V$ be a finite free module over $R$. Let
$\tau \in \mathop{\mathrm{End}}_R(V \times R)$, with projection
$\tau_0 \in \mathop{\mathrm{End}}_R(V)$. Assume that the characteristic
polynomials of $\tau$ and $\tau_0$ are coprime.*

*Let $x \in \mathop{\mathrm{End}}_R(V \times R)$ with $[x,\tau] = 0$,
let $z$ denote the image under the extension-by-zero map
$\mathop{\mathrm{End}}_R(V) \rightarrow \mathop{\mathrm{End}}_R(V \times R)$
of the identity endomorphism of $V$ (corresponding to the matrix
$\mathop{\mathrm{diag}}(1,\dotsc,1,0)$), and suppose that
$$[x,[z,\tau]] = [y, \tau]$$ for some
$y \in \mathop{\mathrm{End}}_R(V)$, extended by zero to an element of
$\mathop{\mathrm{End}}_R(V \times R)$. Then $x$ is a scalar
endomorphism.*
:::

::: {#remark:cnee1noh9i .remark}
**Remark 4**. We have formalized only the special case of Theorem
[3](#theorem:cnee1jt0hq){reference-type="ref"
reference="theorem:cnee1jt0hq"} in which $R$ is a field. This case
suffices for Theorem [1](#theorem:cnee1j2i90){reference-type="ref"
reference="theorem:cnee1j2i90"}, which was our motivating goal. To
deduce the general case would require one further formalization, namely
that of Lemma [9](#lemma:cnee1m7ggm){reference-type="ref"
reference="lemma:cnee1m7ggm"}, below.
:::

To verify that the hypotheses of Theorem
[1](#theorem:cnee1j2i90){reference-type="ref"
reference="theorem:cnee1j2i90"} translate to those of Theorem
[3](#theorem:cnee1jt0hq){reference-type="ref"
reference="theorem:cnee1jt0hq"}, we use the following:

::: {#lemma:cnee1nts0y .lemma}
**Lemma 5**. (`coprime_of_disjoint_roots` in
[CoprimeOfDisjointRoots](CoprimeOfDisjointRoots.lean))

Let $R$ be an algebraically closed field. Let $p, q \in R[X]$ be nonzero
polynomials with no common root. Then $p$ and $q$ are coprime, that is
to say, we can write $1 = a p + b q$ with $a,b \in R[X]$.
:::

Formalizing the passage from Theorem
[3](#theorem:cnee1jt0hq){reference-type="ref"
reference="theorem:cnee1jt0hq"} to
[1](#theorem:cnee1j2i90){reference-type="ref"
reference="theorem:cnee1j2i90"} requires checking that various
operations are compatible with the passage from $V \times R$ to
$R^{n+1}$ obtained by choosing a basis of $V$. This is done,
laboriously, in [MainConcrete](MainConcrete.lean).

It remains to explain the proof of (the field case of) Theorem
[1](#theorem:cnee1j2i90){reference-type="ref"
reference="theorem:cnee1j2i90"}. This requires a couple further lemmas.

::: {#lemma:cnee1nm8ia .lemma}
**Lemma 6**. (`cyclic_e_of_coprime_charpoly` and
`cyclic_e'_of_coprime_charpoly` in
[CyclicOfCoprime](CyclicOfCoprime.lean))

Let $R$ be a nontrivial commutative ring. Let $V$ be a finite free
$R$-module. Let $\tau \in \mathop{\mathrm{End}}_R(V \times R)$ have the
property that its and its projection to $\mathop{\mathrm{End}}_R(V)$
have coprime characteristic polynomials. Then the vector
$(0,1) \in V \times R$ and the dual vector $(0,1)^t \in (V \times R)^*$
are cyclic with respect to $\tau$, i.e., we can write every vector in
the respective module as a polynomial in $\tau$ applied to those
vectors.
:::

::: remark
**Remark 7**. For the same reasons as in Remark
[4](#remark:cnee1noh9i){reference-type="ref"
reference="remark:cnee1noh9i"}, Lemma
[6](#lemma:cnee1nm8ia){reference-type="ref"
reference="lemma:cnee1nm8ia"} has only been fully formalized over a
field.
:::

::: proof
*Proof.* Let us show that $(0,1)^t$ is cyclic; a similar argument gives
the other assertion. We may reduce to the case that $R$ is a field using
Lemma [9](#lemma:cnee1m7ggm){reference-type="ref"
reference="lemma:cnee1m7ggm"}, below (that lemma has not yet formalized,
but is irrelevant if we restrict from the outset to the field case).

Let $W \leq (V \times R)^*$ denote the $R[\tau]$-submodule generated by
$(0,1)^t$; our task is to show that $W = (V \times R)^*$.

Let $U \leq V \times R$ denote the coannihilator of $W$ (i.e., the
kernel of the natural map $V \times R \rightarrow W^*$). By duality for
finite free modules over fields, it is equivalent to check that $U = 0$.
Since $W$ contains $(0,1)^t$, we see that $U$ is contained in the first
summand $V \hookrightarrow V \times R$. Furthermore, it is clear by
construction that $U$ is an $R[\tau]$-submodule of $V \times R$.

We have reduced to verifying the following
(`no_invariant_subspaces_of_coprime_charpoly` in
[CyclicOfCoprime](CyclicOfCoprime.lean)):

-   if $U$ is an $R[\tau]$-submodule of $V \times R$ contained in the
    first summand $V \hookrightarrow V \times R$, then $U = 0$.

To that end, let $u \in U$; we must show that $u = 0$. Let
$\tau_0 \in \mathop{\mathrm{End}}_R(V)$ denote the projection of $\tau$,
and let $p, p_0 \in R[X]$ denote the characteristic polynomials of
$\tau, \tau_0$. By hypothesis, we may write
$1 = a p_\tau + b p_{\tau_0}$ for some $a, b \in R[X]$. By evaluating
this abstract identity of polynomials on $\tau$ and appealing to the
consequence $p(\tau) = 0$ of the Cayley--Hamilton theorem, we see that
$u = b(\tau) p_0(\tau) u$. On the other hand, since $u$ lies in the
$R[\tau]$-submodule $U$ of $V \hookrightarrow V \times R$, we see by
induction on the degree of $p$ that $p_0(\tau) u = p_0(\tau_0) u$. By
another appeal to Cayley--Hamilton, we have $p_0(\tau_0) = 0$. It
follows that $u = 0$, as required. ◻
:::

::: {#enumerate:cnee1ov375 .lemma}
**Lemma 8**. (`injective_of_cyclic` and `injective_of_cyclic'` in
[InjectiveOfCyclic](InjectiveOfCyclic.lean))

Let $R$ be a nontrivial commutative ring. Let $V$ be a finite free
$R$-module (in practice, this will play the role of the module
"$V \times R$" appearing above). Let
$\tau \in \mathop{\mathrm{End}}_R(V)$

(i) []{#enumerate:cnee1ov2p9 label="enumerate:cnee1ov2p9"} If $e \in V$
    is cyclic with respect to $\tau$, then the map
    $$\left\{ x \in \mathop{\mathrm{End}}_R(V) : [x,\tau] = 0 \right\} \rightarrow V$$
    $$x \mapsto x e$$ is injective.

(ii) Dually, if $e^* \in V^*$ is cyclic with respect to $\tau$, then the
     map
     $$\left\{ x \in \mathop{\mathrm{End}}_R(V) : [x,\tau] = 0 \right\} \rightarrow V^*$$
     $$x \mapsto e^* x$$ is injective.
:::

::: proof
*Proof.* We verify
[\[enumerate:cnee1ov2p9\]](#enumerate:cnee1ov2p9){reference-type="eqref"
reference="enumerate:cnee1ov2p9"}, as the proof of
[\[enumerate:cnee1ov375\]](#enumerate:cnee1ov375){reference-type="eqref"
reference="enumerate:cnee1ov375"} is similar. It is enough to show that,
for $x \in \mathop{\mathrm{End}}_R(V)$ with $[x,\tau] = 0$ and
$x e = 0$, we have $x = 0$. It is enough to show that $x v = 0$ for each
$v \in V$. By hypothesis, we may write $v = p(\tau) e$ for some
$p \in R[X]$. Since $x$ commutes with $\tau$, we see by induction on the
degree of $p$ that it also commutes with $p(\tau)$. Thus
$x v = x p(\tau) e = p(\tau) x e = 0$, as required. ◻
:::

Having established Lemmas [5](#lemma:cnee1nts0y){reference-type="ref"
reference="lemma:cnee1nts0y"} and
[6](#lemma:cnee1nm8ia){reference-type="ref"
reference="lemma:cnee1nm8ia"}, we are now in position to complete the
proof of Theorem [3](#theorem:cnee1jt0hq){reference-type="ref"
reference="theorem:cnee1jt0hq"}.

::: proof
*Proof of Theorem [3](#theorem:cnee1jt0hq){reference-type="ref"
reference="theorem:cnee1jt0hq"}.* (see
[MainAbstract](MainAbstract.lean))

Set $t := [x,z] - y$. Then $[x,z] = t + y$, and by
[3](#theorem:cnee1jt0hq){reference-type="ref"
reference="theorem:cnee1jt0hq"}, we have $[t,\tau] = 0$.

Recall that $z \in \mathop{\mathrm{End}}_R(V \times R)$ is the extension
by zero of the identity endomorphism of the first summand $V$ (in matrix
language, this is $\mathop{\mathrm{diag}}(1,\dotsc,1,0)$). Let
$e := (0,1) \in V \times R$ and $e^* := (0,1)^t \in (V \times R)^*$
denote, respectively, the inclusion of the identity element in the
second summand and the projection onto the second factor. We may
identify $e e^* := e \otimes e^*$ with the endomorphism of $V \times R$
given by extension by zero of the identity endomorphism of the second
summand $R$ (in matrix language, this is
$\mathop{\mathrm{diag}}(0,\dotsc,0,1)$). It follows that $z + e e^*$ is
the identity endomorphism of $V \times R$, and in particular, commutes
with $x$. We thus have $[x,e e^*] = - t - y$. Let us evaluate this last
identity on the vectors $e$ and $e^*$. Recalling that $y$ is the
extension by zero of an endomorphism of $V$, we have $y e = 0$ and
$e^* y = 0$, hence $$e = - t e$$ and $$e^* [x, e e^* ] = - e^* t.$$ On
the other hand, by expanding commutator brackets and using that
$e^* e = 1$, we compute that
$$e = x (e e^*) e - (e e^*) x e = (x e) - e (e^* x e) = (x - e^* x e) e,$$
where here $e^* x e \in R$ is identified with a scalar endomorphism of
$V \times R$, and similarly
$$e^* [x, e e^*] = e^* x (e e^*)  - e^* (e e^*) x = (e^* x e) e^* - e^* x = - e^* (x - e^* x e).$$
By Lemmas [5](#lemma:cnee1nts0y){reference-type="ref"
reference="lemma:cnee1nts0y"} and
[6](#lemma:cnee1nm8ia){reference-type="ref"
reference="lemma:cnee1nm8ia"}, the maps defined on the centralizer of
$\tau$ given by multiplication against $e$ or $e^*$ are injective. Since
both $x - e^* x e$ and $t$ centralize $\tau$, we deduce from the above
four identities that $$x - e^* x e = - t = - (x - e^* x e),$$ which
implies that $2 x = 2 (e^* x e)$. By our hypothesis that $2$ is a unit,
we conclude that $x$ is a scalar endomorphism. ◻
:::

This completes our discussion of the proof of the field case of Theorem
[3](#theorem:cnee1jt0hq){reference-type="ref"
reference="theorem:cnee1jt0hq"}, hence that of Theorem
[1](#theorem:cnee1j2i90){reference-type="ref"
reference="theorem:cnee1j2i90"}.

The following would suffice to extend the formalization of Theorem
[3](#theorem:cnee1jt0hq){reference-type="ref"
reference="theorem:cnee1jt0hq"} to a general commutative ring in which
$2$ is a unit:

::: {#lemma:cnee1m7ggm .lemma}
**Lemma 9**. Let $R$ be a commutative ring. Let $M$ be a
finitely-generated $R$-module, and let $N \leq M$ be a submodule. Assume
that $N + \mathfrak{m} M = M$ for each maximal ideal $\mathfrak{m}$ of
$R$. Then $N = M$.
:::

::: proof
*Proof.* We can check whether $N = M$ after localizing at each maximal
ideal $\mathfrak{m}$ of $R$ [@MR3525784 Prop 3.9], so it suffices to
consider the case of a local ring $R$ with maximal ideal $\mathfrak{m}$.
We can then appeal to Nakayama's lemma [@MR3525784 Cor 2.7]. ◻
:::

::: remark
**Remark 10**. Mathlib contains suitable formulations of Nakayama's
lemma. The main outstanding ingredient needed to formalize Lemma
[9](#lemma:cnee1m7ggm){reference-type="ref"
reference="lemma:cnee1m7ggm"} is the generalization of
`ideal_eq_bot_of_localization` from ideals to modules.
:::

::: thebibliography
1

M. F. Atiyah and I. G. Macdonald. . Addison-Wesley Series in
Mathematics. Westview Press, Boulder, CO, economy edition, 2016. For the
1969 original see \[MR0242802\].

Yueke Hu and Paul D Nelson. Subconvex bounds for $u_{n+1}\times u_n$ in
horizontal aspects. 2023. arXiv:2309.06314.

Paul D. Nelson. Spectral aspect subconvex bounds for
$U_{n+1} \times U_n$. , 232(3):1273--1438, 2023.
:::
