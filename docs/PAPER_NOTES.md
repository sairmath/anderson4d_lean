# Formalization conventions for the paper's v1 text

This file records four local choices made while translating Deng--Shen,
*The four-dimensional Anderson model: a case study for critical SPDEs*
([arXiv:2607.10105v1](https://arxiv.org/abs/2607.10105)) that matter when its
proof is represented with explicit constants and data structures in Lean.

The first three state the constant, exponent, or counting convention used by
Lean at points where a fully explicit term is needed. The fourth makes the
periodic-lift convention explicit for the torus discretization. These are
formalization conventions, not proposed changes to the paper. None changes
the statement of the main theorem, any numbered proposition, or any theorem
statement in this project.

## (5.69): the inclusive ancestor sum has constant 2

In the last inequality of (5.69) (paper §5.4.3, pp. 38--39), reversing the
order of summation produces the inner sum

$$
  \sum_{\mathfrak n\geq\mathfrak m,\ \mathfrak n\ne\mathfrak r}
    \frac{N_{\mathfrak m}}{N_{\mathfrak n}}.
$$

With the inclusive convention
$\mathfrak m\leq\mathfrak n$, the self term is already $1$.  When
$\mathfrak m$ has a non-root strict ancestor, the sum is therefore larger
than $1$.  Strict dyadic growth toward the root gives the uniform bound
$2$: the self term contributes $1$, and the strict-ancestor geometric
tail contributes at most $1$.

The Lean proof records the bound with constant $2$ instead of hiding it in an
implicit absolute constant. It is absorbed into the existing $C^m$ factor,
so Proposition 5.10 and all downstream statements are unchanged.

## (5.83): the simple-leaf exponent is $2(m_{\mathfrak l}-2)$

In the formalized simple-majority argument (paper §5.4.3, pp. 40--41), Lean
instantiates the payoff used with (5.76), (5.80), and (5.81) as

$$
  \prod_{\mathfrak l\in\mathcal L^S}
    N_{\mathfrak l^+}^{\,2(m_{\mathfrak l}-2)}.
$$

This is the exponent in the first product of (5.83), the inequality
immediately preceding it, and the downstream payoff. Another display in the
same passage uses $2(m_{\mathfrak l}-1)$. Since Lean requires a single
explicit term, the formalization adopts the former value locally, including
the observation $2(m_{\mathfrak l}-2)\geq m_{\mathfrak l}/2$ used by (5.81).
No claim is made here about intended typesetting in a future paper version.

This convention does not change Proposition 5.10 or its constants.

## (5.43): the intermediate boundary count is $2(s+1)$

In Step 2 of the proof of Proposition 5.9 (paper §5.4.1, pp. 33--35), a
skipped set $O$ of size $s$ breaks the inside word into $s+1$ nonempty
blocks. Each block has at most two boundaries with the outside word, so Lean
uses the elementary intermediate bound

$$
  2(s+1),
$$

The example following (5.48) has $s=1$ and four such crossings, illustrating
this block-counting convention.

The final estimate (5.43) follows unchanged: since all $s+1$ blocks are
nonempty, $s+1\leq n$, and the number of changed boundary factors is still
at most $2n$.  The Lean proof uses this count and obtains the same $4^n$
loss as the paper.

## (5.3): the discretization uses occurrence-wise periodic lifts

In §5.1 (paper pp. 21--22), canonical representatives
$x_j\in[-\pi,\pi]^4$ and labels
$y_j=\lfloor\varepsilon^{-1}x_j\rfloor$ are chosen. In Lean, a chain that
crosses the cut of the fundamental cube must additionally remember compatible
periodic representatives: two adjacent torus cells can have centre
distance $O(\varepsilon)$ while their canonical integer labels differ by
$O(\varepsilon^{-1})$.

The formalization therefore chooses occurrence-wise periodic lifts of the cell
labels along the chain. Equivalently, before choosing lifts one may retain the
periodic edge weight

$$
  \frac{\varepsilon^2}
       {\varepsilon^2+
        d_{\mathbb T^4}(\varepsilon a,\varepsilon b)^2}.
$$

On a no-wrap lifted edge this is exactly the ordinary lattice weight used in
the paper.  The remaining finite sum keeps the winding data, so no uniform
pointwise comparison with canonical labels is asserted.

This convention is explicit and fully proved in Lean: the unwrapping and
winding reindexing are implemented in
`Anderson4D/Continuum/PeriodicQuotient.lean`, and the endpoint sum is closed in
`Anderson4D/Continuum/PrimitiveEndpointPeriodic.lean`.  They feed the checked
theorems
`Anderson4D.sum_primitiveInsertedIntegrand_lintegral_le_r51GlobalDecayBound`
and `Anderson4D.proposition41`. This makes the representative convention
explicit, with no change to Proposition 4.1 or any later statement.
