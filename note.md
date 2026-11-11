# The $N^{\sqrt2+o(1)}$ construction for Hurwitz's problem, written out in terms of bilinear forms

**Lindsay Debnath** · version 1, 10 November 2026

*This is a Markdown copy of `note.tex`, with the same content; `note.pdf` is compiled from `note.tex`.*

**Abstract.** For every $N$ there are integer bilinear forms $f_1,g_1,\dots,f_K,g_K$ in $x_1,\dots,x_N,y_1,\dots,y_N$ with $h!\,(\sum_i x_i^2)(\sum_j y_j^2)=\sum_{k\le K} f_kg_k$ and $K=N^{\sqrt2+o(1)}$, where $h=O(\log^2N)$ is the least integer with at least $N$ partitions. This follows from Theorem B of *A $2^{o(n)}$ time algorithm for 3-SAT* [ETH], as first pointed out in [Sie]. This note does four things. It restates the construction directly as an identity of bilinear forms, gives the coefficients explicitly, writes out the proofs of the two lemmas it rests on with the compressed steps filled in, and says exactly what is machine-checked. Nothing here is new mathematics beyond [ETH]. The point is to make the construction checkable by a reader who works with polynomials rather than with the function language of [ETH].

## 1. The result and its status

Notation:

- $p(E)$ is the number of partitions of $E$, with $p(0)=1$ and $p(E)=0$ for $E<0$.
- $\mathcal P_h$ is the set of partitions of $h$.
- $B_F(N)$ is the least $s$ with $(\sum_{i\le N}x_i^2)(\sum_{j\le N}y_j^2)=\sum_{k\le s}f_kf'_k$, where the $f_k,f'_k$ are bilinear over $F$. This is $B_F(\mathrm{SOS}_N)$ of [HWY], and the bilinear-product variant (9) of [Hru].

**Theorem 1.** Let $h\ge1$ and $K_h=\sum_{j=0}^{2h}(4h-2j+1)\,p(j)$. There are bilinear forms $f_k,g_k$ ($k\le K_h$; some products $f_kg_k$ may vanish) in variables $x_\xi,y_\eta$ indexed by $\xi,\eta\in\mathcal P_h$, with integer coefficients given explicitly in Section 3, such that
$$h!\Big(\sum_{\xi\in\mathcal P_h}x_\xi^2\Big)\Big(\sum_{\eta\in\mathcal P_h}y_\eta^2\Big)=\sum_{k=1}^{K_h}f_kg_k .$$

Setting all but $N\le p(h)$ of the $x$'s and $y$'s to zero gives the identity for $N$ variables. Take $h$ least with $p(h)\ge N$. Then the Hardy–Ramanujan asymptotics give $K_h=N^{\sqrt2+o(1)}$ (Section 5, for $N=2^\lambda$; for other $N$ use $2^{\lambda-1}<N\le2^\lambda$).

**Corollary 2.** $B_\mathbb{Q}(N)\le N^{\sqrt2+o(1)}$. The same holds over any field of characteristic $0$ or of characteristic larger than $h=O(\log^2N)$. By [HWY, Remark 1.5], $\sigma_\mathbb{C}(N)\le 3B_\mathbb{C}(N)\le N^{\sqrt2+o(1)}$, where $\sigma_\mathbb{C}(N)$ is the least number of squares in Hurwitz's problem over $\mathbb{C}$.

The previous best upper bound is $N^{c+o(1)}$ with $c=1+2H(\alpha/2)\approx1.6147$, where $H(\alpha)=\tfrac12$ ([Hru, Theorem 1 and its proof in §4], stated there as $O(N^{c'})$ with $c'<1.62$; for the bilinear-product form (9) see [Hru, §5.1, Remark 18], and [HruCCC, Theorem 12] for a direct proof over every field). That bound also holds in positive characteristic, where the present identity says nothing, since $h!=0$ once $p\le h$. The open problem in [Hru, §7] asks whether $\sigma_\mathbb{C}(N)\le N^{1.5+o(1)}$ can be reached through parity representations. The bound here is below that target, by a different route.

**Remark 3 (a consequence we have not checked beyond substitution).** The proof of [Hru, Theorem 25] uses Theorem 1 there only as a black box, $\sigma(n)=O(n^{1+\delta})$, and obtains $\mathrm{size}^{(nc)}(\mathrm{ID}_n)\le n^{(3+\omega(3)+\delta)/4+o(1)}$. Substituting $\delta=\sqrt2-1$ and $\omega(3)<4.1997$ gives an exponent below $1.904$ (instead of $1.954$), over fields of characteristic $0$.

**Status.**

- **Theorem B in Lean.** Theorem B of [ETH] is formalized in Lean 4 with Mathlib in [FM] (commit `16a5ce41`). The statement file `eth/proof/statements/AppHalfPiecesStatement.lean` restates Appendix B in the paper's words. It holds definitions and statements only, about 240 lines, and imports Mathlib and two short statement files. `GeneralPieces.thmHalfPiecesPure` proves it.
- **Our rebuild.** We rebuilt this from source (`lake exe cache get; lake build GeneralPieces.Main`) and ran `#print axioms`. The only axioms are `propext`, `Classical.choice` and `Quot.sound`.
- **The bound in polynomial terms.** We stated Corollary 2 (the bound over $\mathbb Q$, for $N$ a power of two) in terms of polynomials, in a file that imports Mathlib only. The excerpt below sits inside `namespace HurwitzSqrt2` with `open MvPolynomial Finset`; docstrings are omitted:

```lean
abbrev Idx (lam : ℕ) : Type := Fin lam → Bool
abbrev Var (lam : ℕ) : Type := Idx lam ⊕ Idx lam
noncomputable def bil {lam : ℕ} (F : Idx lam → Idx lam → ℚ) : MvPolynomial (Var lam) ℚ :=
  ∑ i, ∑ j, C (F i j) * X (Sum.inl i) * X (Sum.inr j)
noncomputable def sos (lam : ℕ) : MvPolynomial (Var lam) ℚ :=
  (∑ i, X (Sum.inl i) ^ 2) * (∑ j, X (Sum.inr j) ^ 2)
def Statement : Prop :=
  ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam →
    ∃ (K : ℕ) (f g : Fin K → Idx lam → Idx lam → ℚ),
      (K : ℝ) ≤ (2 * lam : ℝ) ^ c * 2 ^ (Real.sqrt 2 * lam) ∧
      sos lam = ∑ k, bil (f k) * bil (g k)
```

- **The proof of that statement.** We proved `Statement` from `thmHalfPiecesPure` in `HurwitzProof.lean` (292 lines). That file restates the `HurwitzSqrt2` block rather than importing it; we diffed the two blocks and they are identical, and `#print axioms hurwitzSqrt2` gives the same three axioms.
- **What the Lean statement leaves out.** It has rational coefficients and does not contain the factor $h!$, integrality, or the exact count $K_h$ (its $K$ is $\sum_s2^{\lceil\log_2\min(R^{\rm row}_s,R^{\rm col}_s)\rceil}\le2K_h$). Those are checked numerically for $h\le5$ (Section 6) and follow from (54), (55).

So the claim rests on Lean's kernel, plus a reading of the definitions above and of Definition 7 as formalized (`Pieces.Family.Is` in `PiecesStatement.lean`, which matches the printed definition field by field, except the running-time clause of 7(c), which the bound does not need). The Lean development was written and reviewed by AI models, and no person is known to have read its proofs. Section 6 maps each step below to its Lean declaration.

## 2. The construction

**The Fock space.** Let $V=\mathbb{Q}[t_1,t_2,\dots]$, with $t_k$ of weight $k$.

- The monomials $t^\mu=\prod_it_{\mu_i}$, for $\mu$ a partition, form a basis, and $V_E$ (weight $E$) has dimension $p(E)$.
- For $k\ge1$ let $\nabla_{-k}=t_k\cdot$ and $\nabla_k=k\,\partial/\partial t_k$. Then $[\nabla_k,\nabla_{-l}]=k\delta_{kl}$. These are the Heisenberg relations, and $V$ is the Fock representation.
- For all $k\neq0$, $\nabla_k$ maps $V_E$ to $V_{E-k}$.
- Write $[t^{\sigma'}]\,T\,t^\sigma$ for a matrix entry of an operator $T$.

**The operators $a[r]$.** For a monomial $a=t^\mu$ with parts $\mu_1,\dots,\mu_n$ (listed with multiplicity) and $r\in\mathbb Z$, put
$$a[r]=\sum_{\substack{k_i\in\mathbb Z\setminus\{0\}\\ \sum k_i=-r}}\prod_i\binom{-k_i-1}{\mu_i-1}\prod_{i:k_i<0}\nabla_{k_i}\prod_{i:k_i>0}\nabla_{k_i}\qquad(47)$$
Here:

- All differentiations ($k_i>0$) are applied first, and $a[r]$ is extended linearly in $a$.
- $\binom{k}{j}=k(k-1)\cdots(k-j+1)/j!$ for all integers $k$.
- On $V_E$ only finitely many terms are nonzero, since the positive $k_i$ add up to at most $E$.
- $a[r]$ maps $V_E$ into $V_{E+r}$, with integer matrix entries if $a$ has integer coefficients.
- For example, $t_1[r]=\nabla_{-r}$ for $r\ne0$.

With $Y(a,\omega)=\sum_r a[r]\omega^{r-|\mu|}$, these are the coefficients of the fields of the Heisenberg vertex algebra [Fre, §2.3, (4)], as [ETH, App. H] notes. That connection is used only in Remark 6.

**The operators $Q_s$.** Let $h\ge1$, $b\in V_h$, and $a=\sum_{h'=0}^h\bar a_{h'}$ with $\bar a_{h'}\in V_{h'}$. Put $a^{\langle i\rangle}=\sum_{h'}\binom{h'+h}{i}\bar a_{h'}$ and, for $s\in\mathbb Z$,
$$Q_s(a,b)=\sum_{i=0}^{2h}(-1)^i a^{\langle i\rangle}[s-h+i]\,b[h-s-i],\qquad Q'_s(a,b)=\sum_{i=0}^{2h}(-1)^i\, b[h-s-i]\,a^{\langle i\rangle}[s-h+i].\qquad(48)$$
Both preserve weight. The weighting $a^{\langle i\rangle}$ makes $Q_s$ linear in $a$, while each homogeneous component $\bar a_{h'}$ is paired with its own binomial row $\binom{h'+h}{i}$. This is what lets the proof below handle an inhomogeneous $a$ one component at a time.

**Lemma 4 (Lemma 9 of [ETH]).** On $V_E$, for every $E\ge0$:

- (a) $Q_s(a,b)=Q'_s(a,b)$.
- (b) $Q_s(a,b)=0$ for $|s|>E+h$.
- (c) $\sum_{|s|\le E+h}Q_s(a,b)=(a[-h]b)\cdot\mathrm{Id}$, where $a[-h]b\in V_0=\mathbb{Q}$.

**Dual families.** For $n\ge1$ let $y_n=\sum_{j=1}^n\binom nj t_j$. These $y_n$ are unrelated to the variables $y_\eta$ of Theorem 1. For $\mu\in\mathcal P_h$ let
$$a^\mu=\prod_i(-1)^{\mu_i-1}y_{\mu_i},\qquad b^\mu=\tfrac{h!}{z_\mu}t^\mu,\qquad z_\mu=\prod_k k^{m_k(\mu)}m_k(\mu)!,$$
where $m_k(\mu)$ is the number of parts equal to $k$. The number $h!/z_\mu$ is an integer: it counts the permutations of cycle type $\mu$. The polynomial $a^\mu$ has integer coefficients and only monomials of weight $\le h$.

**Lemma 5 (Lemma 10 of [ETH]).** $a^\mu[-h]\,b^\nu=h!\,\delta_{\mu\nu}$ for all $\mu,\nu\in\mathcal P_h$.

**The identity.** For $\xi,\eta,\upsilon,\nu\in\mathcal P_h$ and $|s|\le2h$ let $A_s(\xi,\eta,\upsilon,\nu)=[t^\upsilon]\,Q_s(a^\xi,b^\nu)\,t^\eta$ (this is (53)). Lemma 4(b) and (c) with $E=h$, together with Lemma 5, give
$$\sum_{|s|\le2h}A_s(\xi,\eta,\upsilon,\nu)=h!\,\delta_{\xi\nu}\,\delta_{\eta\upsilon}.\qquad(\ast)$$
Equivalently, $\sum_s\sum A_s(\xi,\eta,\upsilon,\nu)\,x_\xi y_\eta x_\nu y_\upsilon=h!(\sum x_\xi^2)(\sum y_\eta^2)$. This holds already at the level of coefficient tensors. So it also holds for the non-commutative ID polynomial of [HWY], with $(\xi,\eta,\nu,\upsilon)$ in the positions $X,Y,X,Y$. What remains is to write each tensor $A_s$ as a short sum of products of two matrices, splitting the indices as $(\xi,\upsilon)\,|\,(\nu,\eta)$ or as $(\xi,\eta)\,|\,(\nu,\upsilon)$; commutatively, each such product is a product of two bilinear forms. (These two splittings are forms (b) and (a) of [HWY, Lemma 3.5], which matters for the non-commutative width of $h!\,\mathrm{ID}_N$; Theorem 1 itself does not need that lemma.)

## 3. The bilinear forms

For $\xi,\nu\in\mathcal P_h$ define integer matrices, with rows and columns indexed by partitions:
$$\alpha^{(i)}_r[\xi]_{\sigma'\sigma}=(-1)^i[t^{\sigma'}]\,(a^\xi)^{\langle i\rangle}[r]\,t^\sigma,\qquad \beta_r[\nu]_{\sigma'\sigma}=[t^{\sigma'}]\,b^\nu[r]\,t^\sigma.$$
Inserting $\mathrm{Id}=\sum_\sigma t^\sigma[t^\sigma]$ on the middle weight space in (48) gives two factorizations.

**Column-wise.** This comes directly from $Q_s$ and is display (55) of [ETH]. Since $b[h-s-i]t^\eta\in V_{2h-s-i}$,
$$A_s(\xi,\eta,\upsilon,\nu)=\sum_{i=0}^{2h}\sum_{\sigma\in\mathcal P_{2h-s-i}}\alpha^{(i)}_{s-h+i}[\xi]_{\upsilon\sigma}\;\beta_{h-s-i}[\nu]_{\sigma\eta}.$$
Each term $(i,\sigma)$ gives the pair
$$f_{s,i,\sigma}=\sum_{\xi,\upsilon}\alpha^{(i)}_{s-h+i}[\xi]_{\upsilon\sigma}x_\xi y_\upsilon,\qquad g_{s,i,\sigma}=\sum_{\nu,\eta}\beta_{h-s-i}[\nu]_{\sigma\eta}x_\nu y_\eta.$$

**Row-wise.** This comes from $Q'_s$, so it uses Lemma 4(a); it is display (54). Since $a^{\langle i\rangle}[s-h+i]t^\eta\in V_{s+i}$,
$$A_s(\xi,\eta,\upsilon,\nu)=\sum_{i=0}^{2h}\sum_{\sigma\in\mathcal P_{s+i}}\alpha^{(i)}_{s-h+i}[\xi]_{\sigma\eta}\;\beta_{h-s-i}[\nu]_{\upsilon\sigma},$$
$$f_{s,i,\sigma}=\sum_{\xi,\eta}\alpha^{(i)}_{s-h+i}[\xi]_{\sigma\eta}x_\xi y_\eta,\qquad g_{s,i,\sigma}=\sum_{\nu,\upsilon}\beta_{h-s-i}[\nu]_{\upsilon\sigma}x_\nu y_\upsilon.$$

In both cases, summing $f_{s,i,\sigma}g_{s,i,\sigma}$ over the terms gives coefficient $A_s(\xi,\eta,\upsilon,\nu)$ on $x_\xi y_\eta x_\nu y_\upsilon$. So by $(\ast)$, the sum over $s$ is $h!(\sum x^2)(\sum y^2)$.

**Which way for which $s$.** The numbers of terms are $R^{\rm row}_s=\sum_{i=0}^{2h}p(s+i)$ and $R^{\rm col}_s=\sum_{i=0}^{2h}p(2h-s-i)$. Substituting $i\mapsto2h-i$ shows that $R^{\rm col}_s=R^{\rm row}_{-s}$, and $R^{\rm row}_s$ is nondecreasing in $s$. So the column-wise form is at least as short for $s\ge0$, and the row-wise form for $s\le0$. Hence
$$\min(R^{\rm row}_s,R^{\rm col}_s)=\sum_{j=0}^{2h-|s|}p(j),\qquad K_h=\sum_{|s|\le 2h}\sum_{j=0}^{2h-|s|}p(j)=\sum_{j=0}^{2h}(4h-2j+1)p(j).$$
This proves Theorem 1, given Lemmas 4 and 5. Lemma 4(a) is used only for $s<0$.

The intuition: both factors of a term pass through one weight space, of weight $2h-s-i$ or $s+i$. Choosing the side that keeps this weight at most $2h-|s|$ keeps its dimension at most $p(2h)\approx p(h)^{\sqrt2}$.

## 4. Proofs of the lemmas

**Proof of Lemma 5.**

1. Let $b\in V_h$ and let $a$ be a monomial. In $a[-h]b$, only the terms of (47) with all $k_i>0$ survive: if some $k_i<0$, the positive ones add up to more than $h$, and the differentiations kill $b$.
2. Expand $\prod_iy_{\mu_i}=\sum_j\prod_i\binom{\mu_i}{j_i}t_{j_i}$, with $1\le j_i\le\mu_i$. Apply (47) to each monomial, listing its parts as $j_1,\dots,j_n$:
$$\Big(\prod_iy_{\mu_i}\Big)[-h]\,b=\sum_{k_i\ge1,\ \sum k_i=h}\ \prod_i\vartheta_{\mu_i}(k_i)\prod_i\nabla_{k_i}b,\qquad \vartheta_n(k)=\sum_{j=1}^n\binom{n}{n-j}\binom{-k-1}{j-1}=\binom{n-k-1}{n-1}.$$
The last equality is Vandermonde's identity, which is valid for all integer upper indices.
3. For $1\le k<n$ we have $0\le n-k-1<n-1$, so $\vartheta_n(k)=0$. Also $\vartheta_n(n)=\binom{-1}{n-1}=(-1)^{n-1}$.
4. So a nonzero term has $k_i\ge\mu_i$ for all $i$. Both sides add up to $h$, so $k_i=\mu_i$.
5. The signs cancel those in $a^\mu$, so $a^\mu[-h]b=\prod_i\nabla_{\mu_i}b$.
6. For $b=t^\nu$, the product $\prod_i\mu_i\partial_{t_{\mu_i}}t^\nu$ is zero unless $\mu\subseteq\nu$ as multisets, that is, unless $\mu=\nu$. When $\mu=\nu$ it equals $z_\mu$.

Hence $a^\mu[-h]b^\nu=\tfrac{h!}{z_\nu}z_\mu\delta_{\mu\nu}=h!\,\delta_{\mu\nu}$. $\square$

**Proof of Lemma 4.**

*Reduction to monomials.* All three statements are linear in $a$ and $b$ (since $a^{\langle i\rangle}$ is linear in $a$), so it suffices to treat monomials. Let $a=t^\mu$ with $|\mu|=h'\le h$, let $b=t^\nu$ with $|\nu|=h$, and put $H=h'+h$. Then $a^{\langle i\rangle}=\binom Hi a$. The terms of (48) with $i>H$ vanish, so (48) is a sum over $0\le i\le H$, which is what the expansion of $(\omega_1-\omega_2)^H$ below produces.

*Rings.*

- Let $\mathcal L=\mathbb Q[\omega_1^{\pm1},\omega_2^{\pm1}]$.
- Let $\mathcal L^+$ be the ring of formal series $\sum_{j\ge j_0}q_j(\omega_1)\omega_2^j$ with $q_j\in\mathbb Q[\omega_1^{\pm1}]$, and $\mathcal L^-$ the same with $\omega_1$ and $\omega_2$ exchanged.
- In $\mathcal L^\pm$, $\omega_1-\omega_2$ has the inverse $\varepsilon_+=\sum_{m\ge0}\omega_1^{-m-1}\omega_2^m$, resp. $\varepsilon_-=-\sum_{m\ge0}\omega_2^{-m-1}\omega_1^m$.
- From $(\omega_1-\omega_2)\varepsilon_\pm=1$ we get $\partial_{\omega_1}\varepsilon_\pm=-\varepsilon_\pm^2$ and $\partial_{\omega_2}\varepsilon_\pm=\varepsilon_\pm^2$.

Hence $\partial_{\omega_2}^{n-1}\varepsilon^2=n!\,\varepsilon^{n+1}$, and
$$\frac{1}{(j-1)!(n-1)!}\partial_{\omega_1}^{j-1}\partial_{\omega_2}^{n-1}\varepsilon_\pm^2=\Gamma_{j,n}\varepsilon_\pm^{j+n},\qquad \Gamma_{j,n}=(-1)^{j-1}\frac{(j+n-1)!}{(j-1)!(n-1)!}.\qquad(49)$$
$\Gamma_{j,n}$ is the same number for both signs.

*Generating functions.* For $n\ge1$ let
$$J^+_n(\omega)=\sum_{l\ge1}\binom{l-1}{n-1}\nabla_{-l}\,\omega^{l-n},\qquad J^-_n(\omega)=\sum_{k\ge1}\binom{-k-1}{n-1}\nabla_k\,\omega^{-k-n}.$$
Read (47) with $k_i=-l_i<0$ for $i$ in a set $S$ of parts, and $k_i>0$ otherwise. This gives
$$Y(t^\mu,\omega):=\sum_r t^\mu[r]\,\omega^{r-h'}=\sum_S\prod_{i\in S}J^+_{\mu_i}(\omega)\prod_{i\notin S}J^-_{\mu_i}(\omega),$$
with the creation operators to the left. Now take commuting indeterminates $z_n,z'_n$ ($n\ge1$), and put $A^\pm=\sum_nz_nJ^\pm_n(\omega_1)$ and $B^\pm=\sum_nz'_nJ^\pm_n(\omega_2)$. The $J^+$'s commute with each other, as do the $J^-$'s. Expanding the exponentials and collecting $z^\mu$ therefore gives
$$e^{A^+}e^{A^-}=\sum_\mu\frac{z^\mu}{\mu!}Y(t^\mu,\omega_1),\qquad \mu!=\prod_km_k(\mu)!.$$
The reason: the coefficient of $z^\mu$ collects the terms with $\alpha_n+\beta_n=m_n(\mu)$ factors $J^+_n$, $J^-_n$, and $1/(\alpha_n!\beta_n!)=\binom{m_n}{\alpha_n}/m_n!$. Here $\binom{m_n}{\alpha_n}$ counts the ways to choose which $\alpha_n$ of the $m_n$ parts equal to $n$ lie in $S$. The same holds for $B^\pm$ with $\omega_2$.

*Commuting the middle factors.*

- $B^+$ is multiplication by $\sum_kB_kt_k$, where $B_k=\sum_nz'_n\binom{k-1}{n-1}\omega_2^{k-n}$.
- $A^-=\sum_kA_k\nabla_k$, where $A_k=\sum_jz_j\binom{-k-1}{j-1}\omega_1^{-k-j}$.
- By Taylor's formula, on the coefficient of each power of $\omega_2$, $e^{A^-}$ acts as the ring homomorphism $t_k\mapsto t_k+kA_k$.

So $e^{A^-}e^{B^+}=e^\kappa e^{B^+}e^{A^-}$, with
$$\kappa=\sum_kkA_kB_k=\sum_{j,n}z_jz'_n\sum_{k\ge1}k\binom{-k-1}{j-1}\binom{k-1}{n-1}\omega_1^{-k-j}\omega_2^{k-n}=\sum_{j,n}z_jz'_n\Gamma_{j,n}\varepsilon_+^{j+n}\ \text{ in }\mathcal L^+.$$
The last equality holds because the inner sum is the left side of (49) applied to $\varepsilon_+^2=\partial_{\omega_2}\varepsilon_+=\sum_kk\,\omega_1^{-k-1}\omega_2^{k-1}$.

In the same way, $e^{B^-}e^{A^+}=e^{\kappa'}e^{A^+}e^{B^-}$ in $\mathcal L^-$, with $\kappa'=\sum z_jz'_n\Gamma_{j,n}\varepsilon_-^{j+n}$. This time it uses $\varepsilon_-^2=-\partial_{\omega_1}\varepsilon_-=\sum_kk\,\omega_2^{-k-1}\omega_1^{k-1}$.

Let $\mathcal N=e^{A^+}e^{B^+}e^{A^-}e^{B^-}$ be the fully normal-ordered product. Multiplications commute with each other, and so do differentiations, so
$$e^{A^+}e^{A^-}e^{B^+}e^{B^-}=e^\kappa\mathcal N\ \text{in }\mathcal L^+,\qquad e^{B^+}e^{B^-}e^{A^+}e^{A^-}=e^{\kappa'}\mathcal N\ \text{in }\mathcal L^-.\qquad(51)$$
*In which ring these identities hold.* Each side of (51), and of the two commutation rules before it, is a formal power series in the $z_n,z'_n$ whose coefficients are $\mathrm{End}(V)$-valued formal series in $\omega_1^{\pm1},\omega_2^{\pm1}$. Such a product is read as follows: fix a monomial in the $z,z'$, a power of $\omega_2$ (resp. of $\omega_1$), and two monomials $t^\sigma,t^{\sigma'}$; then $[t^\sigma](\cdots)\,t^{\sigma'}$ is a finite sum of Laurent monomials in the other variable, and an identity means that these finite sums agree for every such choice. The finiteness is the argument of [ETH, App. B]. In every product here $e^{A^+}$ stands left of $e^{A^-}$ and $e^{B^+}$ left of $e^{B^-}$. If moreover $e^{B^-}$ does not stand left of $e^{A^+}$, the result lies in $\mathcal L^+$:

1. the differentiations from $B^-$ are applied before all multiplications, so their indices add up to at most $|\sigma'|$;
2. the $\omega_2$-exponent of a term $z'_n\nabla_{-k}$ of $B^+$ is $k-n\ge0$ and grows with $k$, while those from $B^-$ are bounded by step 1, so a fixed power of $\omega_2$ leaves finitely many choices for the multiplications from $B^+$;
3. with the $z$-monomial and all weights now bounded, the indices from $A^\pm$ are bounded too.

The $\omega_2$-exponents are bounded below, so the coefficient lies in $\mathcal L^+$. Likewise the result lies in $\mathcal L^-$ (with $\omega_1,\omega_2$ exchanged) if $e^{A^-}$ does not stand left of $e^{B^+}$. In particular $\kappa$, $e^\kappa$ and both sides of the first identity in (51) are in $\mathcal L^+$, and $\kappa'$ and the second identity in $\mathcal L^-$.

*One Laurent polynomial.* Fix $\sigma,\sigma'\in\mathcal P_E$ and write $\langle X\rangle=[t^\sigma]X\,t^{\sigma'}$.

- Every coefficient $n_{\mu'',\nu''}$ of $z^{\mu''}z'^{\nu''}$ in $\langle\mathcal N\rangle$ lies in $\mathcal L$, because only $\nabla_k$ with $|k|\le E$ contribute between two weight-$E$ states. Also $n_{\emptyset,\emptyset}=\delta_{\sigma\sigma'}$.
- The coefficient of $z^{\mu'}z'^{\nu'}$ in $e^\kappa$ is $\Gamma_{\mu',\nu'}\varepsilon_+^{|\mu'|+|\nu'|}$ for a number $\Gamma_{\mu',\nu'}$, since each $z_jz'_n$ carries $\varepsilon^{j+n}$. In $e^{\kappa'}$ it is $\Gamma_{\mu',\nu'}\varepsilon_-^{|\mu'|+|\nu'|}$.

Comparing coefficients of $z^\mu z'^\nu$ in (51):
$$f_+=\langle Y(a,\omega_1)Y(b,\omega_2)\rangle,\quad f_-=\langle Y(b,\omega_2)Y(a,\omega_1)\rangle:\qquad f_\pm=\mu!\nu!\sum\Gamma_{\mu',\nu'}\varepsilon_\pm^{|\mu'|+|\nu'|}n_{\mu'',\nu''},$$
summed over the splittings $\mu=\mu'\sqcup\mu''$ and $\nu=\nu'\sqcup\nu''$. Since $|\mu'|+|\nu'|\le H$, multiplying by $(\omega_1-\omega_2)^H$ gives the same Laurent polynomial in both cases:
$$F=\mu!\nu!\sum\Gamma_{\mu',\nu'}(\omega_1-\omega_2)^{H-|\mu'|-|\nu'|}n_{\mu'',\nu''}\in\mathcal L.$$
Every term except the one with $\mu'=\mu$, $\nu'=\nu$ has a factor $\omega_1-\omega_2$, so $F(1,1)=\mu!\nu!\,\Gamma_{\mu,\nu}\,\delta_{\sigma\sigma'}$.

*Reading off.* Only weight-preserving products contribute to $\langle\cdot\rangle$. So
$$f_+=\sum_r\langle a[r]b[-r]\rangle\,\omega_1^{r-h'}\omega_2^{-r-h},$$
with no terms for $r>E$ (since $b[-r]t^{\sigma'}\in V_{E-r}$), and
$$f_-=\sum_r\langle b[-r]a[r]\rangle\,\omega_1^{r-h'}\omega_2^{-r-h},$$
with no terms for $r<-E$. Multiply by $(\omega_1-\omega_2)^H=\sum_i(-1)^i\binom Hi\omega_1^{H-i}\omega_2^i$ and collect $\omega_1^s\omega_2^{-s}$, with $r=s-h+i$:
$$F=\sum_sF_s\,\omega_1^s\omega_2^{-s},\qquad F_s=\langle Q_s(a,b)\rangle=\langle Q'_s(a,b)\rangle.$$

- **(a)** is the equality $F_s=\langle Q_s(a,b)\rangle=\langle Q'_s(a,b)\rangle$ just obtained.
- **(b)** For $s>E+h$, every $r=s-h+i\ge s-h>E$, so all terms of the first form vanish. For $s<-E-h$, every $r=s-h+i\le s-h+H=s+h'<-E$, so all terms of the second form vanish, because $a[r]t^{\sigma'}\in V_{E+r}=0$.
- **(c)** $\sum_sF_s=F(1,1)=\mu!\nu!\Gamma_{\mu,\nu}\delta_{\sigma\sigma'}$, and $\Gamma_{\mu,\nu}$ does not depend on $E$. To identify it, take $E=0$.
  - Then $\langle\mathcal N\rangle=1$: the differentiations kill $1$, and the constant term of $e^{A^+}e^{B^+}1$ is $1$.
  - So $f_+=\mu!\nu!\Gamma_{\mu,\nu}\varepsilon_+^H$, whose coefficient of $\omega_2^0$ is $\mu!\nu!\Gamma_{\mu,\nu}\omega_1^{-H}$.
  - In $f_+=\sum_r\langle a[r]b[-r]\rangle\,\omega_1^{r-h'}\omega_2^{-r-h}$, the $\omega_2^0$ term is the one with $r=-h$, namely $a[-h]\,(b[h]1)\,\omega_1^{-H}$.
  - And $b[h]1=b$. On $1$, only the terms of (47) with all $k_i=-l_i<0$ survive, with $\sum l_i=h=\sum\nu_i$. Since $\binom{l_i-1}{\nu_i-1}=0$ for $l_i<\nu_i$, we must have $l_i=\nu_i$, and the term is $t^\nu$.
  - Hence $\mu!\nu!\Gamma_{\mu,\nu}=a[-h]b$, which is (c). $\square$

**Remark 6.** For homogeneous $a$, (a) is the coefficient form of the locality of the fields $Y(a,\omega_1)$ and $Y(b,\omega_2)$ of the Heisenberg vertex algebra, $(\omega_1-\omega_2)^H[Y(a,\omega_1),Y(b,\omega_2)]=0$ [Fre, §2.1 and Prop. 2.4], [MN, Def. 1.5.1], restricted to the weight-preserving products, as [ETH, App. H] observes. A reader who knows that theory can take (a) for homogeneous $a$ from it. It does not by itself give (b), (c), or the bookkeeping for an inhomogeneous $a$ through $a^{\langle i\rangle}$. Those are proved directly above, and they are what $(\ast)$ needs.

## 5. Counting

Let $\kappa_{\rm HR}=\pi\sqrt{2/3}/\ln2\approx3.70$. By Hardy–Ramanujan, $\kappa_{\rm HR}\sqrt E-\log_2E-C\le\log_2p(E)\le\kappa_{\rm HR}\sqrt E+C$; this is the form used in [ETH, (46)]. Let $N=2^\lambda$ and let $h$ be least with $p(h)\ge N$.

- Since $p(h-1)<2^\lambda$, we get $\kappa_{\rm HR}\sqrt h\le\lambda+O(\log\lambda)$ and $h=O(\lambda^2)$.
- Since $p$ is nondecreasing, $K_h\le(2h+1)(4h+1)p(2h)$.
- $\log_2p(2h)\le\sqrt2\,\kappa_{\rm HR}\sqrt h+C\le\sqrt2\lambda+O(\log\lambda)$.

So $K_h\le N^{\sqrt2}(\log N)^{O(1)}$. Exact values, computed by `check_lemmas.py`:

| $\lambda$ | $h$ | $\log_2K_h$ | $\log_2K_h/\lambda$ |
|---:|---:|---:|---:|
| 10 | 23 | 22.7 | 2.272 |
| 20 | 61 | 38.4 | 1.922 |
| 40 | 186 | 68.9 | 1.723 |
| 60 | 372 | 98.5 | 1.641 |
| 70 | 489 | 113.2 | 1.618 |
| 80 | 620 | 127.8 | 1.598 |
| 100 | 927 | 156.9 | 1.569 |
| 200 | 3361 | 300.9 | 1.505 |
| 400 | 12663 | 586.4 | 1.466 |
| 600 | 27849 | 870.9 | 1.451 |

The exponent first drops below $1.6147$ at $\lambda=72$, and it approaches $\sqrt2$ only like $\log\lambda/\lambda$. For small $N$ the identity uses far more than $N^2$ products: $K_4=307$ for $N\le5$, and $K_5=707$ for $N\le7$. The construction is purely asymptotic.

## 6. What is checked, and where

Paths are relative to `eth/proof/rates/GeneralPieces/` of [FM]; those beginning `statements/` or `rates/` are relative to `eth/proof/`.

| Step | Lean declaration |
|---|---|
| Definition 7, Theorem B (statements) | `Pieces.Family.Is` (`statements/PiecesStatement.lean`); `AppHalfPieces.ThmHalfPiecesPure`, `LemmaQ`, `LemmaDual`, `PieceFacts` (`statements/AppHalfPiecesStatement.lean`) |
| (47): finiteness, linearity; (O1) | `GeneralPieces.opFacts` (`Ring/OpFacts.lean`); `GeneralPieces.o1` (`Ring/Op.lean`) |
| (51), the two orders | `GeneralPieces.GenF.stTwoOrders` (`GenF/Commute.lean`); `GeneralPieces.GenF.stExpansion` (`GenF/Main.lean`) |
| One Laurent polynomial $F$; $F(1,1)$; the constant | `GeneralPieces.Series.Expansion.dW_pow_mul_fP`, `…dW_pow_mul_fM`, `…ev_F` (`Series/OneLaurent.lean`); `GeneralPieces.Series.Expansion.const` (`Series/Constant.lean`) |
| Lemma 4 (a), (b), (c) | `GeneralPieces.Series.Qk_eq_Qk'_of`, `Qk_eq_zero_of`, `sum_Qk_of` (`Series/LemmaQ.lean`); assembled as `GeneralPieces.lemmaQ` (`Ring/LemmaQ.lean`) via `GeneralPieces.stBridge` (`Ring/Bridge.lean`) |
| Lemma 5; $h!/z_\mu\in\mathbb Z$ | `GeneralPieces.Dual.lemmaDual`, with `theta_eq`, `theta_of_lt`, `theta_self`; `GeneralPieces.Dual.zDvd` (`Ring/Dual.lean`) |
| $(\ast)$, (54), (55), integrality | `GeneralPieces.pieceFacts` (`Ring/Pieces.lean`); per piece `GeneralPieces.ThmHalfPieces.sum_A`, `row_A`, `col_A` (`Ring/ThmHalfPieces.lean`) |
| Counting, $h=O(\lambda^2)$ | `GeneralPieces.Bits.exists_bits_le`, `exists_hOf_le` (`Ring/Bits.lean`), which take (46) as a hypothesis; (46), with $B\log_2E$ in place of $\log_2E$, is `ClauseBound.Part.exists_bounds` (`rates/ClauseBound/Part/Bounds.lean`), used in `thmHalfPiecesPure` |
| Theorem B | `GeneralPieces.thmHalfPiecesPure` (`Ring/ThmHalfPieces.lean`), applied to `AppHalfPieces.pieceFacts` (`Main.lean`) |
| Corollary 2, bound form over $\mathbb Q$, $N=2^\lambda$ | `hurwitzSqrt2` (our `HurwitzProof.lean`) |

**Independent numerical checks.** `check_lemmas.py` is written in Python with exact integer arithmetic, from the paper's text, not from [Sie] or the Lean code. It implements (47), (48), $a^\mu$ and $b^\mu$, and checks:

- the Heisenberg relations;
- Lemma 5 for all $\mu,\nu\in\mathcal P_h$, $h\le5$;
- Lemma 4(a), (b) and (c) for $a=a^\mu$ (inhomogeneous) and $b=b^\nu$, $h\le4$, on every basis monomial of $V_E$ with $E\le4$, for $|s|\le2(E+h)+2$ (for $s>E+h$ the vanishing of $Q_s$ is immediate, but for $s<-(E+h)$, and for $Q'_s$ with $s>E+h$, it is a real cancellation; the lemma for general $a,b$ is not tested numerically);
- $(\ast)$ on all $p(h)^4$ index tuples, $h\le5$;
- both factorizations, term by term, for $h\le4$;
- the identity of Theorem 1, multiplied out as a polynomial in $2p(h)$ variables, for $h=2,\dots,5$ ($K_h=40,120,307,707$).

All 44 checks pass, in about 160 seconds on a laptop. [Sie] reports the same identity checked for $N=4$ and $N=8$ with a different implementation; we reproduced its $N=4$ case here.

**Credit and provenance.**

- J. P. Siemaszko published first, on 7 November 2026 [Sie], the observation that Theorem B of [ETH] gives $N^{\sqrt2+o(1)}$ for Hurwitz's problem. His note includes the translation to [HWY, Lemma 3.5] and instance checks.
- The construction and the proofs above are those of [ETH], re-presented.
- This note, its Lean bridge and its scripts were produced with Claude models (Anthropic) in sessions directed by the author. The author has not verified the mathematics independently of the checks described.

## References

- [ETH] Claude (Anthropic), *A $2^{o(n)}$ time algorithm for 3-SAT*, 26 Oct 2026. https://github.com/anthropics/formal-math/tree/main/eth
- [FM] `anthropics/formal-math`, `eth/`, commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
- [Fre] E. Frenkel, *Vertex algebras and algebraic curves*, Séminaire Bourbaki 1999/2000, exposé 875, Astérisque 276 (2002), 299–339; arXiv:math/0007054 (numbering cited from this version, as in [ETH]).
- [Hru] P. Hrubeš, *A subquadratic upper bound on Hurwitz's problem and related non-commutative polynomials*, ECCC TR24-099, 2024.
- [HruCCC] P. Hrubeš, *A subquadratic upper bound on sum-of-squares composition formulas*, CCC 2024, LIPIcs 300, 12:1–12:11; ECCC TR24-026 (theorem numbering as cited in [ETH, App. G]).
- [HWY] P. Hrubeš, A. Wigderson, A. Yehudayoff, *Non-commutative circuits and the sum-of-squares problem*, J. Amer. Math. Soc. 24 (2011); ECCC TR10-021.
- [MN] A. Matsuo, K. Nagatomo, *Axioms for a vertex algebra and the locality of quantum fields*, MSJ Memoirs 4, 1999.
- [Sie] J. P. Siemaszko, *An $N^{\sqrt2+o(1)}$ upper bound for Hurwitz's sum-of-squares problem from the ETH-refutation construction*, v0.5, Nov 2026, DOI 10.5281/zenodo.24024689.
