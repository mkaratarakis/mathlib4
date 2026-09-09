# Eisenstein–Dumas densities and Heilbronn's criterion — design

Source: A. Hibbler, K. J. McGown, E. Treviño, *Polynomial densities and Heilbronn's
criterion*, arXiv:2512.16220.  Goal: formalize with **zero new definitions**, generalize
substantively, then emit a stand-alone paper.

## 0. The generalization axes

1. **Eisenstein → Eisenstein–Dumas.** Newton polygon a single segment of slope −m/n,
   gcd(m,n)=1.  Hypothesis-style (no ceilings, no new defs): exponents `c : ℕ → ℕ` with
   `m * (n - i) ≤ n * c i`, `(p:ℤ)^(c i) ∣ a i` for `i < n`, and `¬ (p:ℤ)^(m+1) ∣ a 0`
   together with `c 0 = m`.  (m = 1 recovers Eisenstein.)
2. **Heilbronn's criterion, embedding-free.** Replace the conjugate/Galois-closure step by
   a general algebra lemma (see §2): the norm of a finite free algebra reduces to the n-th
   power on a totally ramified residue field.
3. **Master counting lemma** with *one modulus per coefficient* and an arbitrary set of
   local conditions; sharp two-sided sandwich instead of O-notation, hence exact densities.
4. **Master density theorem** parametrized by a finite set Q of auxiliary primes; the
   paper's 2/27 (Q = {2,3}) and 1 − ε(p) (Q = all primes ≤ p^{1/4}) are both corollaries,
   and intermediate Q give strictly better bounds for moderate p.
5. Rootless-polynomial counts over an arbitrary finite field, and w.r.t. an arbitrary
   subset of forbidden roots.

## 1. Eisenstein–Dumas ⟹ irreducible and totally ramified   (generalizes Lemma 2.1)

Let f = X^n + Σ_{i<n} a_i X^i, θ a root, K = ℚ(θ), d = [K:ℚ] ≤ n, P a maximal ideal of
𝒪_K over p, e = v_P(p), w = v_P(θ) ≥ 0 (θ is an algebraic integer).

Claim: **n·w = e·m**.
* v_P(a_0) = e·m exactly;  v_P(a_i θ^i) ≥ e·c_i + i·w ≥ e·m(n−i)/n + i·w.
* If n w > e m then every i ≥ 1 term has valuation > e m, so v_P(Σ) = v_P(a_0) = e m = n w,
  contradiction.
* If n w < e m then n w ≥ min ≥ min(e m, e m/n + (n−1) w) forces w ≥ e m/n, contradiction.

Hence n | e·m, gcd(m,n) = 1 ⟹ n | e, and e ≤ Σ e_i f_i = d ≤ n forces **e = n = d**:
irreducibility of f *and* total ramification come out of the same computation, and w = m.
(The classical Eisenstein–Dumas criterion is the `d = n` half.)

## 2. Heilbronn's criterion — the embedding-free proof

**Key lemma (new, general).** A comm. ring, B a finite free A-algebra of rank n, 𝔮 ⊆ A a
radical ideal, I ⊆ B an ideal with I^n ≤ 𝔮·B.  If ρ ∈ B, x ∈ A and ρ − x ∈ I then
N_{B/A}(ρ) ≡ x^n (mod 𝔮).
*Proof.* Mod 𝔮 the multiplication operator T of ρ − x is nilpotent (T^n ∈ 𝔮B), so its
characteristic polynomial is X^n (charpoly of a nilpotent matrix over a reduced ring);
N(ρ) = det(x·1 + T) = (−1)^n charpoly(−T)(−x) ≡ x^n.  ∎
No embeddings, no Galois closure — this replaces the paper's "x ≡ ρ^σ (mod π)" step, which
is only literally meaningful in a Galois closure.

**Criterion.** K a number field of degree n, 𝔭^n = (p) in 𝒪_K, p = a + b with a,b > 0,
x^n ≡ a (mod p), and neither a nor −b a norm from 𝒪_K.  Then K is not norm-Euclidean.
*Proof.* If it were, minimality of |N| on 𝔭 makes 𝔭 = (π) with |N π| = p; divide x by π:
x = γπ + ρ, |N ρ| < p; ρ − x ∈ 𝔭 and 𝔭^n = (p) give N ρ ≡ x^n ≡ a (mod p); with
0 < a < p and |N ρ| < p this forces N ρ ∈ {a, a − p} = {a, −b}.  ∎

## 3. Degree-one primes and norms   (corrects Lemma 2.3)

The paper's Lemma 2.3 ("q a norm ⟹ f has a root mod q") is **not sufficient** for its own
application: Heilbronn needs `a = u q₁` (with q₁ ∤ u) to be a non-norm, not merely q₁.
The statement that is needed, and that we prove:

> If f has no root in 𝔽_q then no prime of 𝒪_K above q has residue degree 1, and hence
> v_q(N α) ≠ 1 for every α ∈ 𝒪_K.  In particular u·q is never a norm when q ∤ u.

(Proof: N(α) = Π_{𝔮 | (α)} q_𝔮^{f_𝔮 e_𝔮}; v_q = Σ_{𝔮 | q} f_𝔮 e_𝔮 = 1 forces some 𝔮 | q with
f_𝔮 = 1, whose residue field 𝔽_q receives θ as a root of f.)
Bonus: the sign is irrelevant, so the paper's parity trick ("n odd ⟹ b norm iff −b norm")
is not needed; `n` odd is then forced by gcd(p−1,n) = 1 rather than assumed.

## 4. Master counting lemma   (generalizes Lemma 3.1 / Prop 3.3)

For a finite index type ι, moduli M : ι → ℕ (M i ≥ 1) and S ⊆ Π i, ZMod (M i):
  #{a : ι → ℤ | ∀ i, |a i| ≤ X, (fun i ↦ (a i : ZMod (M i))) ∈ S}
    = Σ_{s ∈ S} Π_i #{t : |t| ≤ X, t ≡ s i}, and each factor is (2X+1)/M i + O(1);
hence the sandwich |S|·Π((2X+1)/M i − 1) ≤ count ≤ |S|·Π((2X+1)/M i + 1) and the exact
density  count/(2X+1)^{|ι|} → |S| / Π M i.
Different moduli per coordinate is exactly what Eisenstein–Dumas needs (a_0 mod p^{m+1},
a_i mod p^{c_i}), and it makes Prop 3.3 a one-line instantiation.

## 5. Local densities

**Eisenstein–Dumas density.** With S(m,n) := Σ_{j=1}^{n} ⌈m j/n⌉ = (m+1)(n+1)/2 − 1
(gcd(m,n) = 1), the density of degree-n monic polynomials satisfying Eisenstein–Dumas at p
with slope m/n is
        E_{p,m}(n) = (1 − 1/p) · p^{−S(m,n)} = p^{−S} − p^{−S−1}.
m = 1 gives S = n and recovers Dubickas' p^{−n} − p^{−n−1}.

**Rootless counts (Lemma 4.1/4.2).** Over a finite field F with |F| = Q, the number of
monic degree-n polynomials with no root in a subset T ⊆ F is Σ_k (−1)^k C(|T|,k) Q^{n−k};
for T = F and n ≥ Q it collapses to (1 − 1/Q)^Q Q^n.  Bounds
1/4 ≤ (Q²−1)/(3Q²) ≤ C_Q(n) ≤ (Q−1)/(2Q) < 1/2.
NB the paper's proof of Lemma 4.2 argues that f(k) = C(p,k)/p^k is decreasing because
f(k)/f(k+1) = (k+1)p/(p−k) > 0; positivity of a ratio does not give monotonicity, and in
fact f(0) = f(1).  Correct version: the ratio is ≥ 1, with strict inequality for k ≥ 1.

## 6. Master density theorem

Let n ≥ 2, p prime with gcd(p−1,n) = 1, m ≥ 1 with gcd(m,n) = 1, and let Q be a finite set
of primes ≠ p such that q₁²q₂² ≤ p for all pairs q₁ < q₂ in Q.  Then among the monic
degree-n integer polynomials that are Eisenstein–Dumas at p of slope m/n, the sub-family of
those f for which f has no root mod q for at least two q ∈ Q has density exactly
      Σ_{T ⊆ Q, |T| ≥ 2} Π_{q ∈ T} C_q(n) · Π_{q ∈ Q∖T} (1 − C_q(n)),
and every such f generates a field that is not norm-Euclidean.  Corollaries:
* Q = {2,3}, p ≥ 36, n ≥ 3: bound C_2 C_3 = 2/27.  (p ∈ {7,11,19}: Q = {2,5}, ≥ 2/25.)
* Q = {q ≤ p^{1/4}}: bound ≥ 1 − (1 + π(p^{1/4}))(3/4)^{π(p^{1/4})} → 1.
* Q = {2,3,5}, p ≥ 225: bound ≥ 0.244, far better than 2/27 in the middle range.

## 7. Weakening gcd(p−1,n) = 1

Pólya–Vinogradov is not in Mathlib; the second theorem is formalized *conditionally* on an
explicit character-sum hypothesis (which is exactly how the source paper uses it: quoted
from the literature).  Everything else in that proof (the character detectors, the shifting
trick for q₂ | v, the choice Y = (log p)^{1/4}) is proved.
