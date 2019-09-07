r"""         Monomial valuations
             ===================

"""

from sage.all import SageObject, PolynomialRing, Infinity


class MonomialValuation(SageObject):
    r""" Return a monomial valuation.

    INPUT:

    - ``R`` -- a polynomial ring `K[x_1,\ldots,x_n]` over a field `K`
    - ``I`` -- a prime ideal of `R`
    - ``v_K`` -- a discrete valuation on `K`
    - ``w`` -- a weight vector `(w_1,w_2,\ldots,w_n)\in\mathbb{Q}^n`

    OUTPUT: the monomial pseudo-valuation `v` on `R` characterized by
        - `v|_K = v_K`,
        - `I = \{ f \in R \mid v(f) = \infty \}`,
        - `v(x_i) = w_i, \quad i=1,\ldots,n`.
    We must assume that no `x_i` is contained in `I`. To define `v`, let
    `v_0` denote the valuation on `R` defined by

    .. MATH::

        v_0(\sum_i c_i x^i) := \min_i v_K(c_i) + w\cdot i.

    Then for `f\in R` we have

    .. MATH::

        v(f) := \max \{ v_0(g) \mid f \equiv g \pmod{I} \}.

    """
    def __init__(self, R, I, v_K, w):
        assert R.base_ring() == v_K.domain(), "the base field of R must be the domain of v_K"
        assert len(R.gens()) == len(w), "the length of w must be equal to the number of variables"
        v_K = v_K / v_K(v_K.uniformizer())
        self._R = R
        self._I = I
        self._v_K = v_K
        self._w = w
        self._Rb = PolynomialRing(v_K.residue_field(), R.variable_names())

    def __repr__(self):
        return "the monomial valuation on {} with kernel {} and weights {}".format(
            self._R, self._I, self._w)

    def __call__(self, f):
        r""" Return the valuation of `f`.

        INPUT:

        - ``f`` -- an element of the polynomial ring `K[x]`

        OUTPUT: the valuation `v(f)`; it is defined as `v(f):=v_0(f_0)`, where
        `f_0` is the *normal form* of `f`, i.e. an element of `K[x]` such that
        `f \equiv f_0 \pmod{I}` and `v_0(f_0)` is maximal.

        """
        return self.v_0(self.normal_form(f))

    def domain(self):
        return self._R

    def kernel(self):
        return self._I

    def base_valuation(self):
        return self._v_K

    def weight_vector(self):
        return self._w

    def residue_polynomial_ring(self):
        return self._Rb

    def normalized_reduction(self, c):
        r""" Return the normalized reduction of `c`.

        INPUT:

        - ``c`` -- a nonzero element of the base field `K`

        OUTPUT: the reduction of `c\cdot \pi^{-v_K(c)}` with respect to `v_K`.
        Here `\pi` is the canonical uniformizer of `v_K`. If `c = 0`, an error
        is raised.

        """
        assert not c.is_zero(), "c must be nonzero"
        v_K = self.base_valuation()
        pi = v_K.uniformizer()
        return v_K.reduce(c / pi**(v_K(c)))

    def in_w(self, f):
        r""" Return the initial term of `f` with respect to `v_K` and `w`.

        INPUT:

        - ``f`` -- an element of the domain, the polynomial ring `K[x]`

        OUTPUT: the initial term of `f` with respect to the base valuation `v_K`
        and the weight vector `w`; if `f = \sum_i c_i x^i`, and
        `\mu = v_0(f) = \min v_K(c_i) + w\cdot i`, then

        .. MATH::

            {\rm in}_w(f) = (\sum_{v_K(c_i) + w\cdot i = \mu} [c_i] x^i, \mu)

        Here `k` denotes the residue field of `v_K` and for an element `c\in K`,
        `[c]\in k` denotes the *normalized reduction* of `c` (with respect to
        a fixed uniformizer of `v_K`. So `{\rm in}_w(f) = (\bar{f}, N)`, where
        `\bar{f} \in k[x]` is a polynomial over `k` and `N` is a rational number,
        which is equal to `v_0(f)`.

        """
        v_K = self.base_valuation()
        Rb = self.residue_polynomial_ring()
        w = self.weight_vector()
        fb = Rb.zero()
        mu = Infinity
        for m in f.monomials():
            c = f.monomial_coefficient(m)
            i = m.degrees()
            nu = v_K(c) + sum([w[j] * i[j] for j in range(len(w))])
            if nu == mu:
                fb = fb + self.normalized_reduction(c) * Rb(m)
            elif nu < mu:
                fb = self.normalized_reduction(c) * Rb(m)
                mu = nu
        return fb, mu

    def v0(self, f):
        return self._LT(f)[1]

    def in_initial_ideal(self, fb):
        r""" Return, if possible, an element of `I` with given initial term.

        INPUT:

        - ``fb`` -- an element of the polynomial ring `k[x]`

        OUTPUT: an element `f\in I` with leading term `\bar{f}`, if this exists;
        otherwise return ``None``.

        """
        I = self.kernel()
        Ib = self.initial_ideal()
        if fb in Ib:
            gb = fb.lift(Ib)
            return sum([self._lift(gb[i]) * I.gens()[i] for i in range(len(gb))])
        else:
            return None

    def normal_form(self, f):
        r""" Return the normal form of `f` w.r.t. `v_0` and `I`.

        INPUT:

        - ``f`` -- an element of the polynomial ring `K[x]`

        OUTPUT: an element `f_0\in K[x]` such that `f \equiv f_0\pmod{I}` and
        such that `v_0(f_0)` is maximal.

        """
        R = self.polynomial_ring()
        f0 = f
        g = R.zero()
        while True:
            fb0, mu = self.in_w(f0)
            h = self.in_initial_ideal(fb0)
            if h:
                f0 = f0 - h
                g = g + h
            else:
                return f0
