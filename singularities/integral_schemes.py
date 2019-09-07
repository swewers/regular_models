r"""
Integral schemes and arithmetic surfaces
========================================

We want to realize a category of integral schemes, which are given by
glueing affine charts corresponding to subrings of a given field.

The main example we have in mind are arithmetic surfaces over `\mathbb{Z}`.


"""

from sage.all import SageObject, Schemes, ZZ, QQ, lcm, PolynomialRing, AffineSpace
from sage.libs.singular.function import singular_function, lib as singular_lib


class SchemeFromCharts(Schemes):
    r""" A scheme over a base ring `R` which is given by a finite list of
    affine algebraic `R`-schemes and glueing morphisms.

    INPUT:

    - ``charts`` -- a nonempty list of affine `R`-schemes `U_i`, `i=1,\ldots,n`,
    - ``intersections`` -- a dictionary with keys `\{i,j\}`, where `i\neq j`,
      and entries `U_{i,j}` which are affine `R`-schemes,
    - ``glueing_maps`` -- a dictionary with keys `\{i,j\}` and entries
      `f_{i,j}:U_{i,j}\to U_i, which are open immersions of `R`-schemes,
    - ``R`` -- the base ring, a ring of finite type over a field or over `\ZZ`
      (default: ``R``=``IntegerRing``)

    """

    def __init__(self, charts, intersections, glueing_maps, R=ZZ):
        self._base_ring = R
        self._charts = charts
        self._intersections = intersections
        self._glueing_maps = glueing_maps

    def charts(self):
        return self._charts


class PointOnSchemeFromCharts(SageObject):
    r""" Return the point on a scheme with given equations.

    INPUT:

    - ``X`` -- a scheme, object of ``SchemeFromCharts``
    - ``equations`` -- a list of polynomials
    - ``chart`` -- the key designating a chart of `X`, or ``None`` (default: ``None``)

    OUTPUT: the point on `X` given by the equations.

    More precisely, ``equations`` is a list of polynomials defined on the
    ambient space of the chart `U={\rm Spec}(A)`. They define a closed subscheme
    of `U`, which we assume to be irreducible. We return the generic point of
    this subscheme.

    If ``chart`` is ``None`` then we take the standard chart.

    """

    def __init__(self, X, equations, chart=None):
        pass

    def __repr__(self):
        pass

    def ambient_scheme(self):
        pass

    def chart(self):
        pass

    def ideal(self):
        pass

    def is_equal(self, P):
        pass

    def residue_field(self):
        pass


"""------------------------------------------------------------------------------
"""


class IntegralScheme(SchemeFromCharts):
    r""" An integral scheme over a ring `R`, given by a finite number of
    affine charts, which correspond to finitely generated `R`-algebras
    contained in a finitely generated field `F`.

    INPUT:

    - ``R`` -- an integral domain
    - ``F`` -- a field which is finitely generated over the fraction field of `R`
    - ``chart_list`` -- a list of lists containing elements of F

    OUTPUT:

    An integral scheme `X` of finite type over `R` with fraction field `F`.

    Let ``chart_list`` consist of tupels `(f_{i_1},\ldots,f_{i,r_i})` of
    elements of `F`, indexed by `i`. Then the scheme `X` is the union of affine
    schemes `U_i={\rm Spec}(A_i)`, where `A_i` is the `R`-subalgebra of `F`
    generated  by the elements `f_{i,j}`.

    .. Note::

    It is assumed and not tested whether the affine schemes `U_i` can be glued
    to a scheme `X`.

    """

    def __init__(self, R, F, chart_list):
        assert R.has_coercion(F), "the base ring R must be a subring of F"
        self._base_ring = R
        self._function_field = F
        charts = []
        for generators in charts:
            U = AffineIntegralScheme(R, F, generators)
            charts.append(U)
        n = len(charts)
        intersections = {}
        glueing_maps = {}
        for i in range(n):
            U_i = charts[i]
            for j in range(i + 1, n):
                generators = chart_list[i] + chart_list[j]
                U_j = charts[j]
                i_j = set([i, j])
                U_i_j = AffineIntegralScheme(R, F, generators)
                intersections[i_j] = U_i_j
                glueing_maps[(i, j)] = U_i_j.map_to(U_i)
                glueing_maps[(j, i)] = U_i_j.map_to(U_j)
        self._chart = charts
        self._intersections = intersections
        self._glueing_maps = glueing_maps


"""---------------------------------------------------------------------------

                   affine integral schemes
                   =======================
"""


def AffineIntegralScheme(R, F, generators):
    r""" Return an integral affine scheme with given base ring and function field.

    INPUT:

    - ``R`` -- an integral domain
    - ``F`` -- a field, finitely generated over the fraction field of `R`
    - ``generators`` -- a list of elements of `F`

    OUTPUT: an affine `R`-scheme `X` with function field `F`, whose coordinate
    ring is generated over `R` by the given generators.

    `X` will be equipped with attributes ``_function_field`` (which returns `F`)
    and ``_generators`` (which returns the list of generators defining `X`).

    .. NOTE::

    At the moment, we assume that `F` is a function field of transcendence degree
    one over the fraction field of `R`, and that the defining equation for
    `F` has coefficients in `R`. In particula, the scheme `X` will be an affine
    arithmetic surface.

    """
    # first we create the ideal defining X
    n = len(generators)
    P = AffineSpace(R, n, 'x')
    A = P.coordinate_ring()
    if hasattr(F, "polynomial"):
        # F is a function field over Frac(R) in two variables x, y
        # with equation G0(x,y)=0. Write the generators as
        # f_i =g_i(x,y)/h_i(x,y) and define the ideal generated by
        # G0 and h_i(x,y)*z_i - g_i(x,y). We obtain the ideal defining
        # X by eliminating x, y from these equations.
        B = PolynomialRing(R, n + 2, 'z')
        x = B.gens()[n]
        y = B.gens()[n + 1]
        G0 = function_field_equation(R, F)(x, y)
        G = [G0]
        for i in range(n):
            f = generators[i]
            # we have to write f = g/h, where g, h are elements of B
            g, h = function_field_element(f, R)
            g = g(x, y)
            h = h(x, y)
            G.append(h * B.gens()[i] - g)
        J = B.ideal(G).elimination_ideal([x, y])
        # in general, this is not a prime ideal; we have to first
        # replace it by its radical. Probably we need to write a
        # Singular script for this
        G = []
        for g in J.gens():
            G.append(g(A.gens() + (A.zero(), A.zero())))
    else:
        # F is a rational function field over Frac(R)
        B = PolynomialRing(R, n + 1, 'z')
        x = B.gens()[n]
        G = []
        for i in range(n):
            f = generators[i]
            g = f.numerator()
            a = common_denominator_of_polynomial(g, R)
            h = f.denominator()
            b = common_denominator_of_polynomial(h, R)
            c = lcm(a, b)
            g = c * g
            h = c * h
            G.append(h(x) * B.gens()[i] - g(x))
        J = B.ideal(G).elimination_ideal([x])
        G = []
        for g in J.gens():
            G.append(g(A.gens() + tuple([A.zero()])))
    J_list = horizontal_minimal_ass_primes(A.ideal(G))
    assert len(J_list) == 1, "some thing strange happened: there is more than one horizontal pime ideal"
    X = P.subscheme(J_list[0])
    X._function_field = F
    X._generators = generators
    return X


def HomOfAffineIntegralSchemes(X, Y):
    r""" Return the natural morphism between to affine integral schemes.

    INPUT:

    - ``X``, ``Y`` -- two affine integral schemes

    OUTPUT: the natural homomorphism `\phi:X\to Y`.

    It is assumed that `F_Y`, the function field of `Y`, coerces into `F_X`,
    the function field of `X`. Then `\phi` exists (and is unique) if and only
    if the coordinate ring of `Y` is contained in the coordinate ring of `X`,
    as subrings of `F_X`.

"""

    pass


"""-----------------------------------------------------------------------------

                          auxiliary functions
                          ===================
"""


def denominator_wrt_order(a, R):
    r""" Return a denominator of a field element  w.r.t an order.

    INPUT:

    - ``a`` -- an element of a field `K`
    - ``R`` -- an order of `K`

    OUTPUT: an element `b` of `R` such that `ab` lies in `R`.

    .. NOTE::

    At the moment this is implemented only for `K=\mathbb{Q}` and `R=\mathbb{Z}`.

    """
    if R is not ZZ:
        raise NotImplementedError
    if a not in QQ:
        raise NotImplementedError
    return a.denominator()


def common_denominator_of_polynomial(g, R):
    r""" Return the lcm of the denominators of the coefficients of this polynomial.

    INPUT:

    - ``g`` -- an univariat polynomial over a field `K`
    - ``R`` -- an order of `K`

    OUTPUT: the lcm of the denominators of the coefficients of `g` with
    respect to `R`. It is never zero.

    """
    return lcm([denominator_wrt_order(g[i], R) for i in range(g.degree() + 1) if not g[i].is_zero()])


def num_denom_for_rational_function_field(f, R):
    r""" Return the numerator and denominator of a function field element.

    INPUT:

    - ``f`` -- an element of a rational function field over a field `K`
    - ``R`` -- an order in K

    OUTPUT: a pair `g, h` of univariate polynomials over `R` such that
    `f = g/h`.

    """
    # F = f.parent()
    # A = F._ring     It seems I don't need these lines
    B = PolynomialRing(R, 'x')
    g = f.numerator()
    a = common_denominator_of_polynomial(g, R)
    h = f.denominator()
    b = common_denominator_of_polynomial(g, R)
    c = lcm(a, b)
    return B(c * g), B(c * h)


def function_field_equation(R, F):
    r""" Return the equation defining a function field.

    INPUT:

    - ``R`` -- an integral domain
    - ``F`` -- a function field, defined as a simple finite extension of a
      rational function field over the fraction field `K` of `R`

    OUTPUT: a polynomial `G` over `R` in two variables such that
    `F = K(x, y | G(x,y)=0)`.

    """
    G = F.polynomial()
    # G should be an univariat polynomial over a rational function field F0
    F0 = G.parent().base_ring()
    A0 = F0._ring()
    # A0 is a polynomial ring over K, the fraction field of R
    K = A0.base_ring()
    assert R.fraction_field() == K, "K must be the fraction field of R"
    coeffs = [G[i] for i in range(G.degree() + 1)]
    a = lcm([c.denominator() for c in coeffs if not c.is_zero()])
    coeffs = [(a * c).numerator() for c in coeffs]
    # now coeffs is a list of univariat polynomials over a field
    common_denominator = R.one()
    for c in coeffs:
        common_denominator = lcm([c[i].denominator() for i in range(c.degree() + 1) if not c[i].is_zero()] + [common_denominator])
    B = PolynomialRing(R, 2, ['x', 'y'])
    x = B.gens()[0]
    y = B.gens()[1]
    coeffs = [(common_denominator * c)(x) for c in coeffs]
    return sum([coeffs[i] * y**i for i in range(len(coeffs))])


def function_field_element(f, R):
    r""" Return the numerator and denominator of a function field element.

    INPUT:

    - ``f`` -- an element of a function field `F`, which is a finite extension
      of a rational function field `F_0` over a field `K`
    - ``R`` -- an order of `K`

    OUTPUT: a pair `g, h` of polynomials over `R` in two variables `x, y` such
    that f = g/h (if we map `x` to the generator of `F_0` and `y` to the
    generator of `F/F_0`.

    """
    F = f.parent()
    if hasattr(F, "polynomial"):
        # F0 = F.base_field()
        # A0 = F0._ring
        f = f.element()
        n = f.degree()
        # now f is an univariant polynomial over F0
        h = lcm([f[i].denominator() for i in range(n + 1)])
        g = h * f
        a = lcm([common_denominator_of_polynomial(g[i].numerator(), ZZ) for i in range(n + 1) if not g[i].is_zero()])
        b = common_denominator_of_polynomial(h, R)
        c = lcm(a, b)
        g = c * g
        h = c * h
        B = PolynomialRing(R, 2, ['x', 'y'])
        x = B.gens()[0]
        y = B.gens()[1]
        g = sum([g[i].numerator()(x) * y**i for i in range(g.degree() + 1)])
        h = h(x)
        return g, h
    else:
        # f seems to constant in y
        g = f.numerator()
        h = f.denominator()
        a = common_denominator_of_polynomial(g, R)
        b = common_denominator_of_polynomial(h, R)
        c = lcm(a, b)
        g = c * g
        h = c * h
        B = PolynomialRing(R, 2, ['x', 'y'])
        x = B.gens()[0]
        return g(x), h(x)


"""                       help from Singular
                          ==================

"""


def radical_singular(I):
    r""" Return the radical of this ideal.

    INPUT:

    - ``I`` -- an ideal of a polynomial ring over `\mathbb{Z}`

    OUTPUT: the radical of `I`

    """
    singular_lib('primdecint.lib')
    return singular_function('radicalZ')(I)


def minimal_ass_primes_singular(I):
    r""" Return the list of minimal associated primes of an ideal.

    INPUT:

    - ``I`` -- an ideal of a polynomial ring over `\mathbb{Z}`

    OUTPUT: the list of all minimal associated prime ideals of `I`

    """
    singular_lib('primdecint.lib')
    R = I.ring()
    return [R.ideal(G) for G in singular_function('minAssZ')(I)]


def horizontal_minimal_ass_primes(I):
    r""" Return the list of horizontal minimal associated primes of I.

    INPUT:

    - ``I`` -- an ideal of a polynomial ring over `\mathbb{Z}`

    OUTPUT: the list of all horizontal minimal associated prime ideals of `I`.
    Here a prime ideal `P` of a polynomial ring `R = \mathbb{Z}[x_1,\ldots,x_n]`
    is called *horizontal* if `P\cap\mathbb{Z}=(0)`.

    """
    singular_lib('primdecint.lib')
    R = I.ring()
    P_list = [R.ideal(G) for G in singular_function('minAssZ')(I)]
    return [P for P in P_list if P.elimination_ideal(R.gens()).is_zero()]
