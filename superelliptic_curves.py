
r"""
Computing an integral basis of differential forms for superelliptic curves
==========================================================================

In this module we implement the algorithm described in Section 4 of our preprint

.. [KunzweilerWewers20] S. Kunzweiler and S. Wewers, Integral differential forms
for superelliptic curves.

Let `Y_K` be a superelliptic curve which is birationally defined by an affine equation
Given a superelliptic curve defined over some local field `K` by an equation of the form

..MATH::

    y^n = f(x),

the algorithm computes the lattice of integral differentials `M` for `Y_K`.
By definition

..MATH::

    M = H^0(Y,\oomega_{Y/S}),

where `Y` is a model of `Y_K` with at most rational singularities (e.g. a regular model)
and `S` is the spectrum of the ring of integers of `K`.
Note that `M` is a lattice in the vector space `M_K` of differential forms of `Y_K`.
In this implementation, we view `M_K` as a subspace of the function space of `Y_K`
via the embedding `\omega \mapsto \omega / \eta`, where `eta = dx/y^{n-1}`.




AUTHORS:

- Sabrina Kunzweiler (2019): initial version


EXAMPLES::

    sage: from regular_models.superelliptic_curves import integral_differentials

We can compute the lattice of integral differentials for hyperelliptic curves defined
over a discretely valued field with odd residue characteristic. ::

    sage: R.<x> = QQ[]
    sage: f = ((x-1)^2 - 5^3) * (x^3 + 3^7)
    sage: v_3 = QQ.valuation(3)
    sage: integral_differentials(f,2,v_3)
    the lattice with basis [x, 3]
    sage: v_5 = QQ.valuation(5)
    sage: integral_differentials(f, 2, v_5)
    the lattice with basis [-x + 1, x]
    sage: v_2 = QQ.valuation(2)
    sage: integral_differentials(f,2,v_2)
    AssertionError
    ...
    AssertionError: n must not divide the residue characteristic of K


It is also possible to compute the integral differentials for superelliptic curves
`y^n = f(x)`, as long as the residue characteristic does not divide `n`.
The following is Example 5.2. in the preprint [KunzweilerWewers20]. ::

    sage: v_2 = QQ.valuation(2)
    sage: f = (x^3 - 2^4)*((x+2)^2 + 2^3)*((x+2)^2 - 2^3)
    sage: M = integral_differentials(f,3,v_2); M
    the lattice with basis [x^3 - 4*x, x*y - 16, 2*y - 16, 4*x^2 - 16, 8*x - 16, 16]

The lattice M lives in a Riemann-Roch space. For some applications (for example
the numerical verification of the BSD conjecture), one is interested in
the covolume of this lattice in the underlying Riemann-Roch space.
It is possible to compute this covolume w.r.t. some (specified) rational basis of `M_K`. ::

    sage: MK = M.RR_space()
    sage: B0 = MK.rational_basis(); B0
    [1, x, x^2, x^3, y, x*y]
    sage: cov = (Matrix([MK.function_space().vector(g) for g in M.basis()])).determinant()
    sage: v_2(cov)
    10

This means that `\det(M) = \langle 2^{10} * 1 \land x \land x^2 \land x^3 \land y \land xy \rangle`.


The exponent of the superelliptic curve need not be prime for our algorithm to work.  ::

    sage: f =  (x^2 + 3^4) * ((x-1)^2 - 3^3)
    sage: integral_differentials(f,4,v_3)
    the lattice with basis [y, x, 3]
    sage: integral_differentials(f,6,v_5)
    the lattice with basis [1, y, y^2, y^3, x, x*y, x^2]


Nevertheless, some instances with n a composite number do not work in the implementation
(due to a known bug in Sage).

    sage: f = x^5-5^2
    sage: integral_differentials(f,4,v_5) # known bug
    Traceback (most recent call last):
    ...
    NotImplementedError:

"""


# *****************************************************************************
#       Copyright (C) 2019 Sabrina Kunzweiler <sabrina.kunzweiler@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# *****************************************************************************


def defining_system(xi):
    r""" Returns a defining system for the component corresponding to `\xi`.

    INPUT:

    - ``xi`` -- a point of type II on the Berkovich line

    OUTPUT: A list `(F,u,t)`where  `(u,t)` is a defining system for the component
    and `F` is the defining polynomial in the sense of [KunzweilerWewers20]

    EXAMPLE:

        sage: from mclf import *
        sage: from regular_models.superelliptic_curves import defining_system
        sage: v_2 = QQ.valuation(2)
        sage: F.<x> = FunctionField(QQ)
        sage: X = BerkovichLine(F, v_2)
        sage: xi = X.point_from_discoid(x^4+2*x^2+2, 10)
        sage: [F,u,t] = defining_system(xi); [F,u,t]
        [T1^4 + 2*T1^2 - 1024*T2 + 2, x, 1/1024*x^4 + 1/512*x^2 + 1/512]

        We can test some of the properties of a defining system.

        sage: xi.v(u)
        1/4
        sage: xi.v(t)
        0
        sage: F(u,t) == 0
        True

    """

    v = xi.pseudovaluation_on_polynomial_ring()
    K = v.phi().base_ring()
    x = v.phi().variables()[0]
    u = v.uniformizer()
    t = v.lift(v.residue_ring().gen())
    B = K['U, T, x']
    U, T, x = B.gens()
    J = B.ideal(B(u) - U, B(t) - T)
    F = J.elimination_ideal([x]).gens()[0]
    A = K['T1,T2']
    T1, T2 = A.gens()
    return [A(F(T1,T2,1)), u, t]


def ord_dx(xi):
    r"""
    Returns the order of vanishing of `dx` along the component with generic point `\xi`.

    INPUT:
    - ``xi`` -- a point of type II on the Berkovich line

    OUTPUT: Assume`\xi`is a point on the Berkovich line with function field K(x).
    Then the algorithm returns the the order of vanishing of `dx` along a component
    with generic point `\xi`.
    """
    v = xi.pseudovaluation_on_polynomial_ring()
    [F, u, t] = defining_system(xi)
    # canoncial sheaf on U is generated by `dt/F_u`, where `F_u` is the derivative of `F`
    # with respect to `u`. By definition, `F_u` nonzero.
    # So the order of `dx = dt/t_x` is given by `v(F_u(u,t)) - v(t_x)`
    t_x = t.derivative()
    #R = F.parent()
    U, T = F.parent().gens()
    F_u = F.derivative(U)
    return v(F_u(u, t)) - v(t_x)


def integral_differentials(f, n, v_K):
    r"""
    Returns the lattice of integral differentials of the superelliptic curve Y
    defined by y^n = f(x) over K

    INPUT:

    - ``f`` - a monic, integral and separable polynomial of degree at least 3 over some field `K`
    - ``n`` - an integer not dividing the residue characteristic of K
    - ``v_K`` - a discrete valuation on `K`

    OUTPUT: The output is an O_K lattice in the Riemann-Roch space of differential forms
    of the superelliptic curve `Y`.
    The differential forms are viewed as elements in the function field `K(Y)` under the
    embedding `\omega \mapsto \omega y^{n-1}/dx`.

    EXAMPLE:

        sage: from regular_models.superelliptic_curves import integral_differentials
        sage: v_2 = QQ.valuation(2)
        sage: R.<x> = QQ[]
        sage: f = (x^3-2^4)*((x+2)^2+2^3)*((x+2)^2-2^3)
        sage: integral_differentials(f,3,v_2)
        the lattice with basis [x^3 - 4*x, x*y - 16, 2*y - 16, 4*x^2 - 16, 8*x - 16, 16]

    """
    from regular_models.models_of_projective_line import minimal_rnc_model
    from regular_models.RR_spaces.RR_lattices import RRSpace
    from sage.rings.integer import Integer
    from sage.schemes.riemann_surfaces.riemann_surface import differential_basis_baker

    assert v_K(n) == 0, "n must not divide the residue characteristic of K"
    assert v_K.domain() is f.base_ring(), "v_K must be a valuation on the base ring of f"

    S = f.base_ring()['x, y']
    x, y = S.gens()
    G = y**n-f(x)

    X = minimal_rnc_model(f, v_K)
    F0 = X.function_field()
    R = F0['y']
    y, = R.gens()
    F = F0.extension(y**n - F0(f), names=('y',))
    y, = F.gens()

    B = [F(b) for b in differential_basis_baker(G)]
    M_K = RRSpace(v_K, F, B)
    m = []
    i = Integer(0)
    for E in X.vertical_components():
        xi = E.generic_point()
        v = xi.pseudovaluation_on_polynomial_ring()
        v0 = F0.valuation(v)
        w0 = v0.extensions(F)[0]
        M_K.add_valuation(w0, "w{0}".format(i))
        if v(v.phi()) == 0:
            mv = Integer(0)
        else:
            # mv is the order of vanishing `\eta = dx/y^{n-1}` along the component E
            e = w0.value_group().index(v0.value_group())
            mv = ord_dx(xi) - w0(y) * (n - 1) + e - 1
        m.append(("w{0}".format(i), -mv))
        i += 1
    return M_K.RR_lattice(m)