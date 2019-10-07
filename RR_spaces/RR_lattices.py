r"""
Riemann-Roch Lattices
=====================

Let `K` be a field equipped with a discrete valuation `v_K` and let `R` denote
the valuation ring of `v_K`. Let us also fix a field extension `F/K`. Although
this is not necessarily the case, one should think of `F` as the function field
of a smooth projective curve over `K`.

Let `M_K\subset F` be a finitely generated `K`-vector subspace of dimension `n`.
Then for any extension `v` of `v_K` to a discrete valuation on `F`, we obtain an
`R`-submodule of `V`,

.. MATH::

    M_v := \{ f \in M_K \mid v(f) \geq 0 \}.

It is easy to see that `M_v` if a *full lattice*, i.e.\ a free `R`-submodule of
`M_K` of rank `n`. More generally, if `V=\{v_1,\ldots,v_r\}` is a finite set
of valuations as above, then

.. MATH::

  M_V := \bigcap_{v\in V} M_v

is a lattice. We call `M_V` a *Riemann-Roch lattice*.

We define a class ``RRSpace`` whose objects represent a triple `(v_K, F/K, M_K)`
as above. With the available methods it is possible to compute Riemann-Roch
lattices `M_V`.

"""

from sage.all import SageObject


class RRSpace(SageObject):
    r""" Return the Riemann-Roch space defined by the input.

    INPUT:

    - ``v_K`` -- a discrete valuation on a field `K`
    - ``F`` -- a field extension of `K`
    - ``gens`` -- a nonempty list of elements of `F`

    OUTPUT: the object represented by `(v_K, F, M_K)`, where `M_K\subset F`
    is the `K`-subspace generated by ``gens``. Its functionality
    includes:

    - computing the Riemann-Roch lattice `M_V` for a finite set `V` of discrete
      valutions on `F` extending `v_K`
    - for `V_1\subset V_2`, compute the index `(M_{V_1}:M_{V_2})`

    etc.

    """

    def __init__(self, v_K, F, gens):
        from function_spaces import FunctionSpace
        K = v_K.domain()
        self._constant_base_field = K
        self._base_valuation = v_K
        self._function_field = F
        self._function_space = FunctionSpace(K, F, gens)
        self._valuations = {}
        self._reduced_basis = {}
        self._simple_lattices = {}

    def __repr__(self):
        return "the Riemann-Roch space with basis {}".format(self.rational_basis())

    def constant_base_field(self):
        return self._constant_base_field

    def base_valuation(self):
        return self._base_valuation

    def function_field(self):
        return self._function_field

    def function_space(self):
        return self._function_space

    def rational_basis(self):
        r""" Return a basis for this Riemann-Roch space.
        """
        return self.function_space().basis()

    def dimension(self):
        return self.function_space().dimension()

    def vector(self, f):
        r""" Return the vector representation of `f`.

        INPUT:

        - ``f`` -- an element of the function field `F`

        OUTPUT:

        If `f` is an element of this Riemann Roch space then the vector
        representing `f` as a linear combination of the standard basis
        is returned.

        Otherwise, ``None`` is returned.

        """
        return self.function_space().vector(f)

    def valuations(self):
        return self._valuations

    def add_valuation(self, v, key=None):
        r""" Add a valuation to the database, and return the key.

        INPUT:

        - ``v`` -- a discrete valuation on the function field `F`
        - ``key`` -- a string, or number, or .. (default=None)

        OUTPUT: the key for `v` in the database.

        The valuation `v` is added to the database of valuations, and its key is
        returned. It is expected that `v` is an extension of `v_K`, and that it
        has not been added before; but this is not checked.

        If ``key`` is given, it is used as the key. Otherwise, the key will be
        the index of `v`` in the database.
        """
        if not key:
            key = len(self._valuations)
        if key in self._valuations.keys():
            try:
                key = key + 1
            except ValueError:
                print "this key is already in use"
        self._valuations[key] = v

    def reduced_basis(self, val_key):
        r""" Return a reduced basis with respect to one valuation.

        INPUT:

        - ``val_key`` -- a key for a registered valuations

        OUTPUT:

        a basis `(f_1,..,f_r)` of this Riemann_Roch space which is reduced with
        respect to `v`, the valuation corresponding to ``val_key``.

        Reducedness means that for every linear combination of the basis

        .. MATH::

            f = a_1f_1 + \ldot + a_rf_r

        we have

        .. MATH::

            v(f) = \min_i v(a_if_i).

        """
        if val_key in self._reduced_basis:
            return self._reduced_basis[val_key]
        else:
            K = self.constant_base_field()
            basis = self.rational_basis()
            v = self.valuations()[val_key]
            reduced_basis = make_reduced_basis(K, basis, v)
            self._reduced_basis[val_key] = reduced_basis
            return reduced_basis

    def simple_RR_lattice(self, val_key, m):
        r""" Return the simple RR lattice.

        INPUT:

        - ``val_key`` -- a key for a registered valuations
        - ``m`` -- a rational number

        OUTPUT:

        The lattice `M_{v,m}` inside the Riemann-Roch space `M_K\subset F`
        defined by the inequality

        .. MATH::

            v(f) \geq m,

        where `v` is the valuation on the function field `F` corresponding to
        ``val_key``.

        """
        if (val_key, m) in self._simple_lattices:
            return self._simple_lattices[(val_key, m)]
        else:
            v_K = self.base_valuation()
            pi = v_K.uniformizer()
            e = v_K(pi)
            v = self.valuations()[val_key]
            reduced_basis = self.reduced_basis(val_key)
            k = [((m - v(f))/e).ceil() for f in reduced_basis]
            lattice_basis = [pi**k[i]*reduced_basis[i] for i in range(len(k))]
            lattice = RRLattice(self, lattice_basis)
            self._simple_lattices[(val_key, m)] = lattice
            return lattice

    def RR_lattice(self, inequalities):
        r""" Return the RR lattice defined by a list in inequalities.

        INPUT:

        - ``inequalities`` -- a list of pairs (``val_key``, `m`)

        Here ``val_key`` is the key for a registered valuation on `F`, and `m`
        is a rational number.

        OUTPUT:

        The full lattice inside this Riemann Roch space defined by the
        simultaneous inequalities

        .. MATH::

            v(f) \geq m,

        where `v` is the valuation corresponding to ``val_key``.

        """
        assert len(inequalities) > 0, "there must be at least one inequality"
        M = self.simple_RR_lattice(inequalities[0][0], inequalities[0][1])
        for val_key, m in inequalities[1:]:
            M_new = self.simple_RR_lattice(val_key, m)
            M = M.intersection(M_new)
        return M


class RRLattice(SageObject):
    r""" Return the lattice in a Riemann-Roch space with given generators.

    INPUT:

    - ``M_K`` -- a Riemann-Roch space
    - ``gens`` -- a list of elements of `M_K`

    OUTPUT: the lattice in `M_K` spanned by ``gens``.

    """

    def __init__(self, M_K, gens):
        from RR_spaces.lattices import DVR_Lattice
        F = M_K.function_field()
        v_K = M_K.base_valuation()
        assert all([f in F for f in gens]), "the generators must lie in the function field F"
        vectors = [M_K.vector(f) for f in gens]
        d = M_K.dimension()
        lattice = DVR_Lattice(v_K, vectors)
        self._RR_space = M_K
        self._lattice = lattice
        basis_vectors = lattice.basis()
        rational_basis = M_K.rational_basis()
        lattice_basis = []
        for v in basis_vectors:
            g = sum([v[i]*rational_basis[i] for i in range(d)])
            lattice_basis.append(g)
        self._basis = lattice_basis

    def __repr__(self):
        return "the lattice with basis {}".format(self.basis())

    def base_field(self):
        return self.RR_space().constant_base_field()

    def base_valuation(self):
        return self.RR_space().base_valuaton()

    def RR_space(self):
        return self._RR_space

    def basis(self):
        return self._basis

    def rank(self):
        return len(self.basis())

    def intersection(self, M):
        r""" Return the intersection of this lattice with another one.

        INPUT:

        - ``M`` -- a lattice inside the same Riemann Roch space

        OUTPUT: the lattice which is the intersection of `M` with ``self``.

        """
        M_K = self.RR_space()
        d = M_K.dimension()
        assert M.RR_space() is M_K, "M must lie in the same RR space as self"
        new_lattice = self._lattice.intersection(M._lattice)
        basis_vectors = new_lattice.basis()
        rational_basis = M_K.rational_basis()
        new_lattice_basis = []
        for v in basis_vectors:
            g = sum([v[i]*rational_basis[i] for i in range(d)])
            new_lattice_basis.append(g)
        return RRLattice(M_K, new_lattice_basis)

# ----------------------------------------------------------------------------

#                    auxiliary functions


def make_reduced_basis(K, B, v):
    r""" Return a reduced basis.

    INPUT:

    - ``K`` -- a field
    - ``B`` -- a list of `K`-linearly independent elements `f_i` of a field
      extension `F/K`
    - ``v`` -- a discrete valuation on `F`

    It is expected that the restriction `v_K:=v|_K` is nontirvial, that
    `F/K` is a function field in one variable, and that the
    residue field `k(v)` of `v` is also a function field over the residue field
    `k` of `v_K`.

    OUTPUT:

    A new basis `B_1` of the `K`-span of `B`, which is reduced with respect to
    `v`.

    """
    v_K = v.restriction(K)
    B_red = [B[0]]
    for i in range(1, len(B)):
        g = B[i]
        a = make_reduced(v_K, g, B_red, v)
        h = g + sum([a[j]*B_red[j] for j in range(i)])
        B_red.append(h)
    return B_red


def make_reduced(v_K, g, B, v):
    r""" Return the reduction of an element with respect to a reduced basis.

    INPUT:

    - ``v_K`` -- a discrete valuation on a field `K`
    - ``g`` -- a nonzero element of a finled extension `F/K`
    - ``B`` -- a list of `K`-linearly independent elements of `F`
    - ``v`` -- a discrete valuation on `v`, extending `v_K`

    It is assumed that `B` is reduced with respect to `v`, and that `g` does
    not lie in the `K`-span of `B`.

    OUTPUT:

    Write `B = [f_1,\ldots,f_r]`. Then the output is a list `[a_1,\ldots,a_r]`
    of elements of `K` such that `v(h)` is maximal, with

    .. MATH::

        h := g + \sum_i a_i f_i.

    """
    from function_spaces import FunctionSpace
    K = v_K.domain()
    pi = v_K.uniformizer()
    # we want to normalize v_K
    v_K = v_K/v_K(pi)
    k = v_K.residue_field()
    k_v = v.residue_field()
    h = g
    a = [K.zero() for i in range(len(B))]
    e_B = [v(f) for f in B]
    while True:
        e_h = v(h)
        h0 = v.element_with_valuation(e_h)
        hb = v.reduce(h/h0)
        Bb = [v.reduce(B[i]*h0**(-1)*pi**((e_h-e_B[i]).ceil())) for i in range(len(B))]
        Mb = FunctionSpace(k, k_v, Bb)
        is_in_Mb, cb = Mb.is_in(hb, coefficients=True, generators=True)
        if is_in_Mb:
            c = [v_K.lift(cb[i]) for i in range(len(cb))]
            for i in range(len(a)):
                a[i] -= c[i]*pi**((e_h-e_B[i]).ceil())
            h_new = g + sum([a[i]*B[i] for i in range(len(B))])

            # this is only for debugging:
            if v(h_new) <= e_h:
                print "B = ", B
                print "e_B = ", e_B
                print "h = ", h
                print "e_h = ", e_h
                print "h0 = ", h0
                print "hb = ", hb
                print "Bb = ", Bb
                print "cb = ", cb
                print "c = ", c
                print "a = ", a
                print "h_new = ", h_new
                return None

            h = h_new
            assert v(h) > e_h, "something is wrong!"
        else:
            return a

