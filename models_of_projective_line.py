r"""
Models of the projective line
=============================

In this module we implement the algorithm described in Section 4 of our preprint

.. [KunzweilerWewers20] S. Kunzweiler and S. Wewers, Regular models of curves
    and tame ramification.


Let `K` be a field with a discrete valuation `v_K` and valuation ring `R`.
Let `X_K` denote the projective line over `K`. A *model* of `X_K` is a proper,
flat and normal `R`-scheme 'X' with generic fiber `X_K`.

Let `D_K\subset X_K` be an effective and reduced divisor. For a model `X` of
`X_K`, let `X_s` denote the reduced special fiber of `X`, `D^{\rm hor}\subset X`
the closure of `D_K` and `D:=X_s\cup D^{\rm hor}`. Our goal is to find a regular
model `X` such that `D` is a normal crossing divisor.



AUTHORS:

- Stefan Wewers (2019): initial version


EXAMPLES::

    sage: from regular_models.models_of_projective_line import *

We compute the regular rnc-model from [KunzweilerWewers20]_, Example 8.1. ::

    sage: v_2 = QQ.valuation(2)
    sage: R.<x> = QQ[]
    sage: f = (x^3-2^4)*((x+2)^2+2^3)*((x+2)^2-2^3)
    sage: X = minimal_rnc_model(f, v_2)
    sage: X.vertical_components()
    [vertical component corresponding to Point of type II on Berkovich line, corresponding to v(x + 2) >= 3/2,
    vertical component corresponding to Point of type II on Berkovich line, corresponding to v(x) >= 4/3,
    vertical component corresponding to Point of type II on Berkovich line, corresponding to v(x) >= 0,
    vertical component corresponding to Point of type II on Berkovich line, corresponding to v(x) >= 1,
    vertical component corresponding to Point of type II on Berkovich line, corresponding to v(x^2 + 4*x + 12) >= 4,
    vertical component corresponding to Point of type II on Berkovich line, corresponding to v(x^2 + 4*x + 12) >= 7/2,
    vertical component corresponding to Point of type II on Berkovich line, corresponding to v(x + 2) >= 2,
    vertical component corresponding to Point of type II on Berkovich line, corresponding to v(x) >= 2,
    vertical component corresponding to Point of type II on Berkovich line, corresponding to v(x) >= 3/2]

"""

# *****************************************************************************
#       Copyright (C) 2019 Stefan Wewers <stefan.wewers@uni-ulm.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# *****************************************************************************


from sage.all import SageObject


def minimal_rnc_model(f, v_K):
    r""" Return the minimal rnc-model of a divisor on the projective line,
    with respect to a discrete valuation.

    INPUT:

    - ``f`` -- a polynomial or a rational function over a field `K`
    - ``v_K`` -- a discrete valuation on `K`

    OUTPUT:

    a regular `v_K`-model `X` of the projective line, equipped with a
    horizontal divisor `D`, such that the following holds:

    1. on the generic fiber, `D` is the (reduced) divisor of zeroes and poles of `f`
    2. `(X,D)` is an *rnc-pair*, meaning that the union of `D` with the special fiber
      of `X` is a reduced normal crossing divisor
    3. `(X,D)` is minimal under Conditions 1 and 2.


    """
    A = f.parent()
    # K = v_K.domain()
    # assert A.base_ring() is K, "the base field of f has to be the domain of v_K"
    X = ModelOfProjectiveLine(v_K, A.variable_name())
    F = X.function_field()
    f = F(f)
    X.add_horizontal_divisor(f)
    X.make_minimal_rnc_model()
    return X


class ModelOfProjectiveLine(SageObject):
    r""" Return a model of the projective line over a discrete valuation ring.

    INPUT:

    - ``v_K`` -- a discrete valuation on a field `K`
    - ``var_name`` -- a string (default: "x")

    OUTPUT: an (empty) `R`-model of the projective line over `K`, where `R` is
    the valuation ring of `v_K`.

    'Empty' means that we do not specify the valuations corresponding to the
    vertical prime divisors of the model. These can be added, for instance,
    using the method ``add_component``.

    EXAMPLES::

        sage: from regular_models.models_of_projective_line import *

    We create an empty model over the 2-adic integers.::

        sage: v_2 = QQ.valuation(2)
        sage: ModelOfProjectiveLine(v_2)
        model of the projective line over 2-adic valuation

    """

    def __init__(self, v_K, var_name="x"):
        from sage.rings.function_field.constructor import FunctionField
        from mclf.berkovich.berkovich_line import BerkovichLine
        from mclf.berkovich.berkovich_trees import BerkovichTree
        self._base_valuation = v_K
        K = v_K.domain()
        self._base_field = K
        F = FunctionField(K, var_name)
        self._function_field = F
        X_K = BerkovichLine(F, v_K)
        T = BerkovichTree(X_K)
        self._berkovich_line = X_K
        self._tree = T
        self._vertical_components = []
        self._horizontal_components = []
        # the flag '_changed' indicated whether the model has been changed after
        # the last computation of the intersection numbers
        self._changed = False
        self._is_rnc = False
        self._is_minimal_rnc = False

    def __repr__(self):
        return "model of the projective line over {}".format(self.base_valuation())

    def base_valuation(self):
        return self._base_valuation

    def base_field(self):
        return self._base_field

    def function_field(self):
        return self._function_field

    def berkovich_line(self):
        return self._berkovich_line

    def tree(self):
        return self._tree

    def vertical_components(self):
        return self._vertical_components

    def horizontal_components(self):
        return self._horizontal_components

    def components(self):
        return self.vertical_components() + self.horizontal_components()

    def is_component(self, xi):
        r""" Return whether xi is the generic point of a component.

        INPUT:

        - ``xi`` -- a point of type I or II on the Berkovich line underlying this model

        OUTPUT:

        ``True`` is `\xi` is the generic point of a component of this model,
        ``False`` otherwise.

        """
        T = self.tree()
        vertex = T.find_point(xi)
        if not vertex:
            return False
        if xi.type() == "II":
            return not all([not comp.vertex().root().is_equal(xi)
                            for comp in self.vertical_components()])
        else:
            return not all([not comp.vertex().root().is_equal(xi)
                            for comp in self.horizontal_components()])

    def add_component(self, xi):
        r""" Add a component to the model.

        INPUT:

        - ``xi`` -- a point of type I or II on the Berkovich line underlying ``self``

        We add a component to the model `X` corresponding to `\xi`. If `\xi` is
        of type II, then this new component is vertical, otherwise it is
        horizontal.

        """
        assert xi.berkovich_line() is self.berkovich_line(), "xi must be a point\
            on the Berkovich line underlying this model"
        X = self
        if not X.is_component(xi):
            ComponentOfModel(X, xi)
            X._changed = True

        """
        T = X.tree()
        # we have to first check whether xi is already a component !
        # the first condition should be unnecessary; this is a bug in
        # mclf.berkovich_trees: T.find_point for an empty tree gives an error
        if not X.is_component(xi):
            T, vertex = T.add_point(xi)
            self._tree = T
            component = ComponentOfModel(self, vertex)
            if component.is_horizontal():
                self._horizontal_components.append(component)
            else:
                self._vertical_components.append(component)
            # we report that the model has changed
            self._changed = True
        """

    def remove_component(self, component):
        r""" Remove this component from the model.

        INPUT:

        - ``component`` - a component of a model of the projective line

        We remove the given component from the model. If it is a vertical
        component, this amounts to a modification of the model in which the
        given component is contracted. If it is a horizontal component then the
        model `X` itself remains unchanged.

        """
        component.remove()
        self._changed = True

    def add_horizontal_divisor(self, f):
        r""" Add the zeroes and poles of `f` to the horizontal divisor.

        INPUT:

        - ``f`` -- a polynomial or a rational function

        We add the divisor or zeroes and poles to the horizontal divisor.

        """
        X = self
        f = X.function_field()(f)
        D = X.berkovich_line().divisor(f)
        for xi, m in D:
            X.add_component(xi)

    def make_inf_closed(self):
        r""" Add vertical components to make the tree inf-closed.

        We add vertical components to the set of components such that it becomes
        inf-closed. As a result, any point on the special fiber will lie on at
        most two components.

        """
        X = self
        T = X.tree()
        for vertex in T.vertices():
            X.add_component(vertex)

    def make_rnc_model(self):
        r""" Refine the model to a regular rnc model.

        We refine the model `X` such that it becomes a regular model and such
        that the divisor `D` is a normal crossing divisor.

        We follow the Algorithm 4.11 from [KunzweilerWewers20]_:

        1. We add all the predecessors of all components
        2. We take the inf-closure
        3. We follow Algorithm 4.14.

        """
        X = self

        # Step 1
        for E in X.components():
            xi = E.vertex().root()
            for xi1 in predecessors(xi):
                X.add_component(xi1)

        # Step 2
        X.make_inf_closed()

        # Step 3
        new_components = []
        T = X.tree()
        for subtree in T.subtrees():
            xi0 = subtree.root()
            eta = critical_residue_class(xi0)
            critical_residue_class_is_empty = True
            for child in subtree.children():
                xi1 = child.root()
                if xi1.type() == "II":
                    for xi in resolution_chain(xi0, xi1):
                        new_components.append(xi)
                    if eta and eta.is_in_residue_class(xi1):
                        critical_residue_class_is_empty = False
            if xi0.type() == "II" and critical_residue_class_is_empty:
                for xi in resolution_chain(xi0):
                    new_components.append(xi)
        for xi in new_components:
            X.add_component(xi)
        X._is_rnc = True

    def make_minimal_rnc_model(self, components_to_keep=[]):
        r""" Refine the model to a minimal rnc model.

        INPUT:

        - ``components_to_keep`` -- list of components of the model

        The model `X` is refined to a minimal rnc-model containing the components
        in ``components_to_keep`.

        """
        X = self
        if not X._is_rnc:
            X.make_rnc_model()
        if not X._is_minimal_rnc:
            while True:
                E = X.removable_component()
                if E:
                    X.remove_component(E)
                else:
                    break
        X._is_minimal_rnc = True

    def removable_component(self):
        r""" Return a removable component (if one exists).

        OUTPUT:

        a removable component, if one exists, or ``None`` otherwise.

        We assume that the model `X` is regular and the divisor `D` a normal
        corssing divisor. Then a vertical component `E` is called *removable*
        if it has self-intersection number `-1` and meets at most two other
        components, *and* no horizontal component.

        This latter condition may not be necessary. However, the way we
        construct an rnc model it will typically be necessary.

        If the rnc assumption is true and the method returns ``None``, then we
        can conclude that the model is the minimal rnc model.

        However, if the model is not rnc, then the output is also ``None``,
        and no conclusion can be drawn from this information.

        """
        if not self._is_rnc:
            return None
        for E in self.vertical_components():
            if (E.valency() <= 2 and E.self_intersection() == -1
                    and all([E1.is_vertical() for E1 in E.neighbors()])):
                return E

    def show_tree(self):
        r""" Show a graphic representation of the component tree.

        """
        G, vertex_dict = self.tree().graph()
        root = self.tree().root()
        vertical_list = []
        horizontal_list = []
        no_component_list = []
        for i, xi in vertex_dict.items():
            if xi.is_equal(root):
                root_index = i
            if self.is_component(xi):
                if xi.type() == "II":
                    vertical_list.append(i)
                else:
                    horizontal_list.append(i)
                print(i, ": ", xi)
            else:
                no_component_list.append(i)
        vertex_colors = {'red': vertical_list, 'blue': horizontal_list,
                         'grey': no_component_list}
        G.show(vertex_colors=vertex_colors, tree_root=root_index, layout='tree')


class ComponentOfModel(SageObject):
    r""" Return the component of a model.

    INPUT:

    - ``X`` -- a model of the projective line
    - ``xi`` -- a point of type I or II on the Berkovich line underlying the model

    OUTPUT: an object representing the component corresponding to ``xi``.

    If no component with generic point `\xi` exists yet, then it is added to the
    list of components.

    """

    def __init__(self, X, xi):
        self._model = X
        T = X.tree()
        T, vertex = T.add_point(xi)
        X._tree = T
        self._vertex = vertex
        self._generic_point = xi
        self._is_vertical = (xi.type() == "II")
        # the tree vertex must 'know' the component
        vertex._attr = {}
        vertex._attr["component"] = self
        if self.is_vertical():
            X._vertical_components.append(self)
        else:
            X._horizontal_components.append(self)

    def __repr__(self):
        return "{} component corresponding to {}".format(self.type(), self.generic_point())

    def remove(self):
        """ Remove this component.
        """
        X = self.model()
        self.vertex()._attr.pop("component")
        T = X.tree().remove_point(self.generic_point())
        X._tree = T
        if self.is_vertical():
            X.vertical_components().remove(self)
        else:
            X.horizontal_components().remove(self)

    def model(self):
        return self._model

    def vertex(self):
        return self._vertex

    def generic_point(self):
        return self._generic_point

    def is_vertical(self):
        return self._is_vertical

    def is_horizontal(self):
        return not self._is_vertical

    def type(self):
        if self.is_vertical():
            return "vertical"
        else:
            return "horizontal"

    def multiplicity(self):
        assert self.is_vertical(), "multiplicity of horizontal component is not defined."
        return self.generic_point().pseudovaluation_on_polynomial_ring().E()

    def valency(self):
        r""" Return the valency of this component.

        The *valency* of a component is the number of its neighbors, i.e. the
        other components which intersect it.

        """
        return len(self.neighbors())

    def neighbors(self):
        r""" Return the list of the neighbors of this component.

        A *neighbor* of a component is another component which intersects it.

        """
        vertex = self.vertex()
        neighbors = vertex.children()
        if vertex.has_parent():
            neighbors.append(vertex.parent())
        return [v._attr["component"] for v in neighbors if "component" in v._attr]

    def self_intersection(self):
        r""" Return the self-intersection number of this component.

        """
        from sage.rings.integer_ring import ZZ
        assert self.is_vertical(), "self-intersection number of horizontal component not defined."
        ret = sum(E.multiplicity() for E in self.neighbors() if E.is_vertical())
        ret = -ret/self.multiplicity()
        assert ret.is_integral(), "something is wrong: self-intersection number is not an integer!"
        return ZZ(ret)

# ----------------------------------------------------------------------------

#               auxiliary functions


def predecessors(xi):
    r""" Return the predecessors of this Berkovich point.

    INPUT:

    - ``xi`` -- a point of type I or II on the Berkovich line

    OUTPUT:

    a list of points `[\xi_0,..,xi_n]` corresponding to the minimal augmentation
    chain of the inductive valuation corresponding to `\xi`. So `\xi_0` is the
    Gauss point, `\xi_0<\ldots<\xi_n` and `\xi=\xi_n`.

    """
    X_K = xi.berkovich_line()
    if xi.is_limit_point():
        xi = xi.approximation()
    y = xi.parameter()
    v = xi.pseudovaluation_on_polynomial_ring()
    v_list = v.augmentation_chain()[1:-1]
    return [X_K.point_from_pseudovaluation_on_polynomial_ring(w, y)
            for w in v_list]


def critical_residue_class(xi):
    r""" Return the critical residue class of this point.

    INPUT:

    - ``xi`` -- a point of type II on the Berkovich line

    OUTPUT: the point of type IV corresponding to the critical residue class of
    the discoid with root `\xi`, or ``None`` if it is not defined.

    The critical residue class is defined in [KunzweilerWewers20]_, Remark 3.18.

    .. NOTE::

        This method should be made obsolete by including the functionality in
        ``mclf.berkovich.berkovich_line``.

    """
    from sage.rings.infinity import Infinity
    from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
    if not xi.type() == "II" or xi.is_gauss_point():
        return None
    v = xi.pseudovaluation_on_polynomial_ring()
    v0 = v.augmentation_chain()[1]
    if v.E() == v0.E():
        return None
    phi, _ = xi.discoid()
    xi1 = xi.berkovich_line().point_from_discoid(phi, Infinity)
    return TypeVPointOnBerkovichLine(xi, xi1)


def resolution_chain(xi0, xi1=None):
    r""" Return the resolution chain of a point of type II.

    INPUT:

    - ``xi0`` -- a point of type II on the Berkovich line.
    - ``xi1`` -- a point of type I or II, strictly larger than `xi0`, or ``None``

    OUTPUT:

    a strictly increasing list of points of type II `\xi` such that
    `\xi_0<\xi<\xi_1` (or `xi_0<\xi` if ``xi1`` is ``None``).
    These points are determined as follows, see [KunzweilerWewers20]_,
    Section 4.4.

    Assume first that ``\xi1`` is ``None``.
    Let `v` be the inductive valuation corresponding to `\xi_0`,

    .. MATH::

        v = [v_0,...,v_n(\phi_n)=\lambda_n].

    If `\xi_1` is given, we assume that it corresponds to an inductive valuation
    `v'` of the form

    .. MATH::

         v' = [v_0,...,v_n(\phi_n)=\lambda_n'],

    where `\lambda_n'>\lambda_n`. If `\xi_1` is not given, then we let
    `\lambda_n'` be the smallest element of `1/N\mathbb{Z}` strictly larger
    then `\lambda:=\lambda_n`, where `N` is the least common denominator of
    `\lambda_1,\ldots,\lamnda_{n-1}`.

    Then the points `\xi` in the resolution chain correspond to the valuations

    .. MATH::

        v_\mu := [v_0,\ldots, v_n(\phi_n)=\mu],

    and where `\mu` runs through the *shortest path* from `\lambda_n'` to
    `\lambda_n`.

    """
    X_K = xi0.berkovich_line()
    y = xi0.parameter()
    v0 = xi0.pseudovaluation_on_polynomial_ring()

    if xi1 is None or xi1.type() == "I":
        if v0.is_gauss_valuation():
            N = 1
        else:
            N = v0.augmentation_chain()[1].E()
        phi = v0.phi()
        t0 = v0(phi)
        if (t0*N).is_integral():
            return []
        t1 = (t0*N+1).floor()/N
    else:
        v1 = xi1.pseudovaluation_on_polynomial_ring()
        # By assumption, xi0 must be an immediate predecessor of xi1.
        # Therefore, we may write v1 = [v0, v1(phi_1) = t_1]
        N = v1.augmentation_chain()[1].E()
        phi = v1.phi()
        assert v0.is_key(phi), "something is wrong!"
        t0 = v0(phi)
        t1 = v1(phi)
    path = shortest_path(N, t0, t1)[:-1]
    w_list = [v0.augmentation(phi, s) for s in path]
    return [X_K.point_from_pseudovaluation_on_polynomial_ring(w, y)
            for w in w_list]


def shortest_path(N, a_0, a_1=None):
    r""" Return the shortest N-path from a to aa.

    INPUT:

    ``N`` -- a positive integer

    ``a_0`` -- a nonnegative rational number

    ``a_1`` -- a positive rational number strictly greater than `a_0`, or ``None``

    OUTPUT:

    a strictly decreasing list `[a_1, .. , a_0]` of rational numbers, which is the
    *shortest `N`-path* from `a_1` to `a_0`, in the sense of Definition 2.10
    from [ObusWewers]. If ``a_1`` is ``None``,
    then we define `a_1` as the smallest element of `1/N\mathbb{ZZ}` strictly
    larger than `a_0`.

    ALGORITHM:

    We follow Corollary 2.16 from [ObusWewers].

    """
    path = HJ_path(a_1*N, a_0*N)
    path = [c/d/N for c, d in path]
    return path


def HJ_path(s1, s2):
    r""" Return the Hirzebruch-Jung path from s1 to s2.

    INPUT:

    - ``s1``, ``s2`` -- rational number such that `s_1 > s_2`

    OUTPUT: a list of pairs `(m_0, d_0),\ldots,(m_r,d_r)` such that

    .. MATH::

        s_1 > \frac{m_1}{d_1} > \ldots > \frac{m_r}{d_r} = s_2

    and

    .. MATH::

        m_i d_{i+1} - m_{i+1} d_i = 1, \quad i=1,..,r-1.

    """
    from sage.all import xgcd, ceil, floor
    assert s1 > s2, "s1 must be larger than s2"
    m1 = s1.numerator()
    d1 = s1.denominator()
    m2 = s2.numerator()
    d2 = s2.denominator()
    path = [(m1, d1)]
    while m1 / d1 > s2:
        _, x, y = xgcd(m1, d1)
        if d1 * m2 - m1 * d2 > 0:
            k = ceil((x * m2 + y * d2) / (d1 * m2 - m1 * d2))
        else:
            k = floor((x * m2 + y * d2) / (d1 * m2 - m1 * d2))
        m = - y - k * m1
        d = x - k * d1
        path.append((m, d))
        m1, d1 = m, d

    # these test are for debugging only, and should be unnecessary by now
    assert path[0][0] / path[0][1] == s1, "first entry not correct: {}".format(path)
    assert path[-1][0] / path[-1][1] == s2, "last entry not correct: {}".format(path)
    assert all([path[i][0] * path[i + 1][1] - path[i + 1][0] * path[i][1] == 1
                for i in range(len(path) - 1)]), "determinant condition wrong: {}".format(path)

    return path
