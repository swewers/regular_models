r"""
Models of the projective line
=============================

Let `K` be a field with a discrete valuation `v_K` and valuation ring `R`.
Let `X_K` denote the projective line over `K`. A *model* of `X_K` is a proper,
flat and normal `R`-scheme with generic fiber `X_K`.

"""

from sage.all import SageObject


def minimal_rnc_model(f, v_K):
    r""" Return the minimal rnc-model of a divisor on the projective line,
    with respect to a dicrete valuation.

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

    def is_component(self, xi):
        r""" Return whether xi is the generic point of a component.

        INPUT:

        - ``xi`` -- a point of type I or II on the Berkovich line underlying this model

        OUTPUT:

        ``True`` is `\xi` is the generic point of a component of this model,
        ``False`` otherwise.

        """
        T = self.tree()
        if T.root():
            vertex = T.find_point(xi)
        else:
            # this is only necessary because of a bug in mclf
            vertex = False
        if not vertex:
            return False
        if xi.type() == "II":
            return not all([not comp.vertex() is vertex
                            for comp in self.vertical_components()])
        else:
            return not all([not comp.vertex() is vertex
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

        We add vertical components to the component tree such that it is inf-closed.
        As a result, any point on the special fiber will lie on at most two components.

        """
        X = self
        T = X.tree()
        for vertex in T.vertices():
            X.add_component(vertex)

    def make_rnc_model(self):
        r""" Refine the model to a regular rnc model.

        This seems to work now for the vertical components.

        I still need to find out how to deal with the horzontal components.

        """
        X = self
        X.make_inf_closed()
        X.add_component(X.berkovich_line().gauss_point())
        # X.make_rnc_model_from_component(X.tree())
        T = X.tree()
        # the component set is inf_closed, therefore T is exactly the component
        # tree
        # we make sure that for any vertex of the tree, all its predecessors
        # are also components
        new_components = []
        for xi in T.vertices():
            for xi1 in predecessors(xi):
                new_components.append(xi1)
        for xi in new_components:
            X.add_component(xi)
        # the component tree may have changed:
        T = X.tree()
        new_components = []
        # now we add the resolution chains
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

    def make_minimal_rnc_model(self, components_to_keep=[]):
        r""" Refine the model to a minimal rnc model.

        INPUT:

        - ``components_to_keep`` -- list of components of the model

        The model `X` is refined to a minimal rnc-model containing the components
        in ``components_to_keep`.

        """
        X = self
        X.make_rnc_model()
        print("Minimal rnc model is not yet implemented.")

    def show_tree(self):
        r""" Show a graphic representation of the component tree.

        """
        G, vertex_dict = self.tree().graph()
        vertical_list = []
        horizontal_list = []
        for i, xi in vertex_dict.items():
            if xi.type() == "II":
                vertical_list.append(i)
            else:
                horizontal_list.append(i)
            print(i, ": ", xi)
        # print(vertex_dict)
        G.show(partition=[vertical_list, horizontal_list])


class ComponentOfModel(SageObject):
    r""" Return the component of a model.

    INPUT:

    - ``X`` -- a model of the projective line
    - ``vertex`` -- a vertex of the component tree of `X`

    OUTPUT: an object representing the component corresponding to ``vertex``.

    """

    def __init__(self, X, vertex):
        self._model = X
        self._vertex = vertex
        xi = vertex.root()
        self._generic_point = xi
        self._is_vertical = (xi.type() == "II")

    def __repr__(self):
        return "{} component corresponding to {}".format(self.type(), self.generic_point())

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

    OUTPUT: the critical residue class of the discoid with root `\xi`, or
    ``None`` if it does not exist.

    """
    from sage.rings.infinity import Infinity
    from mclf.berkovich.type_V_points import TypeVPointOnBerkovichLine
    if not xi.type() == "II" or xi.is_gauss_point():
        return None
    v = xi.pseudovaluation_on_polynomial_ring()
    v0 = v.augmentation_chain()[1]
    if v.E() == v0.E():
        return None
    else:
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
    These points are determined as follows, see [KunzweilerWewers].

    Assume first that ``\xi1`` is ``None``.
    Let `v` be the inductive valuation corresponding to `\xi_0`,

    .. MATH::

        v = [v_0,...,v_n(\phi_n)=\lambda_n].

    Let `N` be the least common denominator of `\lambda_1,\ldots,\lamnda_{n-1}`.
    Let `\lambda'` be the smallest element of `1/N\mathbb{Z}` strictly larger
    then `\lambda:=\lambda_n`. Then the points `\xi` correspond to the valuations

    .. MATH::

        v_\mu := [v_0,\ldots, v_n(\phi_n)=\mu],

    and where `\mu` runs through the *shortest path from `\lambda'` to `\lambda`.

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
    """
    if d1 == 1:
        N = s2.ceil()
        path = path + [(i, 1) for i in range(m1 - 1, N - 1, -1)]
    if m1 / d1 > s2:
        path2 = HJ_path(N - s2, 0)
        path = path + [(- m - N * d, d)]
    """
    assert path[0][0] / path[0][1] == s1, "first entry not correct: {}".format(path)
    assert path[-1][0] / path[-1][1] == s2, "last entry not correct: {}".format(path)
    assert all([path[i][0] * path[i + 1][1] - path[i + 1][0] * path[i][1] == 1
                for i in range(len(path) - 1)]), "determinant condition wrong: {}".format(path)
    return path


def neg_continued_fractions_expansion(y):
    r""" Return the convergents of the negative continued fraction expansion of y.

    """
    expansion = []
    a = y.ceil()
    expansion = [a]
    while a > y:
        y = 1/(a - y)
        a = y.ceil()
        expansion.append(a)
    return expansion


def ncf_value(a_list):
    if len(a_list) == 1:
        return a_list[0]
    else:
        return a_list[0] - 1/ncf_value(a_list[1:])


def convergents(a_list):
    ret = []
    for i in range(len(a_list)):
        ret.append(ncf_value(a_list[:i+1]))
    return ret
