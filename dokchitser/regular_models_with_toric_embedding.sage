# Computing regular models with Tim Dokchitser's method
# =====================================================


from sage.all import SageObject, Set, ZZ, gcd, lcm, xgcd, ceil, floor, product, denominator, vector, Polyhedron, PolynomialRing, LaurentPolynomialRing, Matrix


class ToricCurve(SageObject):
    r""" A class for computing the smooth projective model of a curve,
    via an embedding into a toric variety.

    INPUT:

    - ``f`` -- a polynomial in two variables over a field `K`

    OUTPUT: an object which represents the affine curve `X` inside the torus
    `\mathbb{G}_m^2` given by the equation `f(x,y) = 0`. Assuming certain
    conditions hold (e.g. that `X` is smooth), we can compute the smooth
    projective model of `X` as the closure of `X` inside some toric surface.

    """

    def __init__(self, f):

        A = f.parent()
        K = A.base_ring()
        self._ring = A
        self._base_field = K
        self._f = f
        if not self.is_smooth():
            print('Warning: the toric model is not smooth ')

    def __repr__(self):
        return "The toric model of the curve {} = 0".format(self.equation())

    def equation(self):
        return self._f

    def Delta(self):

        if not hasattr(self, "Delta)"):
            self._Delta = self.equation().newton_polytope()
        return self._Delta

    def is_smooth(self):
        r""" Test whether the toric model of the curve X is smooth
        """
        f = self.equation()
        A = f.parent()
        x, y = A.gens()
        if not x * y in A.ideal(f, f.derivative(x), f.derivative(y)).radical():
            return False
        else:
            Delta = self.Delta()
            for L in Delta.faces(1):
                f_L = self.f_L(L)
                return all([m == 1 for g, m in f_L.factor()])

    def interior_points(self):
        if not hasattr(self, "_int_points"):
            Delta = self.Delta()
            int_points = [P for P in Delta.integral_points() if Delta.interior_contains(P)]
            self._int_points = int_points
        return self._int_points

    def genus(self):
        return len(self.interior_points())

    def f_L(self, L):
        r""" Return the polynomial corresponding to an edge of Delta
        """
        K = self._base_field
        R = PolynomialRing(K, "z")
        f = self.equation()
        z = R.gen()
        L = L.as_polyhedron()
        vertices = L.vertices_list()
        P1 = vertices[0]
        P2 = vertices[1]
        a = P2[0] - P1[0]
        b = P2[1] - P1[1]
        d = gcd(a, b)
        f_L = R.zero()
        for i in range(d + 1):
            P = [P1[0] + a / d * i, P1[1] + b / d * i]
            f_L = f_L + f[P[0], P[1]] * z**i
        return f_L


class ToricIntegralModel(SageObject):
    r""" A class for computing the regular model of a curve as in Tim
    Dokchitser's paper *Models of curves over DVRs*.

    INPUT:

    - ``f`` -- a polynomial in two variables over a field `K`
    - ``v_K`` -- a discrete valuation on `K`

    OUTPUT: an object which provides access to Dokchitser's method for computing
    a regular normal crossing model of the curve with equation `f(x,y) = 0` over
    the valuation ring of `v_K`. This method succeeds if the defining equation
    is *`\Delta_v`-regular* (see Definition 3.9 in Dokchitser's paper). Otherwise,
    we get a normal model of `X` with a rather explicit description.

    """

    def __init__(self, f, v_K):
        A = f.parent()
        K = A.base_ring()
        assert v_K.domain() is K, "the base field of f must be the domain of v_K"
        X = ToricCurve(f)
        if not X.is_smooth():
            print("Warning: the toric model of the curve defined by  {} = 0 is not smooth".format(f))
        v_K = v_K / v_K(v_K.uniformizer())  # normalize v_K
        self._equation = f
        self._base_field = K
        self._base_valuation = v_K
        self._toric_curve = X
        self._number_of_components = 0
        self._genus_of_component = []
        self._degree_of_component = []
        self._multiplicity_of_component = []
        self._intersection_number = {}
        self.compute_model()

    def __repr__(self):
        return "the toric integral model of the curve {} = 0 w.r.t. {}".format(self.equation(), self.base_valuation())

    def equation(self):
        return self._equation

    def base_field(self):
        return self._base_field

    def base_valuation(self):
        return self._base_valuation

    def toric_curve(self):
        return self._toric_curve

    def variables(self):
        return self.equation().parent().gens()

    def faces(self):
        if not hasattr(self, "_faces"):
            self._faces = [face_projection(F_v) for F_v in self.Delta_v()]
        return self._faces

    def edges(self):
        if hasattr(self, "_edges"):
            return self._edges
        edges = []
        for F in self.faces():
            for L in [L.as_polyhedron() for L in F.faces(1)]:
                if L not in edges:
                    edges.append(L)
        self._edges = edges
        return edges

    def Delta_v(self):
        r""" Return the polyhedral fan `Delta_v`.

        We encode `Delta_v` as a list of `2`-faces of a `3`-dimensional
        polyhedron.

        """
        if hasattr(self, "_Delta_v"):
            return self._Delta_v
        x, y = self.variables()
        f = self.equation()
        v_K = self.base_valuation()
        monomials = [[m.degree(x), m.degree(y)] for m in f.monomials()]
        point_list = [[m[0], m[1], v_K(f.coefficient(m))] for m in monomials]
        self._Delta_v = lower_convex_hull(point_list)
        return self._Delta_v

    def face_objects(self):
        if not hasattr(self, "_face_objects"):
            self._face_objects = [FaceObjectOfToricIntegralModel(self, F_v)
                                  for F_v in self.Delta_v()]
        return self._face_objects

    def edge_objects(self):
        if not hasattr(self, "_edge_objects"):
            self._edge_objects = [EdgeObjectOfToricIntegralModel(self, L)
                                  for L in self.edges()]
        return self._edge_objects

    def face_object(self, F):
        ret = [FO for FO in self.face_objects() if FO.face() == F]
        assert len(ret) == 1, "Error: there is not a unique object associated to this face"
        return ret[0]

    def edge_object(self, L):
        ret = [EO for EO in self.edge_objects() if EO.edge() == L]
        assert len(ret) == 1, "Error: there is not a unique object associated to this edge"
        return ret[0]

    def is_regular(self):
        faces_are_regular = all([self.face_object(F).is_smooth() for F in self.faces()])
        edges_are_regular = all([self.edge_object(L).is_smooth() for L in self.edges()])
        return faces_are_regular and edges_are_regular

    def number_of_components(self):
        return self._number_of_components

    def components(self):
        return range(self.number_of_components())

    def genus_of_component(self, i):
        return self._genus_of_component[i]

    def degree_of_component(self, i):
        return self._degree_of_component[i]

    def multiplicity_of_component(self, i):
        return self._multiplicity_of_component[i]

    def new_component(self, genus, degree, multiplicity):
        self._genus_of_component.append(genus)
        self._degree_of_component.append(degree)
        self._multiplicity_of_component.append(multiplicity)
        self._number_of_components += 1
        return self._number_of_components - 1

    def add_intersection(self, i, j, k):
        s = Set([i, j])
        if s in self._intersection_number:
            self._intersection_number[s] += k
        else:
            self._intersection_number[s] = k

    def intersection_matrix(self):
        if hasattr(self, "_intersection_matrix"):
            return self._intersection_matrix
        n = self.number_of_components()
        intersection_number = self._intersection_number
        M = Matrix(ZZ, n, n)
        for i in range(n):
            x_ii = 0
            for j in range(n):
                if i != j:
                    s = Set([i, j])
                    if s in intersection_number:
                        x_ij = intersection_number[s]
                    else:
                        x_ij = 0
                    M[i, j] = x_ij
                    x_ii -= self.multiplicity_of_component(j) * x_ij
            M[i, i] = x_ii / self.multiplicity_of_component(i)
        self._intersection_matrix = M
        return M

    def compute_model(self):
        X = self
        for face_object in self.face_objects():
            genus = face_object.curve().genus()
            degree = 1  # this is not correct in general !
            multiplicity = face_object.delta()
            new_component = self.new_component(genus, degree, multiplicity)
            face_object._component = new_component
        for edge_object in self.edge_objects():
            fb = edge_object.equation()
            s1, s2 = edge_object.slopes()
            delta = edge_object.delta()
            path = HJ_path(s1, s2)
            F1 = edge_object.adjacent_faces()[0]
            Y1 = X.face_object(F1)
            for gb, e in fb.factor():
                previous_component = Y1._component
                deg = gb.degree()
                for i in range(1, len(path) - 1):
                    m, d = path[i]
                    new_component = X.new_component(0, deg, delta * d)
                    X.add_intersection(previous_component, new_component, deg)
                    previous_component = new_component
                if edge_object.is_inner_edge():
                    F2 = edge_object.adjacent_faces()[1]
                    Y2 = X.face_object(F2)
                    last_component = Y2._component
                    X.add_intersection(previous_component, last_component, deg)


class FaceObjectOfToricIntegralModel(SageObject):
    r""" The object representing the component corresponding to a face.

    INPUT:

    - ``X`` -- a toric integral model
    - ``F_v`` -- a 2-face of `Delta_v`

    OUTPUT: an object representing the component `\bar{X}_F` of the special fiber
    of the model corresponding to a `2`-face `F`. By [D], Theorem 3.14,
    `\bar{X}_F` is the toric completion of the closed subscheme
    `X_F\subset\mathbb{G}_m^2` defined as `\bar{f}_F = 0`.

    """
    def __init__(self, X, F_v):
        self._toric_integral_model = X
        F, v, delta = deconstruct_face(F_v)
        self._face = F
        self._F_v = F_v
        self._v = v
        self._delta = delta

    def __repr__(self):
        return "the face object of with vertices {}".format(self.face().vertices_list())

    def toric_integral_model(self):
        return self._toric_integral_model

    def F_v(self):
        return self._F_v

    def face(self):
        return self._face

    def v(self, P):
        r""" Return the value of `v` at the point `P`.

        """
        a, b, c = self._v
        return a * P[0] + b * P[1] + c

    def delta(self):
        return self._delta

    def lattice(self):
        r""" Return the minimal lattice containing the integral points of `F`.

        The component is determined by a 2-face `F` in `\mathbb{Z}^2`. Let
        `\Lambda` be the smallest affine lattice containing `F\cap\mathbb{Z}^2`.
        The function returns three vectors `w_0,w_1,w_2\in\mathbb{Z}^2` such that

        .. MATH::

            \Lambda = \{ w_0 + i\cdot w_1 + j\cdot w_2 \mid i,j\in\mathbb{Z} \}.

        .. Note: probably this function is not needed.

        """
        f = self.toric_integral_model().equation()
        v_K = self.toric_integral_model().base_valuation()
        F = self.face()
        w0 = vector(F.vertices()[0])
        points = F.integral_points()
        points = [P for P in points if self.v(P).is_integral()]
        V = ZZ**2
        W = V.span([vector(points[i]) - w0 for i in range(len(points))])
        w1, w2 = W.gens()
        return w0, w1, w2

    def equation(self):
        r""" Return the equation defining the component.

        In the notation of [D], this is the Laurent polynomial `\bar{f}_F`,
        which defines the closed subscheme `X_F\subset\mathbb{G}_{m,k}^2`.
        Here `F` is the 2-face corresponding to this component.

        """
        if hasattr(self, "_equation"):
            return self._equation
        X = self.toric_integral_model()
        f = X.equation()
        w0, w1, w2 = self.lattice()
        v_K = X.base_valuation()
        k = v_K.residue_field()
        pi = v_K.uniformizer()
        Ab = LaurentPolynomialRing(k, ("u", "v"))
        u, v = Ab.gens()
        monomials = [m.degrees() for m in f.monomials()]
        fb = Ab.zero()
        for i, j in monomials:
            in_lattice, a, b = is_in_lattice(i, j, w0, w1, w2)
            if in_lattice:
                cb = v_K.reduce(f[i, j] * pi**(-self.v([i, j])))
                fb = fb + cb * u**a * v**b
        fb = Ab.polynomial_ring()(product([gb**m for gb, m in fb.factor()]))
        self._equation = fb
        return fb

    def curve(self):
        r""" Return the toric model of this component.

        """
        if not hasattr(self, "_curve"):
            self._curve = ToricCurve(self.equation())
        return self._curve

    def is_smooth(self):
        return self.curve().is_smooth()

    def edges(self):
        r""" Return the edges of the face `F`.

        """
        F = self.face()
        return [L.as_polyhedron() for L in F.faces(1)]


class EdgeObjectOfToricIntegralModel(SageObject):
    r""" Return the object representing the scheme corresponding to an edge `L`.

    INPUT:

    - ``X`` -- a toric integral model
    - ``L`` -- an edge of the polygon `\Delta` corresponding to `X`

    OUTPUT: the object representing the subscheme of the specal fiber
    corresponding to an edge `L` of `\Delta`. By [D], Theorem 3.14, this scheme
    is either of the closed suscheme of `\mathbb{G}_m`

    .. MATH::

        X_L: \bar{f}_L = 0

    of dimension `0`, or it is a projective curve `\Gamma_L\to X_L` whose
    reduced geometric fibers are chains of projective lines.

    """
    def __init__(self, X, L):
        self._X = X
        self._L = L

    def __repr__(self):
        return "the edge object with vertices {}".format(
            self.edge().vertices_list())

    def toric_integral_model(self):
        return self._X

    def edge(self):
        return self._L

    def is_outer_edge(self):
        if not hasattr(self, "._is_outer_edge"):
            self._is_outer_edge = (len(self.adjacent_faces()) == 1)
        return self._is_outer_edge

    def is_inner_edge(self):
        return not self.is_outer_edge()

    def adjacent_faces(self):
        if hasattr(self, "_adjacent_faces"):
            return self._adjacent_faces
        X = self.toric_integral_model()
        L = self.edge()
        adjacent_faces = []
        for F in X.faces():
            edges_of_F = [L1.as_polyhedron() for L1 in F.faces(1)]
            if L in edges_of_F:
                adjacent_faces.append(F)
        self._adjacent_faces = adjacent_faces
        return self._adjacent_faces

    def lattice_points_on_L(self):
        L = self.edge()
        vertices = L.vertices_list()
        P0 = vector(vertices[0])
        w = vector(vertices[1]) - P0
        g = gcd(w[0], w[1])
        points = [P0 + i * w / g for i in range(g + 1)]
        return [P for P in points if self.v(P).is_integral()]

    def v(self, P):
        if not hasattr(self, "_v"):
            F = self.adjacent_faces()[0]
            X = self.toric_integral_model()
            self._v = X.face_object(F).v
        return self._v(P)

    def equation(self):
        r""" Return the equation defining the scheme `X_L`

        In the notation of [D], this is the Laurent polynomial `\bar{f}_L`,
        which defines the closed subscheme `X_L\subset\mathbb{G}_{m,k}`.
        Here `L` is the edge corresponding to this component.

        """
        if hasattr(self, "_equation"):
            return self._equation
        X = self.toric_integral_model()
        f = X.equation()
        v_K = X.base_valuation()
        k = v_K.residue_field()
        pi = v_K.uniformizer()
        Ab = PolynomialRing(k, ("z"))
        z = Ab.gen()
        points = self.lattice_points_on_L()
        fb = Ab.zero()
        for i in range(len(points)):
            P = points[i]
            cb = v_K.reduce(f[P[0], P[1]] * pi**(-self.v([P[0], P[1]])))
            fb = fb + cb * z**i
        self._equation = fb
        return fb

    def is_smooth(self):
        return self.equation().is_squarefree()

    def delta(self):
        X = self.toric_integral_model()
        F = self.adjacent_faces()[0]
        Y = X.face_object(F)
        return lcm([Y.v(P).denominator() for P in self.edge().integral_points()])

    def slopes(self):
        r""" Return the two slopes of thi edge.

        OUTPUT: a pair (s1, s2) of integers, see [D], Definition 3.12,

        """
        X = self.toric_integral_model()
        L = self.edge()
        F1 = self.adjacent_faces()[0]
        Y1 = X.face_object(F1)
        a, b, c, P0, P1 = edge_function(L, F1)
        s1 = self.delta() * (Y1.v(P1) - Y1.v(P0))
        if self.is_inner_edge():
            F2 = self.adjacent_faces()[1]
            Y2 = X.face_object(F2)
            s2 = self.delta() * (Y2.v(P1) - Y2.v(P0))
        else:
            s2 = floor(s1 - 1)
        return s1, s2

# -----------------------------------------------------------------------------
#
#                 Helper functions


def lower_convex_hull(point_list):
    r""" Return the lower convex hull of a list of points in `\mathbb{Z}^3`.

    INPUT:

    - ``point_list`` -- a list of points in `\mathbb{Z}^3`

    OUTPUT: the lower convex hull of ``point_list``, as list of 2-dimensional
    faces (each face is an object of ``PolyhedronFace``).

    """
    Q = Polyhedron(point_list)
    faces = []
    for F in Q.faces(2):
        if F.ambient_Hrepresentation()[0].vector()[3] > 0:
            faces.append(F)
    return faces


def deconstruct_face(F_v):
    r""" Return F, v, delta. """
    F = face_projection(F_v)
    vec = F_v.ambient_Hrepresentation()[0].vector()
    a = - vec[1] / vec[3]
    b = - vec[2] / vec[3]
    c = - vec[0] / vec[3]
    delta = lcm([denominator(a), denominator(b), denominator(c)])
    return F, (a, b, c), delta


def is_in_lattice(i, j, w0, w1, w2):
    r""" Check whether a point lies in a lattice, and return the presentation.

    INPUT:

    - ``i``, ``j`` -- integers
    - ``w0``, `w1``, ``w2`` -- vectors in `\mathbb{Z}^2`

    OUTPUT: if there is a presentation

    .. MATH::

        (i, j) = w_0 + a\cdot w_1 + b\cdot w_2,

    with `a, b\in\mathbb{Z}`. If there is, return (``True``, a, b), otherwise
    return (``False, 0, 0)

    """
    V = ZZ**2
    W = V.span([w1, w2])
    x = W.coordinates(vector([i, j]) - w0)
    if x[0].is_integral() and x[1].is_integral():
        return True, x[0], x[1]
    else:
        return False, 0, 0


def face_projection(F_v):
    return Polyhedron([[P[0], P[1]] for P in F_v.as_polyhedron().vertices_list()])


def edge_function(L, F):
    r""" Return the affine function vanishing on ``L`` and positive on ``F``.

    INPUT:

    - ``L`` -- a one-dimensional polyhedron in `\mathbb{Z}^2`
    - ``F`` -- a two-dimensional polyhedron in `\mathbb{Z}^2` with face `L`

    OUTPUT: a `5`-tuple `(a, b, c, P_0, P_1)`. Here `a,b,c` are integers,
    with `\gcd(a, b)=1`, such that the affine function

    .. MATH::

        \phi(i,j) := a*i + b*j + c

    is zero on `L` and nonnegative on `F`. See [D], Notation 2.1. Furthermore,
    `P_0, P_1 \in \mathbb{Z}^2`such that `\phi(P_0)=0` and `\phi(P1) = 1`.

    """
    LL = [LL for LL in F.faces(1) if LL.as_polyhedron() == L][0]
    c, a, b = LL.ambient_Hrepresentation()[0].vector()
    g, x, y = xgcd(a, b)
    a = a / g
    b = b / g
    c = c / g
    P0 = L.integral_points()[0]
    P1 = [(1 - c) * x, (1 - c) * y]
    return a, b, c, P0, P1


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
