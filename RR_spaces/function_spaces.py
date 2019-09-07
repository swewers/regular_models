r"""
Function spaces
===============

By a *function space* we mean a finite dimensional `K`-subspace `V\subset F`,
where `F/K` is a function field.

The main problem we have to solve is this: given a tuple `(f_1,\ldots,f_n)` of
elements of `F`, find the subspace `R\subset K^n` of linear relations between
the `f_i`.

"""


def relation_space(F, f_list):
    r""" Return the space of relations between a given list of elements of a
    function field.

    INPUT:

    - ``F`` -- a function field with base field `K`
    - ``f_list`` -- a list of elements of `F`

    OUTPUT: suppose ``f_list`` is `[f_1,\ldots,f_n]`. Then we return a list
    consisting of basis vectors of the space of all `K`-linear relations
    between the `f_i`.

    """
    pass


def vector_representation(F, f_list):
    r""" Return a list of vectors representing the given list of function field
    elements.

    INPUT:

    - ``F`` -- a function field with base field `K`
    - ``f_list`` -- a list of elements of `F`

    OUTPUT: a pair (``vector_list``, ``basis``), where ``vector_list`` is a list
    of vectors `v_i\in K^N`

    """
    from sage.arith.functions import lcm
    from sage.modules.free_module_element import vector
    K = F.constant_base_field()
    F0 = F.base_field()
    if F is F0:
        print "F is rational function field"
        print "f_list = ", f_list
        print
        # F is the rational function field over K
        x = F.gen()
        h = lcm([f.denominator() for f in f_list])
        g_list = [(f*h).numerator() for f in f_list]
        N = max([g.degree() for g in g_list]) + 1
        basis = [x**i/h for i in range(N)]
        vector_list = []
        for g in g_list:
            g_vector = vector(K, N, [g[i] for i in range(N)])
            vector_list.append(g_vector)
    else:
        print "F is finite extension of F0"
        print "f_list = ", f_list
        print
        y = F.gen()
        d = F.degree()
        coeff_list = []
        for f in f_list:
            coeff_list += f.list()
        vector_list1, basis1 = vector_representation(F0, coeff_list)
        N = len(basis1)
        basis = []
        for j in range(d):
            for i in range(len(basis1)):
                basis.append(basis1[i]*y**j)
        vector_list = []
        for i in range(len(f_list)):
            v = []
            for j in range(d):
                v += vector_list1[i*d + j]
            v = vector(K, N*d, v)
            vector_list.append(v)
    # we check the result
    for i in range(len(f_list)):
        f = f_list[i]
        v = vector_list[i]
        assert sum([v[j]*basis[j] for j in range(len(basis))]) == f, "something is wrong!"
    return vector_list, basis
