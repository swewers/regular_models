#    test suite for different.py
#    ===========================

#   1. Number fields
#   ----------------

R0.<x> = ZZ[]
R.<x> = QQ[]

for i in range(10):
    while True:
        f = x^5 + R0.random_element(4)
        if f.is_irreducible():
            break
    L.<alpha> = QQ.extension(f)
    for p in [2,3,5]:
        v = QQ.valuation(p)
        D = L.different()
        for w in v.extensions(L):
            d1 = different_of_finite_extension(v, w)
            d2 = min([w(a) for a in D.gens()])
            if d1 != d2:
                print("Error:")
                print("L = ", L)
                print("w = ", w)
                print("d1 = ", d1)
                print("d2 = ", d2)

# function fields over p-adic fields
# ----------------------------------

K.<x> = FunctionField(QQ)
R0.<T> = K._ring[]
R.<T> = K[]

for i in range(20):
    while True:
        f = T^8 + R0.random_element(5)
        if f.is_irreducible():
            break
    L.<y> = K.extension(f)
    for p in [2,3,5]:
        v = K.valuation(GaussValuation(K._ring, QQ.valuation(p)))
        for w in v.extensions(L):
            e = w.value_group().index(v.value_group())
            d = different_of_finite_extension(v, w)
            kw = w.residue_field()
            kv = v.residue_field()
            g = _minimal_polynomial(kw.gen(), kv)
            is_separable = g.derivative() != 0
            is_wild = p.divides(e) or not is_separable
            if (is_wild and d < 1) or (not is_wild and d != (e-1)/e):
                print("Error:")
                print("L = ", L)
                print("w = ", w)
                print("e = ", e)
                print("d = ", d)
