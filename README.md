Integral differential forms for superelliptic curves
====================================================

This is the Sage/Python package accompanying our preprint

> S. Kunzweiler and S. Wewers, Integral differential forms for superelliptic curves, Preprint, 2020

It contains the implementation of the algorithms described in that article.

Let K be a local field, with ring of integers R, and let Y be a *superelliptic curve* over K, given by an equation of the form
y^n = f(x). We assume that the exponent n is invertible in R. The goal is to compute a basis of *integral differential forms*.
For instance, consider the curve Y of genus 6 over the 2-adic numbers with equation y^3 = (x^3-2^4)((x+2)^2+2^3)((x+2)^2-2^3).
We compute a basis of integral differential forms as follows:

```
sage: from regular_models.superelliptic_curves import integral_differentials
sage: v_2 = QQ.valuation(2)
sage: R.<x> = QQ[]
sage: f = (x^3-2^4)*((x+2)^2+2^3)*((x+2)^2-2^3)
sage: integral_differentials(f, 3, v_2)
the lattice with basis [x^3 - 4*x, x*y - 16, 2*y - 16, 4*x^2 - 16, 8*x - 16, 16]
```
Thus, a basis is given by f_i(x,y)dx, i=1,..,6, where f_i are the functions on Y in the above list.

To run the code, you need

- a recent version of Sage (>= 8.8 should do)
- the Sage/Python package [MCLF](https://github.com/MCLF/mclf)
- the Sage/Python package [regular_models](https://github.com/swewers/regular_models) (this repository)

We plan to expand the code to be able to handle more general classes of curves, and compute regular models of them. 
At some point, this work should become part of MCLF.
