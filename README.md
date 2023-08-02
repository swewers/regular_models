# Integral differential forms for superelliptic curves

This is the Sage/Python package accompanying our preprint

> S. Kunzweiler and S. Wewers, Integral differential forms for superelliptic curves, Preprint, 2023

It contains the implementation of the algorithms described in that article.

Let $K$ be a local field, with ring of integers $R$, and let $Y$ be a *superelliptic curve* over $K$, given by an equation of the form $y^n = f(x)$. 
Under the condition that the exponent $n$ is invertible in $R$, our implementation can be used to compute a basis of *integral differential forms*.


## Examples

For instance, consider **Example 5.2** from [KunzweilerWewers23].
Let $Y$ be the hyperelliptic curve
$$ Y: y^2 = (x^2-5)^3-5^5$$
defined over $\mathbb{Q}_5$.

The input for our algorithm in this case is:
* the polynomial $f = (x^2-5)^3-5^5$,
* the exponent $n=2$ of $y$,
* the $5$-adic valuation $v_5$.

```
sage: from regular_models.superelliptic_curves import integral_differentials
sage: R.<x> = QQ[]
sage: f = (x^2-5)^3-5^5
sage: n=2
sage: v5 = QQ.valuation(5)
sage: integral_differentials(f,n,v5)
the lattice with basis [x, 5]
```
In this implementation the space of differentials is viewed as a subspace of the function space of $Y$ via the embedding $\omega \mapsto \omega / \eta$ with $\eta = \frac{dx}{y^{n-1}}$, and the output has to be interpreted with respect to this embedding. This means that $$(x\frac{dx}{y}, 5 \frac{dx}{y})$$ is a basis for the lattice of integral differentials of $Y$.


Modifying the above computation by setting $n=3$, we compute the lattice of integral differential forms for the superelliptic curve 
$$y^3 = (x^2-5)^3-5^5.$$
This is **Example 5.3** in [KunzweilerWewers23].
```
sage: n=3
sage: integral_differentials(f,n,v5)
the lattice with basis [x^2 - 5, y, 5*x, 25]
```

For hyperelliptic curves $y^2 = f(x)$, our implementation can also be used to compute the order of the *hyperelliptic discriminant*
$$\Lambda := \Delta^{g} \cdot \omega^{\otimes 8g+4}$$,
where $g$ is the genus of the curve, $\Delta$ the discriminant of $f$ and $\omega = \frac{dx}{y} \land \dots \land x^{g-1}\frac{dx}{y}$. This is a canonical element of the curve. In our first example, we obtain the following.

```
sage: g = 2
sage: a = order_hyperelliptic_discriminant(f,v5); a
26
sage: a == g * v5(f.discriminant()) - (8*g+4)*v5(covolume(integral_differentials(f,2,v5)))
True
```

Let $Y$ be a hyperelliptic curve of genus $g$ over a local field $K$, defined by some equation of the form 
$Y: y^2 = f(x).$ We write $\Delta$ for the discriminant of this equation and $\omega = \frac{dx}{y} \land \dots \land x^{g-1}\frac{dx}{y}$. We call 
$$\Lambda := \Delta^{g} \cdot \omega^{\otimes 8g+4}$$ the *hyperelliptic discriminant*. 
By the order of the hyperelliptic discriminant, $\text{ord}(\Lambda)$, we mean the order of vanishing of  $\Lambda \in (\det M)^{\otimes 8g+4}$ at the prime ideal of $O_K$, where $M$ denotes the lattice of integral differentials.

More examples can be found in the Jupyter notebook `Examples.ipynb`.


## How to install

To run the code, you need

- a recent version of Sage (>= 9.0 should do)
- the Sage/Python package [MCLF](https://github.com/MCLF/mclf) (>= version 1.0.6). For example this can be installed using the command 
``` 
sage -pip install git+https://github.com/MCLF/mclf
```
- the Sage/Python package [regular_models](https://github.com/swewers/regular_models) (this repository)
``` 
sage -pip install git+https://github.com/swewers/regular_models
```

We plan to expand the code to be able to handle more general classes of curves, and compute regular models of them. 
At some point, this work should become part of MCLF.
