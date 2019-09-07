"""
                    help from Singular
                    ==================

"""

from sage.libs.singular.function import singular_function, lib as singular_lib


def radical_singular(I):
    r""" Return the radical of this ideal.

    INPUT:

    - ``I`` -- an ideal of a polynomial ring over `\mathbb{Z}`

    OUTPUT: the radical of `I`

    """
    singular_lib('primdecint.lib')
    return singular_function('radicalZ')(I)
