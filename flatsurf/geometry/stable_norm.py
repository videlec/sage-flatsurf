r"""
Stable norm
"""

import itertools
import collections

from sage.graphs.digraph import DiGraph
from sage.rings.integer_ring import ZZ
from sage.rings.qqbar import AA
from sage.rings.real_mpfr import RealField
from sage.rings.real_mpfr import RealField
from sage.rings.infinity import Infinity
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector

def angle(S, v1, v2):
    r"""
    Given two tangent vector based at the same point, return the angle between them.
    """
    if v1 == v2:
        return 0

    p1 = S.point(v1.polygon_label(), v1.point())
    p2 = S.point(v2.polygon_label(), v2.point())
    if p1 != p2:
        raise ValueError("the tangent vectors must be based at the same point: {} and {}".format(v1.point(), v2.point()))

    u1 = v1.vector()
    u2 = v2.vector()

    x = v1.counterclockwise_to(u2)
    if u1[0] * u2[1] != u2[0] * u1[1]:
        raise NotImplementedError("non-colinear vectors")

    if u1[0]:
        s1 = (u1[0] > 0) - (u1[0] < 0)
        s2 = (u2[0] > 0) - (u2[0] < 0)
    else:
        s1 = (u1[1] > 0) - (u1[1] < 0)
        s2 = (u2[1] > 0) - (u2[1] < 0)
    if s1 * s2 == 1:
        a = 2
    elif s1 * s2 == -1:
        a = 1
    else:
        raise RuntimeError

    while x != v2:
        x = x.counterclockwise_to(u2)
        a += 2

    return a


def cylinders(S, B):
    r"""
    Return a list of cylinders in the surface ``S`` whose boundary belongs to
    the list of saddle connections ``B``.

    Note: the function ignores cylinders bounded by a single saddle connection.
    """
    ans = []

    by_holonomy = collections.defaultdict(list)
    for sc in B:
        by_holonomy[sc.holonomy()].append(sc)

    # build a graph whose vertices are the start and edges are (start) -- sc -- (end) -- rot ccw -- (start)
    # then boundary of cylinders are cycles
    for hol, scs in by_holonomy.items():
        G = DiGraph(len(scs))
        for (i1, sc1) in enumerate(scs):
            for (i2, sc2) in enumerate(scs):
                if i1 != i2 and angle(S, sc1.end_tangent_vector(), sc2.start_tangent_vector()) == 1:
                    G.add_edge(i1, i2)
        for cc in G.strongly_connected_components():
            if len(cc) > 1:
                # ignore as this is a saddle connection
                yield [scs[i] for i in cc]


def stable_norm_integral_points(S, R, numerical=True):
    r"""
    Return a dictionary whose keys are the integral points in homology whose
    squared stable norm is < R together and the values is the stable norm.

    EXAMPLES::

        sage: from flatsurf import *
        sage: from flatsurf.geometry.stable_norm import stable_norm_integral_points
        sage: S = translation_surfaces.mcmullen_L(1, 1, 1, 1)
        sage: norm = stable_norm_integral_points(S, 10)
        sage: print(len(norm))
        129
    """
    from flatsurf.geometry.categories.translation_surfaces import TranslationSurfaces
    if S not in TranslationSurfaces().FiniteType():
        raise TypeError("S must be a finite type translation surface")

    if S.angles() != [3]:
        raise ValueError("the function only works for genus two translation surfaces in the stratum H(2)")

    if numerical:
        ring = RealField(256)
    else:
        ring = AA

    H = S.homology()
    B = S.saddle_connections(R)
    C = cylinders(S, B)

    hol_hom = [(sc.holonomy(), H(sc)) for sc in B]
    #hol_hom.extend((sum(sc.holonomy() for sc in cyl), sum(H(sc) for sc in cyl)) for cyl in C)
    hol_hom.sort(key=lambda hh: hh[0][0]**2 + hh[0][1]**2)

    gens = H.gens()
    intersection_matrix = matrix(ZZ, len(gens))

    for i, gi in enumerate(gens):
        for j, gj in enumerate(gens):
            intersection_matrix[i, j] = gi.algebraic_intersection(gj)

    norm = collections.defaultdict(lambda: Infinity)  # for each class, we store its current norm
    norm[H.zero()] = ring.zero()
    for i, (xyi, hi) in enumerate(hol_hom):
        xi, yi = xyi
        normi = (ring(xi)**2 + ring(yi)**2).sqrt()
        norm[hi] = normi
        for j in range(i):
            xyj, hj = hol_hom[j]
            if vector(ZZ, hi.coefficients()) * intersection_matrix * vector(ZZ, hj.coefficients()):
                # discard saddle connection that intersects
                continue

            # TODO: also ignore when hi and hj are linearly dependent

            # now iterate over casses in ZZ hi + ZZ hj whose norm is < r
            xj, yj = xyj
            normj = norm[hj]
            ai = ZZ.one()
            while (ai * normi)**2 < R:
                aj = ZZ.one()
                # TODO: this better would be exact
                while (ai * normi + aj * normj)**2 < R:
                    for si, sj in itertools.product((1, -1), repeat=2):
                        h = si * ai * hi + sj * aj * hj
                        norm[h] = min(norm[h], ai * normi + aj * normj)
                    aj += 1
                ai += 1

    if numerical:
        for h, n in norm.items():
            norm[h] = (ZZ(2)**14 * n).round() / ZZ(2)**14

    return norm
