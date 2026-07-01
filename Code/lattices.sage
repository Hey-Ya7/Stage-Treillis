# note : part of this code was integrated (locally) to the sage library, at 
# sage/combinat/posets/lattices.py. For this reason, join_kappa and
# meet_dual_kappa were rewritten to be class methods of FiniteLatticePoset.

def join_kappa(self, j):
    r"""
    Return the kappa map of the join-irreducible element j.

    The lattice is assumed to be finite and meet-semidistributive.
    The kappa map of a join-irreducible element j is always well-defined 
    in this case, and gives the unique maximal element among those above 
    the lower cover of j but not above j.

    INPUT:

    - ``L`` -- lattice; assumed to be finite and meet-semidistributive
    - ``j`` -- an element of the lattice; assumed to be join-irreducible

    OUTPUT:

    The image of j by the kappa map. Raises an error if j is not join-
    irreducible. If L is not meet-semidistributive, an arbitrary maximal element
    (which may not be unique) is returned. The returned element is guaranteed to 
    be meet-irreducible even if L is not meet-semidistributive.

    EXAMPLES:

    On a meet-semidistributive lattice, the kappa map is always well defined 
    as a map from the join-irreducibles to the meet-irreducibles::

        sage: T4 = posets.TamariLattice(4)
        sage: j = T4.join_irreducibles()[0]
        sage: T4.join_kappa(j)
        (1, 1, 1, 0, 1, 0, 0, 0, 0)
        sage: T4.join_kappa(j) in T4.meet_irreducibles()
        True
    
    On elements that are not join-irreducible, the kappa map is ill-defined and
    an error is raised::

        sage: T4 = posets.TamariLattice(4)
        sage: e = T4[6]
        sage: T4.join_kappa(e)
        Traceback (most recent call last):
        ...
        ValueError: element is not join-irreducible

    If the lattice is not meet-semidistributive, an element is still returned. 
    This element is guaranteed to be above the lower cover of j but not j.
    Furthermore, it is also guaranteed to be meet-irreducible and maximal among 
    elements above the lower cover of j but not j::

        sage: L = posets.DiamondPoset(5)
        sage: L.join_kappa(2)
        1
        sage: L.is_lequal(0, 1) and not L.is_lequal(2, 1)
        True
        sage: 1 in L.meet_irreducibles()
        True
    
    However, if the lattice is not meet-semidistributive, the returned element 
    need not be the only maximal element among those above the lower cover of j 
    but not j. This can be seen in the previous example::
        
        sage: L = posets.DiamondPoset(5)
        sage: L.is_lequal(0, 3) and not L.is_lequal(2, 3)
        True
        sage: 3 in L.meet_irreducibles()
        True
    """
    # Algorithm: Starting from the lower cover of j, progressively move upwards
    # while not going above j. This process necessarily terminates by finitude.
    
    if j not in self.join_irreducibles():
        raise ValueError("element is not join-irreducible")
    js = self.lower_covers(j)[0]
    while True: # This loop will always terminate for a finite lattice.
        if self.is_lequal(j, self.upper_covers(js)[0]):
            if len(self.upper_covers(js)) == 1:
                return js
            js = self.upper_covers(js)[1]
        else:
            js = self.upper_covers(js)[0]


def meet_dual_kappa(self, m):
    r"""
    Return the dual kappa map of the meet-irreducible element m.

    The lattice is assumed to be finite and join-semidistributive. 
    The dual kappa map of a meet-irreducible element m is always well-defined 
    in this case, and gives the unique minimal element among those under 
    the upper cover of j but not under j.

    INPUT:

    - ``L`` -- lattice; assumed to be finite and join-semidistributive
    - ``m`` -- an element of the lattice; assumed to be meet-irreducible

    OUTPUT:

    The image of m by the dual kappa map. Raises an error if m is not meet-
    irreducible. If L is not join-semidistributive, an arbitrary minimal element 
    (which may not be unique) is returned. The returned element is guaranteed to 
    be join-irreducible even if L is not join-semidistributive.

    EXAMPLES:
    
    On a join-semidistributive lattice, the dual kappa map is always well defined 
    as a map from the meet-irreducibles to the join-irreducibles::

        sage: T4 = posets.TamariLattice(4)
        sage: m = T4.meet_irreducibles()[0]
        sage: T4.meet_dual_kappa(m)
        (1, 1, 0, 0, 1, 0, 1, 0, 0)
        sage: T4.meet_dual_kappa(m) in T4.join_irreducibles()
        True
    
    On elements that are not meet-irreducible, the dual kappa map is ill-defined,
    an error is raised::

        sage: T4 = posets.TamariLattice(4)
        sage: e = T4[5]
        sage: T4.meet_dual_kappa(e)
        Traceback (most recent call last):
        ...
        ValueError: element is not meet-irreducible

    If the lattice is not join-semidistributive, an element is still returned. 
    This element is guaranteed to be below the upper cover of m but not m.
    Furthermore, it is also guaranteed to be join-irreducible and minimal among 
    elements below the upper cover of m but not m::

        sage: L = posets.DiamondPoset(5)
        sage: L.meet_dual_kappa(2)
        1
        sage: L.is_lequal(1, 4) and not L.is_lequal(1, 2)
        True
        sage: 1 in L.join_irreducibles()
        True
    
    However, if the lattice is not join-semidistributive, the returned element 
    need not be the only minimal element among those below the upper cover of m 
    but not m. This can be seen in the previous example::
        
        sage: L = posets.DiamondPoset(5)
        sage: L.is_lequal(3, 4) and not L.is_lequal(3, 2)
        True
        sage: 3 in L.join_irreducibles()
        True

    """
    # Algorithm: Starting from the upper cover of m, progressively move downwards
    # while not going below m. This process necessarily terminates by finitude.

    if m not in self.meet_irreducibles():
        raise ValueError("element is not meet-irreducible")
    ms = self.upper_covers(m)[0]
    while True: # This loop will always terminate for a finite lattice.
        if self.is_lequal(self.lower_covers(ms)[0], m):
            if len(self.lower_covers(ms)) == 1:
                return ms
            ms = self.lower_covers(ms)[1]
        else:
            ms = self.lower_covers(ms)[0]


def join_irreducible_graph(L):
    r"""
    Return the graph of join-irreducible elements of the lattice.
    
    INPUT:

    - ``L`` -- lattice; assumed to be finite and meet-semidistributive

    EXAMPLES:

    """

    K = {}
    for i in L.join_irreducibles():
        K[i] = join_kappa(L, i)
    return DiGraph({i: [j for j in K if not L.is_lequal(i, K[j])] for i in K})


def right_orthogonal(G, X):
    r"""
    Return the right orthogonal of some subgraph of a DiGraph.
    
    INPUT:

    - ``G`` -- DiGraph
    - ``X`` -- Set; some subset of vertices

    OUTPUT:

    The right orthogonal of X as a subgraph of G.

    EXAMPLES:

    """

    S = set(X)
    l = []
    for x in G:
        if x not in S and all(y not in S for y in G.neighbors_in(x)):
            l.append(x)
    return l


def left_orthogonal(G, X):
    r"""
    Return the left orthogonal of some subgraph of a DiGraph.
    
    INPUT:

    - ``G`` -- DiGraph
    - ``X`` -- Set; some subset of vertices

    OUTPUT:

    The left orthogonal of X as a subgraph of G.

    EXAMPLES:

    """

    S = set(X)
    l = []
    for x in G:
        if x not in S and all(y not in S for y in G.neighbors_out(x)):
            l.append(x)
    return l


# plus performant
def MOPLattice(G, lattice=True):
    LS = [Set()]
    L = {}
    while LS != []:
        L2 = []
        for s in LS:
            cov = []
            for x in G:
                if x not in s:
                    s2 = list(s)
                    s2.append(x)
                    t = Set(left_orthogonal(G, right_orthogonal(G, s2)))
                    if t not in L and t not in L2:
                        L2.append(t)
                    cov.append(t)
            L[s] = cov
        LS = L2
    if lattice:
        return LatticePoset(L)
    return L

# work in progress
def updatePairs(G, pair, x):
    # takes a maximal orthogonal pair (X, Y), returns the smallest orthogonal pair (X', Y')
    # such that X' contains all points of X and x
    newY = set(pair[1])
    for y in newY:
        if G.is_lequal(x, y): newY.remove(y)
    return (left_orthogonal(G, newY), newY)


def MaxOrthoPairs(G, lattice=True):
    OrthoPairs = {}
    currentPairs = [(Set(), Set(G))]
    while len(currentDepth) > 0:
        covers = []
        for pair in currentPairs:
            OrthoPairs[pair] = []
            for x in G:
                if x not in pair[0]:
                    newPair = updatePairs(G, pair, x)
                    OrthoPairs[pair].append(newPair)
                    covers.append(newPair)
        currentPairs = covers
    if lattice: return LatticePoset(OrthoPairs)
    return OrthoPairs
    

def OPLattice(G, lattice=True):
    S = set()
    for x in MOPLattice(G, False):
        for s1 in Subsets(Set(x)):
            for s2 in Subsets(Set(right_orthogonal(G, x))):
                S.add((s1,  s2))
    if lattice:
        return LatticePoset((S, lambda p, q: p[0].issubset(q[0]) and q[1].issubset(p[1])))
    return S


def surjective_edges(G, loops=False):
    r"""
    Return the surjective edges of a directed graph.

    An edge between vertices x, y of G is surjective if, for all vertices z such that there exists
    an edge between y and z, there exists an edge between x and z.

    INPUT:

    -- ``G`` - DiGraph
    -- ``loops`` - boolean (default: ``False``); specifies whether the graph is cyclic

    """

    E = []
    for x,y,_ in G.edges():
        if loops or x != y:
            s = True
            for z in G.neighbors_out(y):
                if x!=z and not G.has_edge(x,z):
                    s = False
                    break
            if s:
                E.append((x,y))
    return E


def injective_edges(G, loops=False):
    r"""
    Return the injective edges of a directed graph.

    An edge between vertices y, z of G is surjective if, for all vertices x such that there exists
    an edge between x and y, there exists an edge between x and z.

    INPUT:

    -- ``G`` - DiGraph
    -- ``loops`` - boolean (default: ``False``); specifies whether the graph is cyclic

    """

    E = []
    for y, z, _ in G.edges():
        if loops or y != z:
            s = True
            for x in G.neighbors_in(y):
                if x != y and not G.has_edge(x, z):
                    s = False
                    break
            if s:
                E.append((y, z))
    return E


#check if a DiGraph G is a two-acyclic factorization system
def is_TAFS(G):
    r"""
    Return whether G is a two-acyclic factorization system.

    As shown in [...], this is equivalent to checking whether G gives rise to a semidistributive lattice.

    INPUT:

    - ``G`` -- DiGraph

    EXAMPLES:

    """

    GS = DiGraph(surjective_edges(G))
    GI = DiGraph(injective_edges(G))
    Mult = set((x,y) for x,y,_ in GI.edges())
    for x,y,_ in GS.edges():
        Mult.add((x,y))
        if GS.has_edge(y,x):
#            print(x,y,"cycle d'arêtes surjectives")
            return False
        if y in GI:
            if GI.has_edge(y,x):
#                print(x,y,"cycle d'arêtes surjective et injective")
                return False
            for z in GI.neighbors_out(y):
                Mult.add((x,z))
    for x,y,_ in GI.edges():
        Mult.add((x,y))
        if GI.has_edge(y,x):
#            print(x,y,"cycle d'arêtes injectives")
            return False
    for x,y,_ in G.edges():
        if x!=y and (x,y) not in Mult:
#            print(x,y,'arête composée non présente')
            return False
    return True


def DrawTAFS(G, size=15):
    S = surjective_edges(G)
    I = injective_edges(G)
    colI, colS, colIS, col = 'red','blue','black','green'
    D = {colI:[], colS:[], colIS:[], col:[]}
    for e in G.edges():
        if e[:2] in S:
            if e[:2] in I:
                D[colIS].append(e)
            else:
                D[colS].append(e)
        else:
            if e[:2] in I:
                D[colI].append(e)
            else:
                D[col].append(e)
    return G.plot(edge_colors = D,figsize = size)


def DoubleEdgesGraph(G):
    E = []
    for x,y,_ in G.edges():
        if x!=y and G.has_edge(y,x):
            E.append((x,y))
    return Graph(E)

# (note : is Forcing Order well-understood terminology? elaboration may be required)
def ForcingOrder(G):
    r"""
    Return the forcing order of a directed graph.

    INPUT:

    -- ``G`` - DiGraph

    EXAMPLES:

    """

    G = DiGraph(G, loops=True)
    for x in G:
        G.add_edge(x, x)
    S, I = surjective_edges(G, True), injective_edges(G, True)
    GS, GI = DiGraph(S, loops=True), DiGraph(I, loops=True)
    PS, PI = Poset((G, lambda x, y: (x, y) in S)), Poset((G, lambda x, y: (x,y) in I))
    E = []
    for y in GI:
        for x in PS.subposet(GI.neighbors_in(y)).maximal_elements():
            if x != y:
                E.append((x, y))
    for y in GS:
        for x in PI.subposet(GS.neighbors_out(y)).minimal_elements():
            if x != y:
                E.append((x, y))
    D = {x: [] for x in G}
    for x, y in E:
        D[x].append(y)
    D = DiGraph(D)
    F = D.transitive_closure()
    C = {c[0]: c for c in D.strongly_connected_components()}
    for x in C:
        F.merge_vertices(C[x])
    return Poset(F).relabel(lambda x: tuple(C[x]))


def Cov(G,X,PI = None,PS = None):
    if PI==None:
        PI = DiGraph()
        PI.add_vertices(G)
        PI.add_edges(injective_edges(G))
        PI = Poset(PI)
    if PS==None:
        PS = DiGraph()
        PS.add_vertices(G)
        PS.add_edges(surjective_edges(G))
        PS = Poset(PS)
    return PS.subposet(PI.subposet(X).minimal_elements()).minimal_elements()


def JoinRepresentations(L):
    G = irreducible_graph(L)
    PI = DiGraph()
    PI.add_vertices(G)
    PI.add_edges(injective_edges(G))
    PI = Poset(PI)
    PS = DiGraph()
    PS.add_vertices(G)
    PS.add_edges(surjective_edges(G))
    PS = Poset(PS)
    return {x:Cov(G,[j for j in G if L.is_lequal(j,x)],PI,PS) for x in L}


def SD_rowmotion(L, lengths=False):
    r"""
    Return the Rowmotion operator applied to L.

    INPUT:

    -- ``L`` - lattice;

    EXAMPLES:

    """

    J = JoinRepresentations(L)
    K = JoinKMap(L)
    A,C = list(L),[]
    while A!=[]:
        a = A[0]
        del A[0]
        c,a = [a],L.meet([K[j] for j in J[a]])
        while a!=c[0]:
            del A[A.index(a)]
            c.append(a)
            a = L.meet([K[j] for j in J[a]])
        C.append(c)
    if lengths:
        L = {}
        for c in C:
            if len(c) in L:
                L[len(c)] += 1
            else:
                L[len(c)] = 1
        return sum(L[k] for k in L),{k:L[k] for k in sorted(L)}
    return C


def factorization(G):
    if not is_TAFS(G):
        raise Exception('G is not a two-acyclic factorization system')
    GI,GS = {},{}
    for x,y in injective_edges(G):
        if x in GI:
            GI[x].append(y)
        else:
            GI[x] = [y]
    for x,y in surjective_edges(G):
        if x in GS:
            GS[x].append(y)
        else:
            GS[x] = [y]
    G2,EI,ES = {},set(tuple(e) for e in Poset(GI).cover_relations()),set(tuple(e) for e in Poset(GS).cover_relations())
    for x,y in EI.union(ES):
        if x in G2:
            G2[x].append(y)
        else:
            G2[x] = [y]
    return DiGraph(G2), {'red':list(EI.difference(ES)),'green':list(ES.intersection(EI)),'blue':list(ES.difference(EI))}