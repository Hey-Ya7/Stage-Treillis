# L = meet-semidistributive lattice
def join_kappa(L, j):
    r"""
    Return the kappa map of some join-irreducible element of a lattice.

    The lattice is assumed to be finite and meet-semidistributive. The kappa map of a join-irreducible element j is always 
    well-defined in this case and gives the unique maximal element among those above the lower cover of j but not above j.

    INPUT:

    - ``L`` -- lattice; assumed to be finite and meet-semidistributive
    - ``j`` -- an element of the lattice; assumed to be join-irreducible

    OUTPUT:

    The image of j by the kappa map. Raises an error if j is not join-irreducible. If L is not meet-semidistributive, an
    arbitrary maximal element (which may not be unique) is returned. The returned element is guaranteed to be meet-irreducible
    even if L is not meet-semidistributive.

    EXAMPLES:


    """
    assert j in L.join_irreducibles()
    js = L.lower_covers(j)[0]
    while true:
        if L.is_lequal(j, L.upper_covers(js)[0]):
            if len(L.upper_covers(js)) == 1:
                return js
            js = L.upper_covers(js)[1]
        else:
            js = L.upper_covers(js)[0]


def irreducible_graph(L):
    r"""
    Return the graph of (join-) irreducible elements of a (meet-) semidistributive lattice.
    
    INPUT:

    - ``L`` -- lattice; assumed to be finite and (meet-) semidistributive

    EXAMPLES:

    """

    K = {}
    for i in L.join_irreducibles():
        K[i] = JoinKappa(L, i)
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
    for x in X:
        for y in G.upper_covers(x):
            S.add(y)
    return [x for x in G if x not in S]


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
    for x in X:
        for y in G.lower_covers(x):
            S.add(y)
    return [x for x in G if x not in S]


# def MOPLattice(G):
#    return LatticePoset(([s for s in Subsets(G) if Set(left_orthogonal(G,right_orthogonal(G,s))) == s],lambda p,q:p.issubset(q)))

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