def Coatomic_intervals(L):
    CI = set()
    for y in L:
        for s in Subsets(L.lower_covers(y)):
            x = L.meet([y] + list(s))
            CI.add((x,y))
    return CI

# on teste si le poset des intervalles coatomiques est un treillis avec le même join que dans le cas semidistributif
def Test_coatomic_join(L):
    CI = Poset((Coatomic_intervals(L), lambda p,q: L.is_lequal(p[0],q[0]) and L.is_lequal(p[1],q[1])))
    if not CI.is_lattice():
        return False
    CI = LatticePoset(CI)
    for x in CI:
        for y in CI:
            if not CI.is_lequal(x,y) and not CI.is_lequal(y,x):
                j = L.join([x[1],y[1]])
                z = (L.meet([j] + [k for k in L.lower_covers(j) if L.is_lequal(x[0],k) and L.is_lequal(y[0],k)]),j)
                if z!= CI.join([x,y]):
                    return False
    return True

def Random_lattice(n, p):
    return posets.RandomPoset(n, p).completion_by_cuts().canonical_label()

def Random_coatomic(n, p, x):
    for k in range(x):
        L = Random_lattice(n, p)
        if L.is_meet_semidistributive():
            print('L meet semidistributif')
            if not Test_coatomic_join(L):
                print(L.hasse_diagram().to_dictionary())