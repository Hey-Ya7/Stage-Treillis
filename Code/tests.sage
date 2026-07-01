def Random_lattice(n, p):
    return posets.RandomPoset(n, p).completion_by_cuts().canonical_label()

def Random_meetsemidistributive_lattice(n, p):
    while True:
        L = Random_lattice(n, p)
        if L.is_meet_semidistributive() and not L.is_join_semidistributive():
            return L


####### INTERVALLES ATOMIQUES #######


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

def Random_coatomic(n, p, x):
    for k in range(x):
        L = Random_lattice(n, p)
        if L.is_meet_semidistributive():
            print('L meet semidistributif')
            if not Test_coatomic_join(L):
                print(L.hasse_diagram().to_dictionary())



######## Lambda and Mu #########

def kappa_map(L):
    maxs = {}
    for j in L.join_irreducibles_poset():
        M = []
        l = [L.lower_covers(j)[0]]
        while l != []:
            l2 = []
            for x in l:
                m = True
                for y in L.upper_covers(x):
                    if not L.is_lequal(j, y):
                        l2.append(y)
                        m = False
                if m:
                    M.append(x)
            l = l2
        maxs[j] = Set(M)
    return maxs

def Lambda_map(L):
    maxs = kappa_map(L)
    Lambda = {}
    for x in L:
        s = Set()
        for j in maxs:
            if L.is_lequal(j, x):
                s = s.union(maxs[j])
        Lambda[x] = s
    return Lambda

def Mu_map(L):
    return  {x: Set([m for m in L.meet_irreducibles() if not L.is_lequal(x, m)]) for x in L}

def Lambda_equals_Mu(L):
    Lambda = Lambda_map(L)
    Mu = Mu_map(L)
    return all(Lambda[x] == Mu[x] for x in L)

def gamma_map(L):
    gamma = {}
    for j in L.join_irreducibles_poset():
        M = []
        l = [L.lower_covers(j)[0]]
        while l != []:
            l2 = []
            for x in l:
                cov = L.upper_covers(x)
                if len(cov) == 1:
                    M.append(x)
                for y in cov:
                    if not L.is_lequal(j, y):
                        l2.append(y)
            l = l2
        gamma[j] = Set(M)
    return gamma

def gamma_equals_kappa(L):
    gamma = gamma_map(L)
    kappa = kappa_map(L)
    return all(gamma[j] == kappa[j] for j in gamma)


"""
Treillis tels que gamma = kappa
Contient les treillis semimodulaires supérieurement, en particulier les treillis join-distributifs et les treillis géométriques
			1	1	2	4	9	21	56	158
join-distributif <==>
meet-semidistributif : 	1	1	2	3	5	9	17	32
upper-semimodular :	1	1	2	4	8	17	38	88
géométrique		1	1	1	1	1	1	2	1

"""

