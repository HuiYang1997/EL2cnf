def split(axiom, type='concepts'):
    axiom_s = axiom.split('<')
    if type == 'concepts':
        # a1 = axiom_s[1]
        # return a1.split('>', 1)[0], [a.split('>', 1)[0] for a in axiom_s[2:]]
        return [a.split('>', 1)[0] for a in axiom_s[1:]]
    else:
        a1 = axiom_s[-1]
        return [a.split('>', 1)[0] for a in axiom_s[1:-1]], a1.split('>', 1)[0]


class saturate_process_pools:
    def __init__(self):
        # (H, A), (H,r,K), H,K is sorted tuple
        self.H2A = {}
        self.H2rK, self.K2rH = {}, {}  # here self.K2rH is just a copy of self.H2rK which accelerate the searching progress.

    def add(self, axiom):
        # axioms of form "(implies (some r B) A)" is ignored
        first_item, rest = split(axiom)
        first = (first_item,)
        axiom_s = axiom.split('(')
        if len(axiom_s) == 2:
            assert len(rest) == 1
            clause = ('H2A', first, rest[0])
            self.add_clause(clause)
            result = [clause]
            return result

        result = []
        literal = axiom.split('(')[2]

        if literal[0] == 's':
            assert len(rest) == 2
            r, K = rest[0], (rest[1],)
            clause = ('H2rK', first, r, K)
            self.add_clause(clause)
            result.append(clause)

        elif literal[1] == 'n':
            for rest_term in rest:
                clause = ('H2A', first, rest_term)
                self.add_clause(clause)
                result.append(clause)

            if axiom[1] == 'e':
                rest_tuple = tuple(sorted(rest))
                clause = ('H2A', rest_tuple, first)
                self.add_clause(clause)
                result.append(clause)
        return result

    # add clause, return True if it is new clause, False if not. if type !='add', only return True, False, do not add.
    def add_clause(self, clause, type='add'):
        if clause[0] == 'H2A':
            H, A = clause[1], clause[2]
            # add (H,A)
            if H in self.H2A and A not in self.H2A[H]:
                if type == 'add':
                    self.H2A[H].add(A)
                return True
            elif H not in self.H2A:
                if type == 'add':
                    self.H2A[H] = {A}
                return True
            return False

        elif clause[0] == 'H2rK':
            H, r, K = clause[1], clause[2], clause[3]
            f = False
            # add (H,r,K)
            if K in self.K2rH:
                if r in self.K2rH[K] and H not in self.K2rH[K][r]:
                    if type == 'add':
                        self.K2rH[K][r].add(H)
                    f = True
                elif r not in self.K2rH[K]:
                    if type == 'add':
                        self.K2rH[K][r] = {H}
                    f = True
            else:
                if type == 'add':
                    self.K2rH[K] = {r: {H}}
                f = True

            if H in self.H2rK:
                if r in self.H2rK[H] and K not in self.H2rK[H][r]:
                    if type == 'add':
                        self.H2rK[H][r].add(K)
                    f = True
                elif r not in self.H2rK[H]:
                    if type == 'add':
                        self.H2rK[H][r] = {K}
                    f = True
            else:
                if type == 'add':
                    self.H2rK[H] = {r: {K}}
                f = True
            return f

    def not_vaid(self):
        if not self.K2rH or not self.H2A:
            return True
        else:
            return False


class saturate_ini_pools:
    def __init__(self):
        # A\sqsubseteq \exists r.B or  \exists r.B \sqsubseteq A
        self.A2rB, self.B2rA = {}, {}

        #  A\sqsubseteq B, A_1\cap....\cap A_n\sqsubseteq B, A tov {...,A_i,...}
        self.A2B, self.Ai2B, self.A2Ai = {}, {}, {}

        # A to (r, B), A\sqsubseteq \forall r.B
        self.A2rB_universal = {}

        # r1\circ...\circ rn \sqsubseteq r
        self.ri2r, self.r2ri = {}, {}

    def add(self, axiom):
        first, rest = split(axiom)
        axiom_s = axiom.split('(')
        # (implies/equi A B)
        if len(axiom_s) == 2:
            assert len(rest) == 1
            if first in self.A2B:
                self.A2B[first].update(rest)
            else:
                self.A2B[first] = set(rest)

            result = [('A2B', first, rest[0])]
            return result

        result = []
        literal = axiom.split('(')[2]

        if literal[0] == 's':  # (... (some...))
            assert len(rest) == 2
            if first in self.A2rB:
                if rest[0] in self.A2rB[first]:
                    self.A2rB[first][rest[0]].add(rest[1])
                else:
                    self.A2rB[first][rest[0]] = {rest[1]}
            else:
                self.A2rB[first] = {rest[0]: {rest[1]}}
            result.append(('A2rB', first, rest[0], rest[1]))

            if axiom[1] == 'e':
                if rest[1] in self.B2rA:
                    if rest[0] in self.B2rA[rest[1]]:
                        self.B2rA[rest[1]][rest[0]].add(first)
                    else:
                        self.B2rA[rest[1]][rest[0]] = {first}
                else:
                    self.B2rA[rest[1]] = {rest[0]: {first}}
                result.append(('B2rA', rest[1], rest[0], first))

        elif literal[1] == 'l':  # (... (all...))
            if first in self.A2rB_universal:
                if rest[0] in self.A2rB_universal[first]:
                    self.A2rB_universal[first][rest[0]].add(rest[1])
                else:
                    self.A2rB_universal[first][rest[0]] = {rest[1]}
            else:
                self.A2rB_universal[first] = {rest[0]: {rest[1]}}
            result.append(('A2rB_universal', first, rest[0], rest[1]))

            assert axiom[1] != 'e'

        else:  # (... (and...))
            if first in self.A2B:
                self.A2B[first].update(rest)
            else:
                self.A2B[first] = set(rest)

            result += [('A2B', first, rest_term) for rest_term in rest]

            if axiom[1] == 'e':
                rest_tuple = tuple(sorted(rest))
                if rest_tuple in self.Ai2B:
                    self.Ai2B[rest_tuple].add(first)
                else:
                    self.Ai2B[rest_tuple] = {first}
                # clause = ['Ai2B']+list(rest_tuple)+[first]
                result.append(('Ai2B', rest_tuple, first))

                for A in rest_tuple:
                    if A in self.A2Ai:
                        self.A2Ai[A].add(rest_tuple)
                    else:
                        self.A2Ai[A] = {rest_tuple}

        return result

    def add_role_axioms(self, axiom):
        begin, last = split(axiom, 'role')
        begin = tuple(begin)
        if begin in self.ri2r:
            self.ri2r[begin].add(last)
        else:
            self.ri2r[begin] = {last}

        if len(begin) > 1:
            for role in begin:
                if role in self.r2ri:
                    self.r2ri[role].add(begin)
                else:
                    self.r2ri[role] = {begin}

        result = ('ri2r', begin, last)
        return result

    # add clause, return True if it is new clause, False if not. if type !='add', only return True, False, do not add.
    def add_clause(self, clause, type='add'):
        if clause[0] == 'A2rB':
            A, r, B = clause[1], clause[2], clause[3]
            # add (H,r,K)
            if A in self.A2rB:
                if r in self.A2rB[A] and B not in self.A2rB[A][r]:
                    if type == 'add':
                        self.A2rB[A][r].add(B)
                    return True
                elif r not in self.A2rB[A]:
                    if type == 'add':
                        self.A2rB[A][r] = {B}
                    return True
            else:
                if type == 'add':
                    self.A2rB[A] = {r: {B}}
                return True
            return False

        elif clause[0] == 'B2rA':
            B, r, A = clause[1], clause[2], clause[3]
            # add (H,r,K)
            if B in self.B2rA:
                if r in self.B2rA[B] and A not in self.B2rA[B][r]:
                    if type == 'add':
                        self.B2rA[B][r].add(A)
                    return True
                elif r not in self.B2rA[B]:
                    if type == 'add':
                        self.B2rA[B][r] = {A}
                    return True
            else:
                if type == 'add':
                    self.B2rA[B] = {r: {A}}
                return True
            return False

        elif clause[0] == 'A2B':
            A, B = clause[1], clause[2]
            # check if h \sqsubseteq A1 have appeared
            if A in self.A2B and B not in self.A2B[A]:
                if type == 'add':
                    self.A2B[A].add(B)
                return True
            elif A not in self.A2B:
                if type == 'add':
                    self.A2rB[A] = {B}
                return True
            return False

        elif clause[0] == 'A2rB_universal':
            A, r, B = clause[1], clause[2], clause[3]
            # add (H,r,K)
            if A in self.A2rB_universal:
                if r in self.A2rB_universal[A] and B not in self.A2rB_universal[A][r]:
                    if type == 'add':
                        self.A2rB_universal[A][r].add(B)
                    return True
                elif r not in self.A2rB_universal[A]:
                    if type == 'add':
                        self.A2rB_universal[A][r] = {B}
                    return True
            else:
                if type == 'add':
                    self.A2rB_universal[A] = {r: {B}}
                return True
            return False

        elif clause[0] == 'Ai2B':
            Ai, A = clause[1], clause[2]
            if Ai in self.Ai2B and A not in self.Ai2B[A]:
                if type == 'add':
                    self.Ai2B[Ai].add(A)
                    for A in Ai:
                        if A in self.A2Ai:
                            self.A2Ai.add(Ai)
                        else:
                            self.A2Ai = {Ai}
                return True
            elif Ai not in self.Ai2B:
                if type == 'add':
                    self.Ai2B[Ai] = {A}
                    for A in Ai:
                        if A in self.A2Ai:
                            self.A2Ai.add(Ai)
                        else:
                            self.A2Ai = {Ai}
                return True
            return False


class saturate_pools:
    def __init__(self):
        # (H, A), (H,r,K)
        self.H2A, self.H2rK = {}, {}

    def add(self, axiom):
        first_item, rest = split(axiom)
        first = (first_item,)
        axiom_s = axiom.split('(')
        if len(axiom_s) == 2:
            assert len(rest) == 1
            if first in self.H2A:
                self.H2A[first].update(rest)
            else:
                self.H2A[first] = set(rest)

            result = [('H2A', first, rest[0])]
            return result

        result = []
        literal = axiom.split('(')[2]

        if literal[0] == 's':
            assert len(rest) == 2
            r, K = rest[0], (rest[1],)
            if first in self.H2rK:
                if r in self.H2rK[first]:
                    self.H2rK[first][r].add(K)
                else:
                    self.H2rK[first][r] = {K}
            else:
                self.H2rK[first] = {r: {K}}
            result.append(('H2rK', first, r, K))

        elif literal[1] == 'n':
            if first in self.H2A:
                self.H2A[first].update(rest)
            else:
                self.H2A[first] = set(rest)

            result += [('H2A', first, rest_term) for rest_term in rest]

            if axiom[1] == 'e':
                rest_tuple = tuple(sorted(rest))
                if rest_tuple in self.H2A:
                    self.H2A[rest_tuple].add(first)
                else:
                    self.H2A[rest_tuple] = {first}
                result.append(('H2A', rest_tuple, first))

        return result

    # add clause, return True if it is new clause, False if not. if type !='add', only return True, False, do not add.
    def add_clause(self, clause, type='add'):
        if clause[0] == 'H2A':
            H, A = clause[1], clause[2]
            # add (H,A)
            if H in self.H2A and A not in self.H2A[H]:
                if type == 'add':
                    self.H2A[H].add(A)
                return True
            elif H not in self.H2A:
                if type == 'add':
                    self.H2A[H] = {A}
                return True
            return False

        elif clause[0] == 'H2rK':
            H, r, K = clause[1], clause[2], clause[3]
            # add (H,r,K)
            if H in self.H2rK:
                if r in self.H2rK[H] and K not in self.H2rK[H][r]:
                    if type == 'add':
                        self.H2rK[H][r].add(K)
                    return True
                elif r not in self.H2rK[H]:
                    if type == 'add':
                        self.H2rK[H][r] = {K}
                    return True
            else:
                if type == 'add':
                    self.H2rK[H] = {r: {K}}
                return True
            return False

    def not_vaid(self):
        if not self.H2A or not self.H2rK:
            return True
        else:
            return False
