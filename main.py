from tools import trans_back, formal_form, mkdir, depth_bigger_than
from tqdm import tqdm
import json
from random import sample, randint
from copy import deepcopy
from pool import saturate_ini_pools, saturate_pools, saturate_process_pools
from itertools import product


def cut_axiom(one_axiom):
    '''
    :param one_axiom: str ... str (...(...))(...) str(...)
    :return: [str,'',str,'','',str,'',], [...,(...(...)),(...),(...)]
    '''
    l, i = len(one_axiom), 0
    result_str, result, type_1 = '', [], 'outside'
    while i < l:
        if type_1 == 'outside':
            if one_axiom[i] == '(':
                type_1 = 'inside'
                i += 1
            else:
                result_str += one_axiom[i]
                i += 1
        else:
            count, count_term_1, start_id = 0, 1, i
            while i < l:
                if one_axiom[i] == '(':
                    count_term_1 += 1
                elif one_axiom[i] == ')':
                    count_term_1 -= 1
                    if count_term_1 == 0:
                        result.append(one_axiom[start_id:i])
                        result_str += '*'
                        i += 1
                        type_1 = 'outside'
                        break
                i += 1
    return result_str.split('*'), result


def renew_tuple(K, B):
    if B in K:
        return K
    else:
        K_new = list(K)
        K_new.append(B)
        return tuple(sorted(K_new))


def clause2axiom(clause):
    result = '(implies '
    if clause[0] == 'H2rK':
        if len(clause[1]) == 1:
            result += clause[1][0] + ' '
        else:
            result += f'(and {",".join(clause[1])}) '

        result += f'(some {clause[2]} '

        if len(clause[3]) == 1:
            result += clause[3][0] + '))'
        else:
            result += f'(and {",".join(clause[1])})))'
        return result

    elif clause[0] == 'H2A':
        if len(clause[1]) == 1:
            result += clause[1][0] + ' '
        else:
            result += f'(and {",".join(clause[1])}) '

        result += clause[2] + ')'
        return result
    else:
        print(clause)
        return False


class Ontology:
    def __init__(self, name_ontology, normalized=False):
        self.axioms, self.axioms_RI, self.axioms_RC, self.concepts, self.relations = {}, {}, {}, set([]), set([])
        # RI for role inclusion, RC for role chain
        self.axioms_normalized, self.mapback, self.normalize_dic = {}, {}, {}
        self.num_axiom, self.num_axiom_normalized, self.new_normalize_concepts, self.current_axiom = 0, 0, 0, 0
        print('loading ontology:')
        #with open(f'workspace/{name_ontology}/{name_ontology}.owl', 'r') as f:
        with open(f'Ontologies-Less-Than-10000/{name_ontology}.owl', 'r') as f:
            data = f.readlines()
            for line in tqdm(data):
                self.renew(line)
        if not normalized:
            self.normalize()
        self.save(name_ontology)

    def save(self, name_ontology):
        #path = f'workspace/{name_ontology}/data/'
        path = f'result-Ontologies-Less-Than-10000/{name_ontology}/data/'
        mkdir(path)
        jsobj1 = json.dumps(self.axioms_RI)
        fileObject1 = open(f'{path}role_inclusion.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()

        jsobj1 = json.dumps(self.axioms_RC)
        fileObject1 = open(f'{path}role_chain.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()

        jsobj1 = json.dumps(self.axioms)
        fileObject1 = open(f'{path}axioms.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()

        jsobj1 = json.dumps(self.axioms_normalized)
        fileObject1 = open(f'{path}axioms_normalized.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()

        jsobj1 = json.dumps(self.mapback)
        fileObject1 = open(f'{path}mapback.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()
        return

    def renew(self, line):
        if line[0] == 'D':  # Declaration()
            if line[12] == 'C':  # Class
                self.concepts.add(line.split('<', 1)[1][:-3])
            elif line[12] == 'O':  # Object
                self.relations.add(line.split('<', 1)[1][:-3])
        elif line[0] == 'E' or line[0] == 'S':  # Equivalence() or Sub...()
            if 'Property' in line:
                if 'Chain' in line:
                    self.axioms_RC[line[:-1]] = self.num_axiom
                else:
                    self.axioms_RI[line[:-1]] = self.num_axiom
                '''
                tuple_roles = formal_form(line)
                if 'Chain' in line:
                    self.axioms_RC[tuple_roles] = self.num_axiom
                else:
                    self.axioms_RI[tuple_roles] = self.num_axiom
                '''
            else:
                line_other_form = line.replace('SubClassOf(', '(implies ').replace('EquivalentClasses(',
                                                                                   '(equivalent ').replace(
                    'ObjectSomeValuesFrom(', '(some ').replace('ObjectIntersectionOf(', '(and ').replace(
                    'ObjectAllValuesFrom(', '(all').replace('owl:Thing', '<owl:Thing>').replace('owl:Nothing', '<owl:Nothing>')
                self.axioms[line_other_form[:-1]] = self.num_axiom
            self.num_axiom += 1

    # find all the existing definition (equivalence ... ) avoid to add this defi again when normalize the ontology.
    def preprocess(self):
        for axiom in self.axioms:
            if axiom[1] == 'e':
                # not depth_bigger_than(one_axiom, 2) means the axioms contain at most one "some" or "and"
                if len(axiom.split('(')) > 2 and not depth_bigger_than(axiom, 2):
                    # get the item **** inside (equivalent\implies <#...> (****) )
                    def_terms = formal_form(axiom.split('(')[-1].split(')')[0])
                    defined_term = axiom.split(' ')[1]
                    if def_terms not in self.normalize_dic.keys():
                        self.mapback[def_terms] = self.axioms[axiom]
                        self.normalize_dic[def_terms] = defined_term

    def normalize_one_term_begin(self, axiom):
        if depth_bigger_than(axiom, 2):
            # get the item **** inside (equi\implies <#...> (****) )
            axiom_str_rest, axiom_cutted = cut_axiom(axiom[1:-1])
            result = axiom_str_rest[0]
            assert len(axiom_cutted) <= 2
            for i, one_axiom_cutted in enumerate(axiom_cutted):
                if len(result.split('<')) >= 2:
                    k = 2
                    result += '('
                else:
                    k = 1
                while depth_bigger_than(one_axiom_cutted, k):
                    one_axiom_cutted = self.normalize_one_term_middle(one_axiom_cutted)
                result += one_axiom_cutted
                if k == 2:
                    result += ')'
                result += axiom_str_rest[i + 1]
            return '(' + result + ')'
        else:
            return axiom

    def normalize_one_term_middle(self, part_axiom):
        if depth_bigger_than(part_axiom, 2):
            axiom_str_rest, axiom_cutted = cut_axiom(part_axiom)
            result = axiom_str_rest[0]
            for i, one_axiom_cutted in enumerate(axiom_cutted):
                while depth_bigger_than(one_axiom_cutted, 1):
                    one_axiom_cutted = self.normalize_one_term_middle(one_axiom_cutted)
                result += one_axiom_cutted
                result += axiom_str_rest[i + 1]
            return result
        else:
            one_axiom_form = formal_form(part_axiom)
            if one_axiom_form not in self.normalize_dic.keys():
                new_normalized_concept = f'#N{self.new_normalize_concepts}'
                self.new_normalize_concepts += 1
                self.concepts.add(new_normalized_concept)
                self.normalize_dic[one_axiom_form] = new_normalized_concept

                self.axioms_normalized[
                    f'(equivalent <#N{self.new_normalize_concepts}> (' + part_axiom + '))'] = self.num_axiom_normalized
                self.num_axiom_normalized += 1

            return self.normalize_dic[one_axiom_form]

    def normalize(self):
        # self.preprocess()
        for axiom in self.axioms:
            self.axioms_normalized[self.normalize_one_term_begin(axiom)] = self.num_axiom_normalized
            self.mapback[self.num_axiom_normalized] = self.axioms[axiom]
            self.num_axiom_normalized += 1
        print(f'length of ontology, normalization ontology: {len(self.axioms_normalized)}, {self.num_axiom_normalized}')

    def len(self):
        return len(self.axioms_normalized) + len(self.axioms_RC) + len(self.axioms_RI)


# return A, (...,B,...) for input axioms (equi/sub A ... B ...))


class saturate:
    def __init__(self, name_ontology, normalized=False):
        self.ontology = Ontology(name_ontology, normalized)

        self.initial_pool = saturate_pools()
        self.ontology_pool = saturate_ini_pools()
        self.processed_pool = saturate_process_pools()

        # self.ind = self.ontology.len()
        self.ind = 0
        self.ontology_len = self.ontology.len()
        self.clause2ind = {}
        # self.id_axioms2ind = {}
        self.saturate_progress = {}
        #self.savepath = f'workspace/{name_ontology}/data/'
        self.savepath = f'result-Ontologies-Less-Than-10000/{name_ontology}/data/'
        self.initial()

    def initial(self):
        for axiom in self.ontology.axioms_normalized:
            clauses = self.initial_pool.add(axiom)
            for clause in clauses:
                self.add_new_clause(clause, type='fix')

            clauses1 = self.ontology_pool.add(axiom)
            for clause in clauses1:
                self.add_new_clause(clause, type='fix')
            self.clause2ind[('original', axiom)] = self.ind
            print(self.ind)
            self.ind += 1

        for axiom in self.ontology.axioms_RC:
            clause = self.ontology_pool.add_role_axioms(axiom)
            self.clause2ind[clause] = self.ind
            self.clause2ind[('original', axiom)] = self.ind
            self.ind += 1

        for axiom in self.ontology.axioms_RI:
            clause = self.ontology_pool.add_role_axioms(axiom)
            self.clause2ind[clause] = self.ind
            self.clause2ind[('original', axiom)] = self.ind
            self.ind += 1

    def record_saturate_process(self, pre, con):
        pre = list(pre)
        if con in self.saturate_progress:
            self.saturate_progress[con].append(pre)
        else:
            self.saturate_progress[con] = [pre]

    def one_turn_H2A(self):
        if not self.initial_pool.H2A:
            return False
        H = sample(self.initial_pool.H2A.keys(), 1)[0]
        A = self.initial_pool.H2A[H].pop()
        if not self.initial_pool.H2A[H]:
            del self.initial_pool.H2A[H]
        ind_HA = self.clause2ind[('H2A', H, A)]

        # (H, A)   (A,B) --> (H, B).
        B_list = self.ontology_pool.A2B.get(A)
        if B_list:
            for B in B_list:
                clause = ('H2A', H, B)
                self.add_new_clause(clause)
                pre = {ind_HA, self.clause2ind[clause]}
                self.record_saturate_process(pre, self.clause2ind[clause])

        # (H, A),(H, A1),...,(H,An)    ({A,...Ai...},{B}) --> (H, B). (H, Ai) in processed_pool
        Ai_set_list = self.ontology_pool.A2Ai.get(A)
        Ai_avaliable = deepcopy(self.processed_pool.H2A.get(H))
        if Ai_set_list and Ai_avaliable:
            Ai_avaliable.update(H)  # in case (A1, A1),...,(A1,An)    ({...Ai...},{B})  to (A1, B)
            for Ai_set in Ai_set_list:
                for Ai in Ai_set:
                    if Ai != A and Ai not in Ai_avaliable:
                        break
                else:
                    for B in self.ontology_pool.Ai2B[Ai_set]:
                        clause = ('H2A', H, B)
                        self.add_new_clause(clause)
                        pre = {self.clause2ind[('H2A', H, Ai_new)] for Ai_new in Ai_set}
                        pre.add(self.clause2ind[('Ai2B', Ai_set, B)])
                        self.record_saturate_process(pre, self.clause2ind[clause])

        # (H, A)    (A, rB) --> (H, r, B)
        rB_dic = self.ontology_pool.A2rB.get(A)
        if rB_dic:
            for r in rB_dic:
                for B in rB_dic[r]:
                    clause = ('H2rK', H, r, (B,))
                    self.add_new_clause(clause)
                    pre = {self.clause2ind[('A2rB', A, r, B)], ind_HA}
                    self.record_saturate_process(pre, self.clause2ind[clause])

        # (H1, r, H), (H, A)    (rA, B) --> (H1, B)
        r2H1_dic = self.processed_pool.K2rH.get(H)
        r2A_dic = self.ontology_pool.B2rA.get(A)
        if r2H1_dic and r2A_dic:
            for r in r2H1_dic.keys() & r2A_dic.keys():
                for H1, B in product(r2H1_dic[r], r2A_dic[r]):
                    clause = ('H2A', H1, B)
                    self.add_new_clause(clause)
                    pre = {ind_HA, self.clause2ind[('H2rK', H1, r, H)], self.clause2ind[('B2rA', A, r, B)]}
                    self.record_saturate_process(pre, self.clause2ind[clause])

        # (H, r, K), (H, A)    (A, \forall rB) --> (H, r, K\cap B)
        r2K_dic = self.processed_pool.H2rK
        universal_r2B_dic = self.ontology_pool.A2rB_universal.get(A)
        if universal_r2B_dic and r2K_dic:
            for r in universal_r2B_dic.keys() & r2K_dic.keys():
                for K, B in product(r2K_dic[r], universal_r2B_dic[r]):
                    K_new = renew_tuple(K, B)
                    clause = ('H2rK', H, r, K_new)
                    self.add_new_clause(clause)
                    pre = {ind_HA, self.clause2ind[('H2rK', H, r, K)], self.clause2ind[('A2rB_universal', A, r, B)]}
                    self.record_saturate_process(pre, self.clause2ind[clause])

        clause = ('H2A', H, A)
        self.processed_pool.add_clause(clause)
        return True

    def one_turn_H2rK(self):
        # {H:{r:[K1,..,K_n],...}, ...}
        if not self.initial_pool.H2rK:
            return False
        H = sample(self.initial_pool.H2rK.keys(), 1)[0]
        r = sample(self.initial_pool.H2rK[H].keys(), 1)[0]
        K = self.initial_pool.H2rK[H][r].pop()
        if not self.initial_pool.H2rK[H][r]:
            del self.initial_pool.H2rK[H][r]
            if not self.initial_pool.H2rK[H]:
                del self.initial_pool.H2rK[H]
        ind_HrK = self.clause2ind[('H2rK', H, r, K)]

        # (H, r, K), (K, A)    (rA, B) --> (H, B)
        A_list = self.processed_pool.H2A.get(K)
        if not A_list:
            A_list = K
        else:
            A_list.update(K)
        for A in A_list:
            r2B_dic = self.ontology_pool.B2rA.get(A)
            if r2B_dic:
                B_list = r2B_dic.get(r)
                if B_list:
                    for B in B_list:
                        clause = ('H2A', H, B)
                        self.add_new_clause(clause)
                        if A in K:
                            pre = {ind_HrK, self.clause2ind[('B2rA', A, r, B)]}
                        else:
                            pre = {ind_HrK, self.clause2ind[('H2A', K, A)], self.clause2ind[('B2rA', A, r, B)]}
                        self.record_saturate_process(pre, self.clause2ind[clause])

        # or (H, r, K), (H, A)    (A, \forall r.B) --> (H, r, K\cap B)
        A_new_list = self.processed_pool.H2A.get(H)
        if not A_new_list:
            A_new_list = H
        else:
            A_new_list.update(H)
        for A in A_new_list:
            r2B_universal_dic = self.ontology_pool.A2rB_universal.get(A)
            if r2B_universal_dic:
                B_universal_list = r2B_universal_dic.get(r)
                if B_universal_list:
                    for B_universal in B_universal_list:
                        K_new = renew_tuple(K, B_universal)
                        clause = ('H2rK', H, r, K_new)
                        self.add_new_clause(clause)
                        if A in H:
                            pre = {ind_HrK, self.clause2ind[('A2rB_universal', A, r, B_universal)]}
                        else:
                            pre = {ind_HrK, self.clause2ind[('H2A', H, A)],
                                   self.clause2ind[('A2rB_universal', A, r, B_universal)]}
                        self.record_saturate_process(pre, self.clause2ind[clause])

        # ......  +  role axioms --> conclusion
        if len(H) == 1 and len(K) == 1:
            # (A, r, B)...    r\sqsubseteq s to (A, s, B)
            r_tuple = (r,)
            s_list = self.ontology_pool.ri2r.get(r_tuple)
            if s_list:
                for s in s_list:
                    clause = ('H2rK', H, s, K)
                    self.add_new_clause(clause)
                    pre = {ind_HrK, self.clause2ind[('ri2r', r_tuple, s)]}
                    self.record_saturate_process(pre, self.clause2ind[clause])

            r_squence_list = self.ontology_pool.r2ri.get(r)
            if r_squence_list:
                for r_sequence in r_squence_list:
                    # (A_0, r, A_1), (A_1, s, A_2)   r\circ s\sqsubseteq t --> (A_0, t, A_2)
                    if r_sequence[0] == r:
                        r2K_dic = self.processed_pool.H2rK.get(K)
                        if r2K_dic and r_sequence[1] in r2K_dic:
                            A2_tuple_list = r2K_dic[r_sequence[1]]
                            for A2_tuple in A2_tuple_list:
                                for t in self.ontology_pool.ri2r[r_sequence]:
                                    clause = ('H2rK', H, t, A2_tuple)
                                    self.add_new_clause(clause)
                                    pre = {ind_HrK, self.clause2ind[('ri2r', r_sequence, t)],
                                           self.clause2ind[('H2rK', K, r_sequence[1], A2_tuple)]}
                                    self.record_saturate_process(pre, self.clause2ind[clause])
                    else:
                        # (A_0, s, A_1), (A_1, r, A_2)   s\circ r\sqsubseteq t --> (A_0, t, A_2)
                        assert r_sequence[1] == r
                        s2A0_dic = self.processed_pool.K2rH.get(H)
                        if s2A0_dic and r_sequence[0] in s2A0_dic:
                            A0_tuple_list = s2A0_dic[r_sequence[0]]
                            for A0_tuple in A0_tuple_list:
                                for t in self.ontology_pool.ri2r[r_sequence]:
                                    clause = ('H2rK', A0_tuple, t, K)
                                    self.add_new_clause(clause)
                                    pre = {ind_HrK, self.clause2ind[('ri2r', r_sequence, t)],
                                           self.clause2ind[('H2rK', A0_tuple, r_sequence[0], H)]}
                                    self.record_saturate_process(pre, self.clause2ind[clause])

        clause = ('H2rK', H, r, K)
        self.processed_pool.add_clause(clause)
        return True

    def run(self):
        while True:
            a = randint(0, 1)
            if a == 0:
                f = self.one_turn_H2A()
                if not f:
                    f1 = self.one_turn_H2rK()
                    if not f1:
                        break
            else:
                f = self.one_turn_H2rK()
                if not f:
                    f1 = self.one_turn_H2A()
                    if not f1:
                        break
        self.save()

    def add_new_clause(self, clause, type='non-fix'):
        if clause not in self.clause2ind:
            _ = self.initial_pool.add_clause(clause)
            self.clause2ind[clause] = self.ind
            if type == 'non-fix':
                self.ind += 1

    def save(self):
        mkdir(self.savepath)
        jsobj1 = json.dumps(self.saturate_progress)
        fileObject1 = open(f'{self.savepath}saturate_progress.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()

        with open(f'{self.savepath}clause2ind.txt', 'w') as f:
            f.write('original ontologies(normalized):\n')
            for clause, id_clause in self.clause2ind.items():
                if clause[0] == 'original':
                    f.write(f"{id_clause}-{clause[1]}\n")
            f.write('\n####################################\n')
            for clause, id_clause in self.clause2ind.items():
                if clause[0] != 'original':
                    if id_clause >= self.ontology_len:
                        clause_axiom_form = clause2axiom(clause)
                        if clause_axiom_form:
                            f.write(f"{id_clause}-{clause_axiom_form}\n")
                    #else:
                        #print(clause, id_clause, self.ontology_len)
        return


def test(a):
    if a == 0:
        goplus = Ontology('go-plus')
    elif a == 1:
        A = saturate_ini_pools()
        A.add('(implies <A> (some <r> <B>))')
        A.add('(equivalent <A> (and <B1> <B2> <B3>))')
        A.add('(implies <A> (all <r> <B1>))')
        A.add('(equivalence <A> (some <s> <B>))')
        A.add_role_axioms('(implies <r> <s>)')
        A.add_role_axioms('(implies (chain <r> <s>) <t>)')
        print(A.A2B, A.A2rB, A.B2rA, A.A2rB_universal, A.A2Ai, A.Ai2B, A.ri2r, A.r2ri)

    elif a == 2:
        A = saturate_pools()
        A.add('(implies <A> (some <r> <B>))')
        A.add('(equivalent <A> (and <B1> <B2> <B3>))')
        A.add('(implies <A> (all <r> <B1>))')
        A.add('(equivalence <A> (some <s> <B>))')
        print(A.H2rK, A.H2A)

    elif a == 3:
        A = saturate_process_pools()
        A.add('(implies <A> (some <r> <B>))')
        A.add('(equivalent <A> (and <B1> <B2> <B3>))')
        A.add('(implies <A> (all <r> <B1>))')
        A.add('(equivalence <A> (some <s> <B>))')
        print(A.K2rH, A.H2A)


def test_saturate():
    S = saturate('ore_ont_1967')
    print(S.ontology_pool.A2rB, S.ontology_pool.r2ri)
    S.run()


test_saturate()
