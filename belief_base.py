from __future__ import print_function
import copy
import itertools
from checkable_queue import CheckableQueue
from convert2CNF import convert2CNF
from globals import *

class Clause:
    def __init__(self, c=""):
        c1 = c.replace(OR, "")
        self.positives = []
        self.negatives = []

        while c1 != "":
            if c1[0] == NOT: # find all negations
                # add symbol corresponding to the negation to negatives
                self.negatives.append(c1[1])
                # remove negations and corresponding symbol from b
                c1 = c1.replace(c1[0:2], "", 1)
            else:
                # add first symbol to positives
                self.positives.append(c1[0])
                # remove first symbol from
                c1 = c1.replace(c1[0], "", 1)

    def __eq__(self, other):
        if len(self.positives) != len(other.positives) or len(self.negatives) != len(other.negatives):
            return False
        for symbol1 in self.positives: # ensure each positive symbol has a match
            match = False
            for symbol2 in other.positives:
                if symbol1 == symbol2:
                    match = True
                    break
            if match == False:
                return False
        for symbol1 in self.negatives: # ensure each negative symbol has a match
            match = False
            for symbol2 in other.negatives:
                if symbol1 == symbol2:
                    match = True
                    break
            if match == False:
                return False
        return True

    def __ne__(self, other):
        return not self.__eq__(other)

    def __str__(self):
        s = ""
        for symbol in self.positives:
            s += symbol + OR
        for symbol in self.negatives:
            s += NOT + symbol + OR
        s = s[:len(s)-1]
        return s

    def del_positive_symbol(self, s):
        self.positives.remove(s)

    def del_negative_symbol(self, s):
        self.negatives.remove(s)

    def isEmpty(self):
        if len(self.positives) == 0 and len(self.negatives) == 0:
            return True
        return False

    @staticmethod
    def combine_clauses(c1, c2):
        result = Clause()
        result.positives.extend(c1.positives)
        result.positives.extend(c2.positives)
        result.negatives.extend(c1.negatives)
        result.negatives.extend(c2.negatives)
        return result

    @staticmethod
    def copy(c):
        result = Clause()
        for symbol in c.positives:
            result.positives.append(symbol)
        for symbol in c.negatives:
            result.negatives.append(symbol)
        return result

    @staticmethod
    def negate_clause(c):
        new_clauses = []
        for symbol in c.positives:
            new_c = Clause('~'+symbol)
            new_clauses.append(new_c)
        for symbol in c.negatives:
            new_c = Clause(symbol)
            new_clauses.append(new_c)
        return new_clauses

    @staticmethod
    def resolve(c1, c2):
        c1_copy = Clause.copy(c1)
        c2_copy = Clause.copy(c2)

        # find and remove all complements
        for c1_symbol in c1_copy.positives:
            for c2_symbol in c2_copy.negatives:
                # if the symbols match, remove the symbols from c1 and c2
                if c1_symbol == c2_symbol and c1_symbol in c1_copy.positives:
                    c1_copy.del_positive_symbol(c1_symbol)
                    c2_copy.del_negative_symbol(c2_symbol)
        for c2_symbol in c2_copy.positives:
            for c1_symbol in c1_copy.negatives:
                # if the symbols match, remove the symbols from c1 and c2
                if c2_symbol == c1_symbol and c2_symbol in c2_copy.positives:
                    c1_copy.del_negative_symbol(c1_symbol)
                    c2_copy.del_positive_symbol(c2_symbol)

        # remove redundant symbols
        for c1_symbol in c1_copy.positives:
            for c2_symbol in c2_copy.positives:
                # if the symbols match, remove the symbol from c2
                if c1_symbol == c2_symbol and c1_symbol in c1_copy.positives:
                    c2_copy.del_positive_symbol(c2_symbol)
        for c1_symbol in c1_copy.negatives:
            for c2_symbol in c2_copy.negatives:
                # if the symbols match, remove the symbol from c2
                if c1_symbol == c2_symbol and c1_symbol in c1_copy.negatives:
                    c2_copy.del_negative_symbol(c2_symbol)

        resolvent = Clause.combine_clauses(c1_copy, c2_copy)

        # return the resolvent
        return resolvent

class Belief:
    def __init__(self, cnf, negate=False):
        cnf = cnf.replace(" ", "")
        cnf = cnf.replace("~~", "") # eliminate any double negations
        self.clauses = []
        self.entrenchment = 1

        if negate == False:
            idx = cnf.find(AND)
            while idx > -1:
                c = cnf[:idx]
                cnf = cnf[idx+1:]
                c = c.replace("(", "")
                c = c.replace(")", "")
                clause = Clause(c)
                self.clauses.append(clause)
                idx = cnf.find(AND)
            c = cnf
            c = c.replace("(", "")
            c = c.replace(")", "")
            clause = Clause(c)
            self.clauses.append(clause)

        else:
            temp_clauses = []
            idx = cnf.find(AND)
            while idx > -1:
                c = cnf[:idx]
                cnf = cnf[idx+1:]
                c = c.replace("(", "")
                c = c.replace(")", "")
                clause = Clause(c)
                temp_clauses.append(clause)
                idx = cnf.find(AND)
            c = cnf
            c = c.replace("(", "")
            c = c.replace(")", "")
            clause = Clause(c)
            temp_clauses.append(clause)

            # negate each clause
            negated_clauses = []
            for c in temp_clauses:
                result = Clause.negate_clause(c)
                negated_clauses.append(result)

            # distribute to return to cnf
            while(len(negated_clauses) > 1):
                clause_set1 = negated_clauses[0]
                clause_set2 = negated_clauses[1]
                new_clauses = []
                for c1 in clause_set1:
                    for c2 in clause_set2:
                        new_c = Clause.combine_clauses(c1, c2)
                        new_clauses.append(new_c)
                negated_clauses[0] = new_clauses
                del(negated_clauses[1])

            for c in negated_clauses[0]:
                self.clauses.append(c)

    def __eq__(self, item):
        if len(self.clauses) != len(item.clauses):
            return False
        differences = copy.copy(self.clauses)
        for selfclause in self.clauses:
            for itemclause in item.clauses:
                if selfclause == itemclause:
                    differences.remove(selfclause)
        return len(differences) == 0

    def __ne__(self, item):
        return not self.__eq__(item)

    def __str__(self):
        total_str = ''
        for c in self.clauses:
            clause = '(' + str(c) + ")^"
            total_str += clause
        total_str = total_str[:len(total_str)-1]
        return total_str

class BeliefBase:
    hashnum = 0
    def __init__(self):
        self.beliefs = []
        BeliefBase.hashnum += 1

    def __eq__(self, item):
        if len(item.beliefs) != len(self.beliefs):
            return False
        for belief1 in self.beliefs:
            match = False
            for belief2 in item.beliefs:
                if belief1 == belief2:
                    match = True
                    break
            if match == False:
                return False
        return True

    def __ne__(self, item):
        return not self.__eq__(item)

    def __hash__(self):
        return BeliefBase.hashnum

    def __str__(self):
        if len(self.beliefs) != 0:
            out = '{'
            for ele in self.beliefs:
                out = out + str(ele) + ', '
            return out[:len(out)-2] + '}'
        return '{}'

    def add_belief(self, b):
        self.beliefs.append(b)

    def del_belief(self, b):
        for belief in self.beliefs:
            same_belief = True
            for c1,c2 in zip(belief.clauses,b.clauses):
                if c1 != c2:
                    same_belief = False
            if same_belief:
                self.beliefs.remove(belief)

    def clear_beliefs(self):
        self.beliefs = []

    @staticmethod
    def intersect(belief_bases):
        inter_b = BeliefBase()
        if len(belief_bases) > 0:
            if len(belief_bases) == 1:
                return belief_bases[0]
            start_b = belief_bases[0]
            for bb in belief_bases[1:]:
                for belief1 in start_b.beliefs:
                    for belief2 in bb.beliefs:
                        if belief1 == belief2:
                            inter_b.add_belief(belief1)
        return inter_b

    def entails(self, belief):
        # método que verifica si la base de creencias implica b usando resolución
        new_b = Belief(belief, True) # crear negación de la creencia

        # crea una lista conteniendo todas las  clausulas en  KB ^ ~belief
        all_clauses = []
        resolved_clauses = []
        all_clauses.extend(new_b.clauses)
        for b in self.beliefs:
            all_clauses.extend(b.clauses)

        clause_added = True
        while(clause_added): # bucle hasta que ya no se pueda agregar una cláusula
            clause_added = False
            for c1 in all_clauses:
                for c2 in all_clauses:
                    if c1 != c2 and (c1,c2) not in resolved_clauses:
                    # si c1 y c2 no son iguales y aún no se han resuelto
                        result = Clause.resolve(c1, c2) # resuelve c1 y c2
                        if result.isEmpty(): # if the resolvent is empty
                            return True # then the KB entails the belief

                        # add resolvent if it is unique
                        add_clause = True
                        for c3 in all_clauses:
                            if result == c3:
                                add_clause = False
                        if add_clause:
                            clause_added = True
                            all_clauses.append(result)
                            resolved_clauses.append((c1,c2))
        return False


    def contract(self, b, mode='partial-meet'):
        remainders = self.remainders(b)
        if mode == 'partial-meet':
            self.beliefs = self.partial_meet(remainders)
        elif mode == 'full-meet':
            self.beliefs = BeliefBase.intersect(remainders).beliefs
        elif mode == 'maxichoice':
            self.beliefs = remainders[0].beliefs
        else:
            raise ValueError("Invalid mode argument")

    def selection(self):
        # Asignar valores de atrincheramiento a las creencias.
        for i in range(0,len(self.beliefs)):
            for j in range(i,len(self.beliefs)):
                if i != j:
                    bi = BeliefBase()
                    bi.add_belief(self.beliefs[i])
                    bj = BeliefBase()
                    bj.add_belief(self.beliefs[j])
                    if bi.entails(str(self.beliefs[j])):
                        self.beliefs[j].entrenchment += 1
                    if bj.entails(str(self.beliefs[i])):
                        self.beliefs[i].entrenchment += 1
                    if bi.contained_by(self.beliefs[j]):
                        self.beliefs[j].entrenchment += 1
                    if bj.contained_by(self.beliefs[i]):
                        self.beliefs[i].entrenchment += 1
        # valor de atrincheramiento cuadrado para poner más valor en atrincheramientos más profundos
        for belief in self.beliefs:
            belief.entrenchment = belief.entrenchment**2


    # retorna verdadero si  self = p y  belief = p^q, falso de otra forma
    # diseñado para ser llamado cuando uno mismo tiene una creencia
    def contained_by(self, belief):
        count = len(self.beliefs[0].clauses)
        for c in belief.clauses:
            if c in self.beliefs[0].clauses:
                count -= 1
        if count == 0:
            return True
        return False

    def partial_meet(self, remainders):
        self.selection()
        candidates = []
        for length in range(0, len(remainders)+1):
            for subset in itertools.combinations(remainders, length):
                candidates.append(BeliefBase.intersect(subset))
        def sum_entrenchment(i):
            ret = 0
            for b in i.beliefs:
                ret += b.entrenchment
            return ret
        # retorno máximo valor de atrincheramiento intersección
        return max(candidates, key=sum_entrenchment).beliefs

    def remainders(self, b):
        '''Devuelve los residuos máximos de inclusión al introducir la creencia b en la base de creencias.

        Backward Clause Selection - implemented using BFS
        '''
        frontier = CheckableQueue()
        expanded = CheckableQueue()
        frontier.put(self)
        remainders = []
        inclusion_max = 0
        while True:
            if frontier.empty():
                return remainders
            n = frontier.get()
            expanded.put(n)
            if not n.entails(str(b)) and n not in remainders:
                # Asegúrese de que solo se devuelvan los restos de longitud máxima
                if inclusion_max > 0:
                    if len(n.beliefs) == inclusion_max:
                        remainders.append(n)
                else:
                    inclusion_max = len(n.beliefs)
                    remainders.append(n)
            for belief in n.beliefs:
                n_copy = copy.deepcopy(n)
                n_copy.del_belief(belief)
                if n_copy not in frontier and n_copy not in expanded and inclusion_max == 0:
                    frontier.put(n_copy)

    def revise(self, b, mode='partial-meet'):
        b_not = Belief(str(b),negate=True)
        self.contract(b_not, mode)
        self.add_belief(b)
