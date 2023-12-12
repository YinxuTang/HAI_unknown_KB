from networkx.drawing.nx_pydot import graphviz_layout
from pysat.examples.lbx import LBX
from pysat.solvers import Solver
from pysat.examples.hitman import Hitman
from pysat.formula import WCNF, CNF
from pysat.examples.musx import MUSX
from collections import defaultdict
from copy import deepcopy
import itertools
import networkx as nx
from algorithms import *

'----------------------------------------------------------------------------------------------------------------------'

def skeptical_entailment(KB, seed, q):
	# Check if KB entails a query

	s = Solver(name='g4')
	for k in KB:
		s.add_clause(k)
	for k in seed:
		s.add_clause(k)
	# add negation of query
	s.append_formula(q.negate().clauses)
	if s.solve() == False:
		return True
	else: return False

def sat(KB_clauses, seed):
	# Check if a formula is satisfiable
	s = Solver(name='g4')
	for k in KB_clauses:
		s.add_clause(k)

	for k in seed:
		s.add_clause(k)

	if s.solve():
		return True
	else:
		return False



class Agent():
    def __init__(self, KB, id):
        self.id = id
        self.kb_own = deepcopy(KB)
        self.commit_store_args = defaultdict(list)
        self.commit_store_other = defaultdict(list)
        self.arguments = []
        self.is_human = False
        self.attacked_args = []

    def acquire_knowledge(self, arg):
        #When seeing information that is not unsat with KB_own, to add to knowledge
        #TODO
        return

    def update_KB_other(self, arg):
        #When receiving argument, to update other agent's model
        # self.kb_other.append(arg)
        return 

    def store_commit(self, arg, t, other=False):
        if other:
            self.commit_store_other[t].append(arg)
        else:
            self.commit_store_args[t].append(arg)

class Human(Agent):
    def __init__(self, KB, id):
        super().__init__(KB, id)
        self.hard_constraints = []
        self.kb_own = deepcopy(KB)

        self.commit_store_args = defaultdict(list)
        self.commit_store_other = defaultdict(list)
        self.arguments = []
        self.is_human = True
        self.attacked_args = []

    def acquire_knowledge(self, arg):
        #When seeing information that is not unsat with KB_own, to add to knowledge
        #TODO
        #Make the added constraints hard
        #Update the KB_own
        if arg is None:
            return
        self.hard_constraints.extend(arg)
        sol = sat(self.kb_own, arg)
        if not sol:
            MCS = get_MCS(self.kb_own, arg, self.hard_constraints)
            print("Removing MCS: ", MCS)
            print("Current KB: ", self.kb_own)
            for mcs_ in MCS:
                if mcs_ in self.hard_constraints:
                    print("MCS: ", mcs_)
                    print("Hard constraints: ", self.hard_constraints)
                    print("ERROR: MCS has a hard constraint!")
                    exit()
                self.kb_own.remove(mcs_)
        for c in arg:
            if c not in self.kb_own:
                self.kb_own.append(c)
        print("New KB: ", self.kb_own)
        print("*******************")

def unique_combinations(input_list, combo_length, checked_list):
    # Generate all possible combinations
    all_combinations = list(itertools.combinations(input_list, combo_length))
    
    # Filter out combinations that are already in the checked list
    unique_combinations = [list(combo) for combo in all_combinations if combo not in checked_list]
    
    return unique_combinations


def get_MCS(KB, arg, hard_constraints):
    # Compute minimal hitting set
    wcnf = WCNF()
    for c in KB:
        if c in hard_constraints:
            wcnf.append(c)
        else:
            wcnf.append(c, weight=1)
    for c in arg: # add clauses in the arg as hard
        wcnf.append(c)

    lbx = LBX(wcnf, use_cld=True, solver_name='g3')
    # Compute mcs and return the clauses indexes
    mcs = lbx.compute()
    return [list(wcnf.soft[m - 1]) for m in mcs]


def arg_sim(KBa, KBh, e, threshold):
	T = nx.DiGraph()  # argumentation tree
	T.add_node(str(e)+'_agent')
	T.nodes[str(e)+'_agent']['support'] = e
	commit_storeA = [e]
	commit_storeH = []
	# ArgsH = []
	ArgsA = [e]
	while True:
		if not SAT([k for k in KBh if k not in commit_storeH], ArgsA):
			T, ArgsH = getArgs(KBh, commit_storeH, ArgsA, T, threshold, '_agent', '_human')
			if not SAT([k for k in KBa if k not in commit_storeA], ArgsH):
				T, ArgsA = getArgs(KBa, commit_storeA, ArgsH, T, threshold, '_human', '_agent')
			else: return T
		else: return T



def flatten_list(the_lists):
	result = []
	for _list in the_lists:
		result += _list
	return result

def is_subset(list1, list2):
    set1 = set(tuple(x) for x in list1)
    set2 = set(tuple(x) for x in list2)
    return set2.issubset(set1)


# think of adding rebuttals by adding claims into the arguments
def getArgs(time, pri, sec, T, arg_tree = False):
    
    times = sorted(sec.commit_store_args.keys(), reverse=True)

    for t in times:
        arg = sec.commit_store_args[t][0]
        if arg is None:
            continue
        # check for each clause in the argument (extend to combinations later). It means that we only do refutations (not rebuttals!!)
        new_args = [a for a in arg if a not in pri.attacked_args]
        # new_args = unique_combinations(arg, len(arg), pri.attacked_args)

        for a in new_args: 
           
            pri.attacked_args.append(a)
            if not sat(pri.kb_own, [a]):
                wcnf = WCNF()
                wcnf.extend(pri.kb_own, weights=[1 for i in range(len(pri.kb_own))])
                wcnf.append(a, weight=1)
                # wcnf.extend(a, weights=[1 for i in range(len(a))])
                with OptUx(wcnf) as optux:
                    for en in optux.enumerate():
                        mus =[list(wcnf.soft[e - 1]) for e in en]
                        counter = [m for m in mus if m not in arg]
            
                        # if all(len(c)==1 for c in counter):
                            # continue
                        # if len(counter) == 1:
                            # continue

                        if not any(is_subset(i, counter)  for i in pri.arguments):
                            # print(counter, 'new counter')
                            pri.commit_store_args[time].append(counter)
                            pri.arguments.append(counter)
                            # print("attacking: ", t)
                            if arg_tree:
                                T.add_edge(str(arg)+'_'+sec.id, str(counter)+'_'+pri.id)
                                T.nodes[str(counter)+'_'+pri.id]['support'] = counter
                            return counter
                        
                        
        
    pri.commit_store_args[time].append(None)
    return None


def update_tree(arg, counter, T, name1, name2):
    T.add_edge(str(arg)+str(name1), str(counter)+str(name2))
    T.nodes[str(counter)+str(name2)]['support'] = counter
    return T


def arg_step_ATD(time, pri, sec, T):
   
    counter, unsat, arg = getArgs(time, pri, sec)
    
    T = update_tree(arg, counter, T, pri.id, sec.id)

    if unsat:
        pri.store_commit(counter, time)

    return T, counter

		

def dialogue(agent, human, query, one_shot_accept = False, arg_tree = False, verbose = False):

    T = nx.DiGraph()  # argumentation tree

    time = 1
    done = False
    if verbose: 
        print(time, ":",human.id, f'asks why {query.clauses}')
        print()
    if one_shot_accept:
        arg = explanation(agent.kb_own, query)
        human.acquire_knowledge(arg)
        # arg = human.commits_other[time][-1]

        # check if the updated KB entails the query

        if verbose: print("Checking if KB entails query")
        if skeptical_entailment(human.kb_own, [], query):
            if verbose: print("KB entails query")
            done=True
            return
    
    while not done:
        time += 1
        if time%2==0:
            pri=agent
            sec=human
        else:
            pri=human
            sec=agent

        if time == 2:
            arg = explanation(pri.kb_own, query)
            if arg_tree:
                T.add_node(str(arg)+'_'+pri.id)
                T.nodes[str(arg)+'_'+pri.id]['support'] = arg
                
            # arg.extend(query.clauses)
            pri.store_commit(arg, time)
            pri.arguments.append(arg)
            if verbose: 
                print(time,":", pri.id,f'argued {arg}')
                print()
                                                      
        else:
            counter = getArgs(time, pri, sec, T, arg_tree = False)
                 
            if counter == None and pri == human:
                if verbose:
                    counter = "agree to disagree" 
                    print(time,":", pri.id,f'argued {counter}')
                    print()
                done = True
                # times = sorted(sec.commit_store_args.keys(), reverse=True)
                # other_arg = sec.commit_store_args[time-1]
                
                
                # if other_arg[0] == None:
                #      #Both agents have nothing to say
                #     print("Dialogue Completed")
                #     print()
                #     done = True
                  
                      
            else:
                if verbose:
                    if counter == None: counter = "agree to disagree" 
                    print(time,":", pri.id,f'argued {counter}')
                    print()
            
            # if time==5:
            #      done = True
    
    if arg_tree:
        pos = graphviz_layout(T, prog="dot")
        nx.draw(T, pos, with_labels=True)
        plt.show()

    return agent.commit_store_args, time

    





def SAT(KB1, KB2):
	# Check if a formula is satisfiable
	s = Solver(name='g4')
	for k in KB1:
		s.add_clause(k)
	for k in KB2:
		s.append_formula(k)
	if s.solve():
		return True
	else:
		return False





# add the claim to the counters s.t we can get rebuttals

def test():
    L = ['a', 'b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z']
    V  = {L[i]:i+1 for i in range(len(L))}

    KBa = [ [1], [2], [-1,-2, 3], [4], [-4, -5], [6], [-6,7]]
    KBh = [[5], [-5, -2], [8], [-8, -4] ]

    

    q = CNF()
    q.append([3])



    agent1 = Agent(KBa, "Agent")
    human = Human(KBh, "Human")



    D = dialogue(agent1, human, q, one_shot_accept = False, arg_tree = False, verbose=True)
    
    

test()








