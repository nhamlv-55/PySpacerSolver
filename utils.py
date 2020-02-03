from itertools import chain, combinations
from termcolor import colored

def visualize(cube, inducted_cube):
    for l in cube:
        if l in inducted_cube:
            print(colored("||\t"+str(l), 'green'))
        else:
            print(colored("||\t"+str(l), 'red'))

def powerset(policy):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    return chain.from_iterable(combinations(policy, r) for r in range(len(policy)+1))

