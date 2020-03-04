from itertools import chain, combinations
from termcolor import colored

def html_colored(text, color):
    return '<p><font size="2" color="%s">%s</font></p>'%(text, color)

def visualize(cube, inducted_cube, html_file = None):
    for l in cube:
        if l in inducted_cube:
            print(colored("||\t"+str(l), 'blue'))
            if html_file is not None:
                html_file.write(html_colored(str(l), 'blue')
        else:
            print(colored("||\t"+str(l), 'red'))
            if html_file is not None:
                html_file.write(html_colored(str(l), 'red')

def powerset(policy):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    return chain.from_iterable(combinations(policy, r) for r in range(len(policy)+1))

