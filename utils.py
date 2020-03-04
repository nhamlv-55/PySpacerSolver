from itertools import chain, combinations
from termcolor import colored

def html_colored(text, color = "black"):
    text = text.replace("<", "&lt;")
    text = text.replace(">", "&gt;")
    return '<p><font size="4" face="monospace" color="%s">%s</font></p>'%(color, text)

def visualize(cube, inducted_cube, html_file = None):
    for l in cube:
        if l in inducted_cube:
            print(colored("||\t"+str(l), 'blue'))
            if html_file is not None:
                html_file.write(html_colored(str(l), 'blue'))
        else:
            print(colored("||\t"+str(l), 'red'))
            if html_file is not None:
                html_file.write(html_colored(str(l), 'red'))

def powerset(policy):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    return chain.from_iterable(combinations(policy, r) for r in range(len(policy)+1))

class HtmlVisPage:
    def __init__(self, filename):
        self.filename = filename
        self.header = '<!DOCTYPE html>\n<html>\n<body>\n'
        self.footer = '</body>\n</html>'
        self.body = []
    def write(self, s):
        self.body.append(s)

    def dump(self):
        with open(self.filename, "w") as f:
            f.write(self.header)
            f.writelines(self.body)
            f.write(self.footer)
