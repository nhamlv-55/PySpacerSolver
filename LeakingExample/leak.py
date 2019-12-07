import z3
from pysmt.smtlib.parser import SmtLibParser, SmtLibCommand, SmtLibScript
from six.moves import cStringIO
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter, quote
import pysmt.solvers.z3 as pyz3

from pysmt.fnode import FNode, FNodeContent
z3.set_param(proof = True)
z3.set_param(model = True)
parser = SmtLibParser()

converter = pyz3.Z3Converter(parser.env, z3.get_ctx(None))
