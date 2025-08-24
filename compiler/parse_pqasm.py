# By chatGPT

from antlr4 import *
from PQASMLexer import PQASMLexer
from PQASMParser import PQASMParser

# Load the PQASM filepython parse_pqasm.py
input_stream = FileStream("test.pqasm")

# Create a lexer and token stream
lexer = PQASMLexer(input_stream)
token_stream = CommonTokenStream(lexer)

# Create a parser and parse the file starting from the 'program' rule
parser = PQASMParser(token_stream)
tree = parser.program()  # 'program' is your start rule

# Optional: print the parse tree as text
print(tree.toStringTree(recog=parser))
