# By chatGPT

from antlr4 import *
from PQASMCodeLexer import PQASMCodeLexer
from PQASMCodeParser import PQASMCodeParser

# Load the PQASM filepython parse_pqasm.py
input_stream = FileStream("test.pqasm")

# Create a lexer and token stream
lexer = PQASMCodeLexer(input_stream)
token_stream = CommonTokenStream(lexer)

# Create a parser and parse the file starting from the 'program' rule
parser = PQASMCodeParser(token_stream)
tree = parser.program()  # 'program' is your start rule

# Optional: print the parse tree as text
print(tree.toStringTree(recog=parser))
