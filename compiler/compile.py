"""
This file is used to compile a .pqasm file into a .qasm file.
Along the way, it checks for syntax errors.
"""

import sys
import argparse
import os
from antlr4 import *
from PQASMLexer import PQASMLexer
from PQASMParser import PQASMParser
from antlr4.error.ErrorListener import ErrorListener


class EListener(ErrorListener):
    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        print("Parsing failed: Syntax error at line " + line + ", column " +
              column + ", with message: " + msg + "\n");


def main():

    # Read the file specified on the command line
    if len(sys.argv) != 2:
        print("Usage: python compilePQASM.py <inputfile.pqasm>")
        sys.exit(1)
    input_file = sys.argv[1]
    input_stream = FileStream(input_file)


    # Syntax check the .pqasm file using the parser
    lexer = PQASMLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = PQASMParser(stream)
    parser.removeErrorListeners()
    parser.addErrorListener(EListener())
    parser.program()
    print("Parsing finished. No syntax errors found.")


    # Get the argument from the cmd line
    parser = argparse.ArgumentParser()
    parser.add_argument("inputFile") # The file inputted in .pqasm
    args = parser.parse_args()

    outputFile = os.path.splitext(args.inputFile)[0] + ".qasm"

    print("Output written to " + outputFile + "in location " + os.getcwd())



# Ensure the main function runs
if __name__ == "__main__":
    main()