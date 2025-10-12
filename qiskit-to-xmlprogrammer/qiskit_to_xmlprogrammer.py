"""
This file contains a visitor which traverses a Qiskit Quantum Circuit and 
converts it into the format required for "XMLProgrammer.py".
"""

import math
import qiskit
from qiskit import transpile
from qiskit import QuantumCircuit
from qiskit.converters import circuit_to_dag
from qiskit.dagcircuit import DAGInNode, DAGOpNode, DAGNode, DAGOutNode
from qiskit.visualization import dag_drawer
import graphviz
import os
import sys
from qiskit.circuit.library.arithmetic import FullAdderGate

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
# current_dir = os.path.dirname(os.path.abspath(__file__))
# sys.path.append(os.path.join(current_dir, "PQASM"))

from AST_Scripts.XMLProgrammer import QXProgram, QXQID, QXCU, QXX, QXH, QXRZ, QXRY

# Ensure graphviz is in the PATH (for dag drawing)
os.environ["PATH"] += os.pathsep + r"C:\Program Files\Graphviz\bin"

# ------------------------- DAG TO XMLPROGRAMMER -------------------------------

supportedGates = ['h','x','y','z','s','sdg','t','tdg','rx','ry','rz','u','cx','cz']
ignoredGates = ['measure']

def decomposeToGates(qc):
    return transpile(qc, basis_gates=supportedGates + ignoredGates)
   
class QCtoXMLProgrammer:
    def __init__(self):
        self.dag = None

    def startVisit(self, qc):
        qc = decomposeToGates(qc)
        self.dag = circuit_to_dag(qc)

        # Dictionary mapping Qiskit qubits to XMLProgrammer qubits
        self.XMLQubits = dict()
        for qubit in self.dag.qubits:
            self.XMLQubits[qubit] = QXQID(str(qubit._index))

        self.visitedNodes = set()
        self.expList = []
        
        for startingNode in self.dag.input_map.values():
            self.visitNode(startingNode)

        self.program = QXProgram(self.expList)
        print("Extracted program in XMLProgrammer format:")

        print(self.program)

        
    def visitNode(self, node):
        if node in self.visitedNodes:
            return
        else:
            self.visitedNodes.add(node)
            self.nodeToXMLProgrammer(node)
            for successor in self.dag.successors(node): # type: ignore
                self.visitNode(successor)


    def nodeToXMLProgrammer(self, node):
        if isinstance(node, DAGOpNode):
            inputBits = [self.XMLQubits[q] for q in node.qargs]
            exps = []

            # H, X, Y, Z:
            if node.name == "h":
                exps.append(QXH("h", inputBits[0]))
            elif node.name == "x":
                exps.append(QXX("x", inputBits[0]))
            elif node.name == "y":
                exps.append(QXRY("y", inputBits[0], 90))
            elif node.name == "z":
                exps.append(QXRZ("z", inputBits[0], 180))

            # Fractional phase shifts (S, SDG, T, TDG):
            elif node.name == "s":
                exps.append(QXRZ("s", inputBits[0], 90))
            elif node.name == "sdg":
                exps.append(QXRZ("sdg", inputBits[0], -90))
            elif node.name == "t":
                exps.append(QXRZ("t", inputBits[0], 45))
            elif node.name == "tdg":
                exps.append(QXRZ("tdg", inputBits[0], -45))

            # General rotations (RX, RY, RZ):
            # elif node.name == "rx":
            #     exps.append(QXRX("rx", inputBits[0], node.params[0]*180/math.pi))
            elif node.name == "ry":
                exps.append(QXRY("ry", inputBits[0], node.params[0]*180/math.pi))
            elif node.name == "rz":
                exps.append(QXRZ("rz", inputBits[0], node.params[0]*180/math.pi))

            # Universal single-qubit gate (U):
            elif node.name == "u":
                # U(a, b, c) = RZ(a) RY(b) RZ(c)
                exps.append(QXRZ("rz", inputBits[0], node.params[0]*180/math.pi))
                exps.append(QXRY("ry", inputBits[0], node.params[1]*180/math.pi))
                exps.append(QXRZ("rz", inputBits[0], node.params[2]*180/math.pi))

            # Controlled operations (CX, CZ):
            elif node.name == "cx":
                exps.append(QXCU("cx", inputBits[0], QXProgram([QXX("x", inputBits[1])])))
            elif node.name == "cz":
                exps.append(QXCU("cz", inputBits[0], QXProgram([QXRZ("z", inputBits[1], 180)])))
            
            else:
                print("Warning: Unrecognized operation ", node.name)

            # Turn the extracted operation into an expression, and add it to
            # the list of expressions
            for exp in exps:
                self.expList.append(exp)
            
            


