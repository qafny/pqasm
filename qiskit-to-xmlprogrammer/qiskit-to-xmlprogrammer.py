"""

This file contains a visitor which traverses a Qiskit DAG (Directed Acyclic
Graph - a representation of a quantum circuit) and converts it into the format 
required for "XMLProgrammer.py".

"""

import math
import qiskit
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

# --------------------------- EXAMPLE CIRCUITS ---------------------------------

# ----- 1: Common gates

qc = QuantumCircuit(2, 2)
qc.h(0)
qc.cx(0, 1)
qc.h(1)
qc.x(1)
qc.measure([0,1], [0,1])

print(qc.draw())
qcEx1 = qc.copy()

# dag_img = dag_drawer(dagEx1, style="color")
# dag_img.save('dagEx1.png')

# ----- 2: All qiskit gates

qc = QuantumCircuit(3, 1)
qc.h(0)
qc.cx(0, 1)
qc.x(2)
qc.z(2)
qc.s(1)
qc.t(0)
qc.cz(1, 2)
qc.sdg(1)
qc.tdg(0)
qc.y(0)

print(qc.draw())
qcEx2 = qc.copy()

# ----- 3: 3-Qubit GHZ

qc = QuantumCircuit(3, 0)
qc.h(0)
qc.cx(0, 1)
qc.cx(1, 2)

print(qc.draw())
qcEx3 = qc.copy()


# -------------------------- QISKIT LIBRARY CIRCUITS ---------------------------

# 1: Half Adder

# Create a quantum circuit with 4 qubits:
# 1, 2 are inputs qubits, 3 is carry-in, 4 is the output (a+b+carry-in)
qc = QuantumCircuit(4)  # 4 qubits for a single 1-bit full adder
qc.append(FullAdderGate(num_state_qubits=1), [0, 1, 2, 3])  # no argument, just 1-bit adder

print(qc.draw())
qcEx4 = qc.copy()

# ------------------------- DAG TO XMLPROGRAMMER -------------------------------

def decomposeToGates(qc):
    prev_qc = qc
    while True:
        decomp = prev_qc.decompose()
        if decomp == prev_qc:
            break
        prev_qc = decomp
    return decomp


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
            
            
# ------------------------------- EXAMPLE USAGE --------------------------------

visitor = QCtoXMLProgrammer()

print("----- Example 1 -----")
visitor.startVisit(qcEx1)
print("----- Example 2 -----")
visitor.startVisit(qcEx2)
print("----- Example 3 -----")
visitor.startVisit(qcEx3)
print("----- Example 4 -----")
visitor.startVisit(qcEx4)





