"""

This file contains a visitor which traverses a Qiskit DAG (Directed Acyclic
Graph - a representation of a quantum circuit) and converts it into the format 
required for "XMLProgrammer.py".

"""

import qiskit
from qiskit import QuantumCircuit
from qiskit.converters import circuit_to_dag
from qiskit.dagcircuit import DAGInNode, DAGOpNode, DAGNode, DAGOutNode
from qiskit.visualization import dag_drawer
import graphviz
import os
import sys

# sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
# current_dir = os.path.dirname(os.path.abspath(__file__))
# sys.path.append(os.path.join(current_dir, "PQASM"))


from AST_Scripts.XMLProgrammer import QXProgram, QXQID, QXCU, QXX, QXH, QXRZ

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

dagEx1 = circuit_to_dag(qc)

print(qc.draw())
#qc.draw("mpl")
dag_img = dag_drawer(dagEx1, style="color")
dag_img.save('dagEx1.png')

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


dagEx2 = circuit_to_dag(qc)

print(qc.draw())
dag_img = dag_drawer(dagEx2, style="color")
dag_img.save('dagEx2.png')


# ----- 3: 3-Qubit GHZ

qc = QuantumCircuit(3, 0)
qc.h(0)
qc.cx(0, 1)
qc.cx(1, 2)

dagEx3 = circuit_to_dag(qc)

print(qc.draw())
dag_img = dag_drawer(dagEx3, style="color")
dag_img.save('dagEx3.png')



# ------------------------- DAG TO XMLPROGRAMMER -------------------------------


class DAGtoXMLProgrammer:
    def __init__(self):
        self.dag = None

    def startVisit(self, dag):
        self.dag = dag

        # Dictionary mapping Qiskit qubits to XMLProgrammer qubits
        self.XMLQubits = dict()
        for qubit in dag.qubits:
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
            elif node.name == "y": # Y = HXHXH
                exps.append(QXH("h", inputBits[0]))
                exps.append(QXX("x", inputBits[0]))
                exps.append(QXH("h", inputBits[0]))
                exps.append(QXX("x", inputBits[0]))
                exps.append(QXH("h", inputBits[0]))
            elif node.name == "z":
                exp = QXRZ("z", inputBits[0], 180)

            # Fractional phase shifts (S, SDG, T, TDG):
            elif node.name == "s":
                exp = QXRZ("s", inputBits[0], 90)
            elif node.name == "sdg":
                exp = QXRZ("sdg", inputBits[0], -90)
            elif node.name == "t":
                exp = QXRZ("t", inputBits[0], 45)
            elif node.name == "tdg":
                exp = QXRZ("tdg", inputBits[0], -45)


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

visitor = DAGtoXMLProgrammer()

visitor.startVisit(dagEx1)
visitor.startVisit(dagEx2)
visitor.startVisit(dagEx3)





