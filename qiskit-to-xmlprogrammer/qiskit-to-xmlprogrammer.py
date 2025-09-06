"""

This file contains a visitor which traverses a Qiskit DAG (Directed Acyclic
Graph - a representation of a quantum circuit) and converts it into the format 
required for "XMLProgrammer.py".

"""


import qiskit
from qiskit import QuantumCircuit
from qiskit.converters import circuit_to_dag
from qiskit.dagcircuit import DAGInNode, DAGOpNode, DAGNode, DAGOutNode

from XMLProgrammer import QXProgram, QXQID, QXCU, QXX, QXTop, QXExp, QXH


# Example circuit
qc = QuantumCircuit(2, 2)
qc.h(0)
qc.cx(0, 1)
qc.measure([0,1], [0,1])
print(qc.draw())

# Convert to DAG
dagEx = circuit_to_dag(qc)


# ------------------------- DAG TO XMLPROGRAMMER -------------------------------


class DAGVisitor:
    def __init__(self, dag, func = "nodeToXMLProgrammer"):
        self.dag = dag
        
        if func == "printDAG":
            self.func = self.printNodeAndType
        elif func == "nodeToXMLProgrammer":
            self.func = self.nodeToXMLProgrammer
        else:
            raise ValueError("Unknown function for visitor for visitor")

        # Dictionary mapping Qiskit qubits to XMLProgrammer qubits
        self.XMLQubits = dict()
        for qubit in dag.qubits:
            self.XMLQubits[qubit] = QXQID(str(qubit._index))


    def printNodeAndType(self, node):
        if isinstance(node, DAGInNode):
            print("Input Node for wire: ", node.wire)
        elif isinstance(node, DAGOutNode):
            print("Output Node for wire: ", node.wire)
        elif isinstance(node, DAGOpNode):
            print("Operation Node: ", node.op.base_class, " named ", node.name)
        else:
            print("???")


    def startVisit(self):
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
            self.func(node)
            for successor in self.dag.successors(node):
                self.visitNode(successor)


    def nodeToXMLProgrammer(self, node):
        if isinstance(node, DAGInNode):
            pass
        elif isinstance(node, DAGOutNode):
            pass
        elif isinstance(node, DAGOpNode):
            inputBits = [self.XMLQubits[q] for q in node.qargs]

            # Map the operation to XMLProgrammer format
            exp = None
            # Controlled not:
            if node.name == "cx":
                exp = QXCU("cx", inputBits[0], QXProgram([QXX("x", inputBits[1])]))
            elif node.name == "h":
                exp = QXH("h", inputBits[0])
            else:
                pass

            print("Expression found:", exp)

            # Turn the extracted operation into an expression, and add it to
            # the list of expressions
            if exp is not None:
                self.expList.append(exp)
            
            
# ------------------------------- EXAMPLE USAGE --------------------------------

# DAG Printer
#printerVistor = DAGVisitor(dagEx, "printDAG")
#printerVistor.startVisit()


# DAG to XMLProgrammer
xmlProgrammerVisitor = DAGVisitor(dagEx)
xmlProgrammerVisitor.startVisit()





