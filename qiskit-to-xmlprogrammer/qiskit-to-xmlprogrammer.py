import qiskit
from qiskit import QuantumCircuit
from qiskit.converters import circuit_to_dag
from qiskit.dagcircuit import DAGInNode, DAGOpNode, DAGNode, DAGOutNode


# Example circuit
qc = QuantumCircuit(2, 2)
qc.h(0)
qc.cx(0, 1)
qc.measure([0,1], [0,1])
print(qc.draw())

# Convert to DAG
dagEx = circuit_to_dag(qc)

# Create a visitor (class which goes thorugh the DAG)
class DAGVisitor:
    def __init__(self, dag, func):
        self.dag = dag
        self.func = func
        self.visitedNodes = set()
        # Not recording non-visited nodes won't matter, since if they can't be reached
        #, they have no effect on the code anyways

    def startVisit(self):
        self.visitedNodes = set()
        startNodes = set()

        for startingNode in dagEx.input_map.values():
            self.visitNode(startingNode)

        
    def visitNode(self, node):
        if node in self.visitedNodes:
            return
        else:
            self.visitedNodes.add(node)
            self.func(node)
            for successor in self.dag.successors(node):
                self.visitNode(successor)
            

# example usage: just print everything out:
def printNodeAndType(node):
    if isinstance(node, DAGInNode):
        print("Input Node for wire: ", node.wire)
    elif isinstance(node, DAGOutNode):
        print("Output Node for wire: ", node.wire)
    elif isinstance(node, DAGOpNode):
        print("Operation Node: ", node.op.base_class, " named ", node.name)
    else:
        print("???")

printerVistor = DAGVisitor(dagEx, printNodeAndType)
printerVistor.startVisit()