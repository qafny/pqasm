"""
This file contains library circuits from Qiskit to be compiled into
XMLProgrammer format. Run this file to compile them.

"""

import math
from qiskit_to_xmlprogrammer import QCtoXMLProgrammer
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

# -------------------------- QISKIT LIBRARY CIRCUITS ---------------------------

# 1: Half Adder

# Create a quantum circuit with 4 qubits:
# 1, 2 are inputs qubits, 3 is carry-in, 4 is the output (a+b+carry-in)
qc = QuantumCircuit(4)  # 4 qubits for a single 1-bit full adder
qc.append(FullAdderGate(num_state_qubits=1), [0, 1, 2, 3])  # no argument, just 1-bit adder
print('---circuit 1---')
print(qc.draw())
qcEx1 = qc.copy()

# 2: linear pauli rotations
# based on https://github.com/Qiskit/qiskit/blob/main/qiskit/circuit/library/arithmetic/linear_pauli_rotations.py
num_qubits = 6
circuit = QuantumCircuit(num_qubits)

# build the circuit
qr_state = circuit.qubits[:num_qubits - 1]
qr_target = circuit.qubits[-1]
circuit.rx(0, qr_target)
for i, q_i in enumerate(qr_state):
    circuit.crx(1 * pow(2, i), q_i, qr_target)
# if self.basis == "x":
#     circuit.rx(self.offset, qr_target)
# elif self.basis == "y":
#     circuit.ry(self.offset, qr_target)
# else:  # 'Z':
#     circuit.rz(self.offset, qr_target)

# for i, q_i in enumerate(qr_state):
#     if self.basis == "x":
#         circuit.crx(self.slope * pow(2, i), q_i, qr_target)
#     elif self.basis == "y":
#         circuit.cry(self.slope * pow(2, i), q_i, qr_target)
#     else:  # 'Z'
#         circuit.crz(self.slope * pow(2, i), q_i, qr_target)
print('---circuit 2---')
print(circuit.draw())
qcEx2 = circuit.copy()


# -------------------------- COMPILE TO XMLPROGRAMMER --------------------------

visitor = QCtoXMLProgrammer()

print("----- Example 1 -----")
visitor.startVisit(qcEx1)
print("----- Example 2 -----")
visitor.startVisit(qcEx2)

