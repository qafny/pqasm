grammar PQASM;

// -------------------------- Parser Rules ------------------------------------

// High Level

program : instruction
        | program+
        | hadamardOp
        | newQubit
        | measurement
        | conditional;

instruction : oqasmArithmeticOp
            | yRotation
            | controlledInstruction
            | instruction+;

oqasmArithmeticOp : addition
                  | modMult // modular multiplication
                  | equality
                  | comparison;

parameter : qubit
          | NAT;


// Low Level

hadamardOp : HAD '(' qubit ')';

newQubit : 'new (' qubit ')';

conditional : 'if (' BOOL ')' program 'else' program;

yRotation : 'Ry' ANGLE QUBIT;

controlledInstruction : 'CU' QUBIT instruction;

addition : 'add(' parameter ',' parameter ')';

modMult : '(' NAT '*' parameter ') % ' NAT;

equality : '(' parmeter '=' parameter ') @ ' QUBIT;

comparison : '(' parmeter '<' parameter ') @ ' QUBIT


// -------------------------- Lexer Tokens ------------------------------------

NAT : [0-9]+;

BOOL : true
     | false;

QUBIT : [a-zA-Z_][a-zA-Z_0-9]*; // Anything that starts with a letter


WS : [ \t\r\n]+ -> skip; // ignore any whitespace


