grammar PQASMPaper;

// This grammar is only aligned with the paper, not the actual syntax being used
// in the test cases

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

parameter : QUBIT
          | NAT;


// Low Level

hadamardOp : 'h(' QUBIT ')';

newQubit : 'new (' QUBIT ')';

conditional : 'if (' BOOL ')' program 'else' program;

yRotation : 'Ry' angle QUBIT;

controlledInstruction : 'CU' QUBIT instruction;

addition : 'add(' parameter ',' parameter ')';

modMult : '(' NAT '*' parameter ') % ' NAT;

equality : '(' parameter '=' parameter ') @ ' QUBIT;

comparison : '(' parameter '<' parameter ') @ ' QUBIT;

angle : REAL;


// -------------------------- Lexer Tokens ------------------------------------

NAT : [0-9]+;

REAL : [+-]? DIGIT+ ('.' DIGIT+)? ([eE] [+-]? DIGIT+)?; // Real number

BOOL : true
     | false;

QUBIT : [a-zA-Z_][a-zA-Z_0-9]*; // Anything that starts with a letter


WS : [ \t\r\n]+ -> skip; // ignore any whitespace


