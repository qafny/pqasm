grammar PQASMCode;

// -------------------------- Parser Rules ------------------------------------

program : 'ESKIP'
        | 'Next (' instr ')'
        | 'Had (' list ')'
        | 'New (' list ')'
        | 'ESeq ( program ') (' program ')'
        | 'Meas (' natOrVarname ') (' list ') (' program ')'
        | 'IFa (' cBoolExp ') (' program ') (' program ')'
        | instr;

instr : 'ISeq (' instr ') (' instr ')' 
      | 'ICU (' pos ') (' instr ')' 
      | 'Ora (' mu ')' 
      | 'Ry (' pos ') (' rot ')'
      | mu;

// OQASM arithmetic operations
mu : 'Add (' list ') (' natOrVarname ')'
   | 'Less (' list ') (' natOrVarname ') (' pos ')'
   | 'Equal (' list ') (' natOrVarname ') (' pos ')'
   | 'ModMult (' list ') (' natOrVarname ') (' natOrVarname ')'
   | 'Equal_posi_list (' list ') (' pos ')';

// Arithmetic expression
arithExp : 'BA (' VARNAME ')'       // 'BA' seems to be a variable literal
         | 'Num (' NAT ')'
         | 'APlus (' arithExp ') (' arithExp ')'
         | 'AMult (' arithExp ') (' arithExp ')'
         | VARNnatOrVarnameAME;

// Classical boolean expression
cBoolExp : 'CEq (' arithExp ') (' arithExp ')'
         | 'CLt (' arithExp ') (' arithExp ')';


// Low Level

list : '['VARNAME']';

pos : natOrVarname; // Position (in a list)
rot : natOrVarname; // Rotation (this seems to be defined only as a NAT and not REAL?)

natOrVarname : NAT
             | VARNAME;

boolOrVarName : BOOL
              | VARNAME;


// -------------------------- Lexer Tokens ------------------------------------

ESKIP : eskip;

NAT : [0-9]+;

BOOL : true
     | false; // I'm not sure how booleans are even written in PQASM, this is a guess

VARNAME : [a-zA-Z_0-9]*; // Any combo of letters and numbers

WS : [ \t\r\n]+ -> skip; // ignore any whitespace













// OLD


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

//New definitions required

// hadamardOp : 'h(' QUBIT ')';
// 
// newQubit : 'new (' QUBIT ')';
// 
// conditional : 'if (' BOOL ')' program 'else' program;
// 
// yRotation : 'Ry' angle QUBIT;
// 
// controlledInstruction : 'CU' QUBIT instruction;
// 
// addition : 'add(' parameter ',' parameter ')';
// 
// modMult : '(' NAT '*' parameter ') % ' NAT;
// 
// equality : '(' parameter '=' parameter ') @ ' QUBIT;
// 
// comparison : '(' parameter '<' parameter ') @ ' QUBIT;
// 
// angle : REAL;


// -------------------------- Lexer Tokens ------------------------------------

NAT : [0-9]+;

REAL : [+-]? DIGIT+ ('.' DIGIT+)? ([eE] [+-]? DIGIT+)?; // Real number

BOOL : true
     | false;

QUBIT : [a-zA-Z_][a-zA-Z_0-9]*; // Anything that starts with a letter


WS : [ \t\r\n]+ -> skip; // ignore any whitespace


