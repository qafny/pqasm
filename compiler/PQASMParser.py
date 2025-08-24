# Generated from PQASM.g4 by ANTLR 4.13.1
# encoding: utf-8
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
	from typing import TextIO
else:
	from typing.io import TextIO

def serializedATN():
    return [
        4,1,31,169,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
        6,2,7,7,7,2,8,7,8,2,9,7,9,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,
        0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,
        0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,3,0,57,8,0,1,1,1,1,1,1,
        1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
        1,1,1,1,1,1,1,1,3,1,82,8,1,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,
        2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,
        2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,3,2,120,8,2,1,3,1,3,1,
        3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,
        3,3,3,141,8,3,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,3,
        4,155,8,4,1,5,1,5,1,5,1,5,1,6,1,6,1,7,1,7,1,8,1,8,1,9,1,9,1,9,0,
        0,10,0,2,4,6,8,10,12,14,16,18,0,2,2,0,28,28,30,30,1,0,29,30,178,
        0,56,1,0,0,0,2,81,1,0,0,0,4,119,1,0,0,0,6,140,1,0,0,0,8,154,1,0,
        0,0,10,156,1,0,0,0,12,160,1,0,0,0,14,162,1,0,0,0,16,164,1,0,0,0,
        18,166,1,0,0,0,20,57,5,1,0,0,21,22,5,2,0,0,22,23,3,2,1,0,23,24,5,
        3,0,0,24,57,1,0,0,0,25,26,5,4,0,0,26,27,3,10,5,0,27,28,5,3,0,0,28,
        57,1,0,0,0,29,30,5,5,0,0,30,31,3,10,5,0,31,32,5,3,0,0,32,57,1,0,
        0,0,33,34,5,6,0,0,34,35,3,0,0,0,35,36,5,7,0,0,36,37,3,0,0,0,37,38,
        5,3,0,0,38,57,1,0,0,0,39,40,5,8,0,0,40,41,3,16,8,0,41,42,5,7,0,0,
        42,43,3,10,5,0,43,44,5,7,0,0,44,45,3,0,0,0,45,46,5,3,0,0,46,57,1,
        0,0,0,47,48,5,9,0,0,48,49,3,8,4,0,49,50,5,7,0,0,50,51,3,0,0,0,51,
        52,5,7,0,0,52,53,3,0,0,0,53,54,5,3,0,0,54,57,1,0,0,0,55,57,3,2,1,
        0,56,20,1,0,0,0,56,21,1,0,0,0,56,25,1,0,0,0,56,29,1,0,0,0,56,33,
        1,0,0,0,56,39,1,0,0,0,56,47,1,0,0,0,56,55,1,0,0,0,57,1,1,0,0,0,58,
        59,5,10,0,0,59,60,3,2,1,0,60,61,5,7,0,0,61,62,3,2,1,0,62,63,5,3,
        0,0,63,82,1,0,0,0,64,65,5,11,0,0,65,66,3,12,6,0,66,67,5,7,0,0,67,
        68,3,2,1,0,68,69,5,3,0,0,69,82,1,0,0,0,70,71,5,12,0,0,71,72,3,4,
        2,0,72,73,5,3,0,0,73,82,1,0,0,0,74,75,5,13,0,0,75,76,3,12,6,0,76,
        77,5,7,0,0,77,78,3,14,7,0,78,79,5,3,0,0,79,82,1,0,0,0,80,82,3,4,
        2,0,81,58,1,0,0,0,81,64,1,0,0,0,81,70,1,0,0,0,81,74,1,0,0,0,81,80,
        1,0,0,0,82,3,1,0,0,0,83,84,5,14,0,0,84,85,3,10,5,0,85,86,5,7,0,0,
        86,87,3,16,8,0,87,88,5,3,0,0,88,120,1,0,0,0,89,90,5,15,0,0,90,91,
        3,10,5,0,91,92,5,7,0,0,92,93,3,16,8,0,93,94,5,7,0,0,94,95,3,12,6,
        0,95,96,5,3,0,0,96,120,1,0,0,0,97,98,5,16,0,0,98,99,3,10,5,0,99,
        100,5,7,0,0,100,101,3,16,8,0,101,102,5,7,0,0,102,103,3,12,6,0,103,
        104,5,3,0,0,104,120,1,0,0,0,105,106,5,17,0,0,106,107,3,10,5,0,107,
        108,5,7,0,0,108,109,3,16,8,0,109,110,5,7,0,0,110,111,3,16,8,0,111,
        112,5,3,0,0,112,120,1,0,0,0,113,114,5,18,0,0,114,115,3,10,5,0,115,
        116,5,7,0,0,116,117,3,12,6,0,117,118,5,3,0,0,118,120,1,0,0,0,119,
        83,1,0,0,0,119,89,1,0,0,0,119,97,1,0,0,0,119,105,1,0,0,0,119,113,
        1,0,0,0,120,5,1,0,0,0,121,122,5,19,0,0,122,123,5,30,0,0,123,141,
        5,3,0,0,124,125,5,20,0,0,125,126,5,28,0,0,126,141,5,3,0,0,127,128,
        5,21,0,0,128,129,3,6,3,0,129,130,5,7,0,0,130,131,3,6,3,0,131,132,
        5,3,0,0,132,141,1,0,0,0,133,134,5,22,0,0,134,135,3,6,3,0,135,136,
        5,7,0,0,136,137,3,6,3,0,137,138,5,3,0,0,138,141,1,0,0,0,139,141,
        3,16,8,0,140,121,1,0,0,0,140,124,1,0,0,0,140,127,1,0,0,0,140,133,
        1,0,0,0,140,139,1,0,0,0,141,7,1,0,0,0,142,143,5,23,0,0,143,144,3,
        6,3,0,144,145,5,7,0,0,145,146,3,6,3,0,146,147,5,3,0,0,147,155,1,
        0,0,0,148,149,5,24,0,0,149,150,3,6,3,0,150,151,5,7,0,0,151,152,3,
        6,3,0,152,153,5,3,0,0,153,155,1,0,0,0,154,142,1,0,0,0,154,148,1,
        0,0,0,155,9,1,0,0,0,156,157,5,25,0,0,157,158,5,30,0,0,158,159,5,
        26,0,0,159,11,1,0,0,0,160,161,3,16,8,0,161,13,1,0,0,0,162,163,3,
        16,8,0,163,15,1,0,0,0,164,165,7,0,0,0,165,17,1,0,0,0,166,167,7,1,
        0,0,167,19,1,0,0,0,5,56,81,119,140,154
    ]

class PQASMParser ( Parser ):

    grammarFileName = "PQASM.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'ESKIP'", "'Next ('", "')'", "'Had ('", 
                     "'New ('", "'ESeq ('", "') ('", "'Meas ('", "'IFa ('", 
                     "'ISeq ('", "'ICU ('", "'Ora ('", "'Ry ('", "'Add ('", 
                     "'Less ('", "'Equal ('", "'ModMult ('", "'Equal_posi_list ('", 
                     "'BA ('", "'Num ('", "'APlus ('", "'AMult ('", "'CEq ('", 
                     "'CLt ('", "'['", "']'", "'eskip'" ]

    symbolicNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "ESKIP", "NAT", 
                      "BOOL", "VARNAME", "WS" ]

    RULE_program = 0
    RULE_instr = 1
    RULE_mu = 2
    RULE_arithExp = 3
    RULE_cBoolExp = 4
    RULE_list = 5
    RULE_pos = 6
    RULE_rot = 7
    RULE_natOrVarname = 8
    RULE_boolOrVarName = 9

    ruleNames =  [ "program", "instr", "mu", "arithExp", "cBoolExp", "list", 
                   "pos", "rot", "natOrVarname", "boolOrVarName" ]

    EOF = Token.EOF
    T__0=1
    T__1=2
    T__2=3
    T__3=4
    T__4=5
    T__5=6
    T__6=7
    T__7=8
    T__8=9
    T__9=10
    T__10=11
    T__11=12
    T__12=13
    T__13=14
    T__14=15
    T__15=16
    T__16=17
    T__17=18
    T__18=19
    T__19=20
    T__20=21
    T__21=22
    T__22=23
    T__23=24
    T__24=25
    T__25=26
    ESKIP=27
    NAT=28
    BOOL=29
    VARNAME=30
    WS=31

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.1")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class ProgramContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def instr(self):
            return self.getTypedRuleContext(PQASMParser.InstrContext,0)


        def list_(self):
            return self.getTypedRuleContext(PQASMParser.ListContext,0)


        def program(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(PQASMParser.ProgramContext)
            else:
                return self.getTypedRuleContext(PQASMParser.ProgramContext,i)


        def natOrVarname(self):
            return self.getTypedRuleContext(PQASMParser.NatOrVarnameContext,0)


        def cBoolExp(self):
            return self.getTypedRuleContext(PQASMParser.CBoolExpContext,0)


        def getRuleIndex(self):
            return PQASMParser.RULE_program

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterProgram" ):
                listener.enterProgram(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitProgram" ):
                listener.exitProgram(self)




    def program(self):

        localctx = PQASMParser.ProgramContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_program)
        try:
            self.state = 56
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [1]:
                self.enterOuterAlt(localctx, 1)
                self.state = 20
                self.match(PQASMParser.T__0)
                pass
            elif token in [2]:
                self.enterOuterAlt(localctx, 2)
                self.state = 21
                self.match(PQASMParser.T__1)
                self.state = 22
                self.instr()
                self.state = 23
                self.match(PQASMParser.T__2)
                pass
            elif token in [4]:
                self.enterOuterAlt(localctx, 3)
                self.state = 25
                self.match(PQASMParser.T__3)
                self.state = 26
                self.list_()
                self.state = 27
                self.match(PQASMParser.T__2)
                pass
            elif token in [5]:
                self.enterOuterAlt(localctx, 4)
                self.state = 29
                self.match(PQASMParser.T__4)
                self.state = 30
                self.list_()
                self.state = 31
                self.match(PQASMParser.T__2)
                pass
            elif token in [6]:
                self.enterOuterAlt(localctx, 5)
                self.state = 33
                self.match(PQASMParser.T__5)
                self.state = 34
                self.program()
                self.state = 35
                self.match(PQASMParser.T__6)
                self.state = 36
                self.program()
                self.state = 37
                self.match(PQASMParser.T__2)
                pass
            elif token in [8]:
                self.enterOuterAlt(localctx, 6)
                self.state = 39
                self.match(PQASMParser.T__7)
                self.state = 40
                self.natOrVarname()
                self.state = 41
                self.match(PQASMParser.T__6)
                self.state = 42
                self.list_()
                self.state = 43
                self.match(PQASMParser.T__6)
                self.state = 44
                self.program()
                self.state = 45
                self.match(PQASMParser.T__2)
                pass
            elif token in [9]:
                self.enterOuterAlt(localctx, 7)
                self.state = 47
                self.match(PQASMParser.T__8)
                self.state = 48
                self.cBoolExp()
                self.state = 49
                self.match(PQASMParser.T__6)
                self.state = 50
                self.program()
                self.state = 51
                self.match(PQASMParser.T__6)
                self.state = 52
                self.program()
                self.state = 53
                self.match(PQASMParser.T__2)
                pass
            elif token in [10, 11, 12, 13, 14, 15, 16, 17, 18]:
                self.enterOuterAlt(localctx, 8)
                self.state = 55
                self.instr()
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class InstrContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def instr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(PQASMParser.InstrContext)
            else:
                return self.getTypedRuleContext(PQASMParser.InstrContext,i)


        def pos(self):
            return self.getTypedRuleContext(PQASMParser.PosContext,0)


        def mu(self):
            return self.getTypedRuleContext(PQASMParser.MuContext,0)


        def rot(self):
            return self.getTypedRuleContext(PQASMParser.RotContext,0)


        def getRuleIndex(self):
            return PQASMParser.RULE_instr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterInstr" ):
                listener.enterInstr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitInstr" ):
                listener.exitInstr(self)




    def instr(self):

        localctx = PQASMParser.InstrContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_instr)
        try:
            self.state = 81
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [10]:
                self.enterOuterAlt(localctx, 1)
                self.state = 58
                self.match(PQASMParser.T__9)
                self.state = 59
                self.instr()
                self.state = 60
                self.match(PQASMParser.T__6)
                self.state = 61
                self.instr()
                self.state = 62
                self.match(PQASMParser.T__2)
                pass
            elif token in [11]:
                self.enterOuterAlt(localctx, 2)
                self.state = 64
                self.match(PQASMParser.T__10)
                self.state = 65
                self.pos()
                self.state = 66
                self.match(PQASMParser.T__6)
                self.state = 67
                self.instr()
                self.state = 68
                self.match(PQASMParser.T__2)
                pass
            elif token in [12]:
                self.enterOuterAlt(localctx, 3)
                self.state = 70
                self.match(PQASMParser.T__11)
                self.state = 71
                self.mu()
                self.state = 72
                self.match(PQASMParser.T__2)
                pass
            elif token in [13]:
                self.enterOuterAlt(localctx, 4)
                self.state = 74
                self.match(PQASMParser.T__12)
                self.state = 75
                self.pos()
                self.state = 76
                self.match(PQASMParser.T__6)
                self.state = 77
                self.rot()
                self.state = 78
                self.match(PQASMParser.T__2)
                pass
            elif token in [14, 15, 16, 17, 18]:
                self.enterOuterAlt(localctx, 5)
                self.state = 80
                self.mu()
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class MuContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def list_(self):
            return self.getTypedRuleContext(PQASMParser.ListContext,0)


        def natOrVarname(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(PQASMParser.NatOrVarnameContext)
            else:
                return self.getTypedRuleContext(PQASMParser.NatOrVarnameContext,i)


        def pos(self):
            return self.getTypedRuleContext(PQASMParser.PosContext,0)


        def getRuleIndex(self):
            return PQASMParser.RULE_mu

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterMu" ):
                listener.enterMu(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitMu" ):
                listener.exitMu(self)




    def mu(self):

        localctx = PQASMParser.MuContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_mu)
        try:
            self.state = 119
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [14]:
                self.enterOuterAlt(localctx, 1)
                self.state = 83
                self.match(PQASMParser.T__13)
                self.state = 84
                self.list_()
                self.state = 85
                self.match(PQASMParser.T__6)
                self.state = 86
                self.natOrVarname()
                self.state = 87
                self.match(PQASMParser.T__2)
                pass
            elif token in [15]:
                self.enterOuterAlt(localctx, 2)
                self.state = 89
                self.match(PQASMParser.T__14)
                self.state = 90
                self.list_()
                self.state = 91
                self.match(PQASMParser.T__6)
                self.state = 92
                self.natOrVarname()
                self.state = 93
                self.match(PQASMParser.T__6)
                self.state = 94
                self.pos()
                self.state = 95
                self.match(PQASMParser.T__2)
                pass
            elif token in [16]:
                self.enterOuterAlt(localctx, 3)
                self.state = 97
                self.match(PQASMParser.T__15)
                self.state = 98
                self.list_()
                self.state = 99
                self.match(PQASMParser.T__6)
                self.state = 100
                self.natOrVarname()
                self.state = 101
                self.match(PQASMParser.T__6)
                self.state = 102
                self.pos()
                self.state = 103
                self.match(PQASMParser.T__2)
                pass
            elif token in [17]:
                self.enterOuterAlt(localctx, 4)
                self.state = 105
                self.match(PQASMParser.T__16)
                self.state = 106
                self.list_()
                self.state = 107
                self.match(PQASMParser.T__6)
                self.state = 108
                self.natOrVarname()
                self.state = 109
                self.match(PQASMParser.T__6)
                self.state = 110
                self.natOrVarname()
                self.state = 111
                self.match(PQASMParser.T__2)
                pass
            elif token in [18]:
                self.enterOuterAlt(localctx, 5)
                self.state = 113
                self.match(PQASMParser.T__17)
                self.state = 114
                self.list_()
                self.state = 115
                self.match(PQASMParser.T__6)
                self.state = 116
                self.pos()
                self.state = 117
                self.match(PQASMParser.T__2)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ArithExpContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def VARNAME(self):
            return self.getToken(PQASMParser.VARNAME, 0)

        def NAT(self):
            return self.getToken(PQASMParser.NAT, 0)

        def arithExp(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(PQASMParser.ArithExpContext)
            else:
                return self.getTypedRuleContext(PQASMParser.ArithExpContext,i)


        def natOrVarname(self):
            return self.getTypedRuleContext(PQASMParser.NatOrVarnameContext,0)


        def getRuleIndex(self):
            return PQASMParser.RULE_arithExp

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterArithExp" ):
                listener.enterArithExp(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitArithExp" ):
                listener.exitArithExp(self)




    def arithExp(self):

        localctx = PQASMParser.ArithExpContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_arithExp)
        try:
            self.state = 140
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [19]:
                self.enterOuterAlt(localctx, 1)
                self.state = 121
                self.match(PQASMParser.T__18)
                self.state = 122
                self.match(PQASMParser.VARNAME)
                self.state = 123
                self.match(PQASMParser.T__2)
                pass
            elif token in [20]:
                self.enterOuterAlt(localctx, 2)
                self.state = 124
                self.match(PQASMParser.T__19)
                self.state = 125
                self.match(PQASMParser.NAT)
                self.state = 126
                self.match(PQASMParser.T__2)
                pass
            elif token in [21]:
                self.enterOuterAlt(localctx, 3)
                self.state = 127
                self.match(PQASMParser.T__20)
                self.state = 128
                self.arithExp()
                self.state = 129
                self.match(PQASMParser.T__6)
                self.state = 130
                self.arithExp()
                self.state = 131
                self.match(PQASMParser.T__2)
                pass
            elif token in [22]:
                self.enterOuterAlt(localctx, 4)
                self.state = 133
                self.match(PQASMParser.T__21)
                self.state = 134
                self.arithExp()
                self.state = 135
                self.match(PQASMParser.T__6)
                self.state = 136
                self.arithExp()
                self.state = 137
                self.match(PQASMParser.T__2)
                pass
            elif token in [28, 30]:
                self.enterOuterAlt(localctx, 5)
                self.state = 139
                self.natOrVarname()
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class CBoolExpContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def arithExp(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(PQASMParser.ArithExpContext)
            else:
                return self.getTypedRuleContext(PQASMParser.ArithExpContext,i)


        def getRuleIndex(self):
            return PQASMParser.RULE_cBoolExp

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterCBoolExp" ):
                listener.enterCBoolExp(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitCBoolExp" ):
                listener.exitCBoolExp(self)




    def cBoolExp(self):

        localctx = PQASMParser.CBoolExpContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_cBoolExp)
        try:
            self.state = 154
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [23]:
                self.enterOuterAlt(localctx, 1)
                self.state = 142
                self.match(PQASMParser.T__22)
                self.state = 143
                self.arithExp()
                self.state = 144
                self.match(PQASMParser.T__6)
                self.state = 145
                self.arithExp()
                self.state = 146
                self.match(PQASMParser.T__2)
                pass
            elif token in [24]:
                self.enterOuterAlt(localctx, 2)
                self.state = 148
                self.match(PQASMParser.T__23)
                self.state = 149
                self.arithExp()
                self.state = 150
                self.match(PQASMParser.T__6)
                self.state = 151
                self.arithExp()
                self.state = 152
                self.match(PQASMParser.T__2)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ListContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def VARNAME(self):
            return self.getToken(PQASMParser.VARNAME, 0)

        def getRuleIndex(self):
            return PQASMParser.RULE_list

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterList" ):
                listener.enterList(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitList" ):
                listener.exitList(self)




    def list_(self):

        localctx = PQASMParser.ListContext(self, self._ctx, self.state)
        self.enterRule(localctx, 10, self.RULE_list)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 156
            self.match(PQASMParser.T__24)
            self.state = 157
            self.match(PQASMParser.VARNAME)
            self.state = 158
            self.match(PQASMParser.T__25)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class PosContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def natOrVarname(self):
            return self.getTypedRuleContext(PQASMParser.NatOrVarnameContext,0)


        def getRuleIndex(self):
            return PQASMParser.RULE_pos

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterPos" ):
                listener.enterPos(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitPos" ):
                listener.exitPos(self)




    def pos(self):

        localctx = PQASMParser.PosContext(self, self._ctx, self.state)
        self.enterRule(localctx, 12, self.RULE_pos)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 160
            self.natOrVarname()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class RotContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def natOrVarname(self):
            return self.getTypedRuleContext(PQASMParser.NatOrVarnameContext,0)


        def getRuleIndex(self):
            return PQASMParser.RULE_rot

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterRot" ):
                listener.enterRot(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitRot" ):
                listener.exitRot(self)




    def rot(self):

        localctx = PQASMParser.RotContext(self, self._ctx, self.state)
        self.enterRule(localctx, 14, self.RULE_rot)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 162
            self.natOrVarname()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class NatOrVarnameContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def NAT(self):
            return self.getToken(PQASMParser.NAT, 0)

        def VARNAME(self):
            return self.getToken(PQASMParser.VARNAME, 0)

        def getRuleIndex(self):
            return PQASMParser.RULE_natOrVarname

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterNatOrVarname" ):
                listener.enterNatOrVarname(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitNatOrVarname" ):
                listener.exitNatOrVarname(self)




    def natOrVarname(self):

        localctx = PQASMParser.NatOrVarnameContext(self, self._ctx, self.state)
        self.enterRule(localctx, 16, self.RULE_natOrVarname)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 164
            _la = self._input.LA(1)
            if not(_la==28 or _la==30):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class BoolOrVarNameContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def BOOL(self):
            return self.getToken(PQASMParser.BOOL, 0)

        def VARNAME(self):
            return self.getToken(PQASMParser.VARNAME, 0)

        def getRuleIndex(self):
            return PQASMParser.RULE_boolOrVarName

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterBoolOrVarName" ):
                listener.enterBoolOrVarName(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitBoolOrVarName" ):
                listener.exitBoolOrVarName(self)




    def boolOrVarName(self):

        localctx = PQASMParser.BoolOrVarNameContext(self, self._ctx, self.state)
        self.enterRule(localctx, 18, self.RULE_boolOrVarName)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 166
            _la = self._input.LA(1)
            if not(_la==29 or _la==30):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





