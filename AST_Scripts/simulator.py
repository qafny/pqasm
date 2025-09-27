import traceback
from collections import ChainMap
# from types import NoneType

from XMLProgrammer import *
from ProgramVisitor import *

NoneType = type(None)


class CoqVal:
    pass  # TODO


class CoqNVal(CoqVal):

    def __init__(self, boolean_binary_array: [bool], phase: int):
        self.boolean_binary = boolean_binary_array
        self.phase = phase

    def getBits(self):
        return self.boolean_binary

    def getPhase(self):
        return self.phase


class CoqQVal(CoqVal):

    def __init__(self, r1: int, r2: int, b: [bool] = None, n: int = None):
        self.r1 = r1
        self.r2 = r2
        self.n = n
        self.b = b

    def getPhase(self):
        return self.r1

    def getLocal(self):
        return self.r2

    def getRest(self):
        return self.b

    def getNum(self):
        return self.n



class CoqYVal(CoqVal):

    def __init__(self, r1: int, r2: float):
        self.r1 = r1
        self.r2 = r2

    def getPhase(self):
        return self.r1

    def getLocal(self):
        return self.r2

    def addLocal(self, r):
        self.r2 += r


"""
Helper Functions
"""


def exchange(coq_val: CoqVal, n: int):
    if isinstance(coq_val, CoqNVal):
        coq_val.getBits()[n] = not coq_val.getBits()[n]


def times_rotate(v, q, rmax):
    if isinstance(v, CoqNVal):
        if v.boolean_binary:
            return CoqNVal(v.getBits(), rotate(v.getPhase(), q, rmax))
        else:
            return CoqNVal(v.getBits(), v.getPhase())
    else:
        return CoqQVal(v.r1, rotate(v.r2, q, rmax))


def addto(r, n, rmax):
    return (r + 2 ** max_helper(rmax, n)) % 2 ** rmax


def max_helper(x, y):
    return max(x - y, 0)


def rotate(r, n, rmax):
    return addto(r, n, rmax)


def addto_n(r, n, rmax):
    return max_helper(r + 2 ** rmax, 2 ** max_helper(rmax, n)) % 2 ** rmax


def r_rotate(r, n, rmax):
    return addto_n(r, n, rmax)


def times_r_rotate(v, q, rmax):
    if isinstance(v, CoqNVal):
        if v.boolean_binary:
            return CoqNVal(v.getBits(), r_rotate(v.getPhase(), q, rmax))
        else:
            return CoqNVal(v.getBits(), v.getPhase())
    else:
        return CoqQVal(v.r1, r_rotate(v.r2, q, rmax))


def up_h(v, rmax):
    if isinstance(v, CoqNVal):
        b = v.boolean_binary
        r = v.phase
        if b:
            return CoqQVal(
                r,
                rotate(0, 1, rmax)
            )
        else:
            return CoqQVal(r, 0)
    else:
        r = v.r1
        f = v.r2
        return CoqNVal(
            2 ** max_helper(rmax, 1) <= f,
            r
        )


def natminusmod(x, v, a):
    if x - v < 0:
        return x - v + a
    else:
        return x - v


def bit_array_to_int(bit_array, num_qubits):
    val = 0
    #print("bit_array", bit_array)
    #print("length of bit array", len(bit_array))
    #print("num_qubits", num_qubits)
    for i in range(min(len(bit_array), num_qubits)):
        val += pow(2, i) * int(bit_array[i])
    return val


def to_binary_arr(value, array_length):
    binary_arr = [False] * array_length
    for i in range(array_length):
        b = value % 2
        value = value // 2
        binary_arr[i] = bool(b)
    return binary_arr

def calBin(val, num):
    return to_binary_arr(val, num)


def calBinNoLength(v):
    val = []
    while v != 0:
        b = v % 2
        v = v // 2
        val.append(b)
    return val


class Simulator(ProgramVisitor):
    # x, y, z, env : ChainMap{ x: n, y : m, z : v} , n m v are nat numbers 100, 100, 100, eg {x : 128}
    # st state map, {x : v1, y : v2 , z : v3}, eg {x : v1}: v1,
    # st {x : v1} --> Coq_nval case: v1 is a ChainMap of Coq_nval
    # v1 --> 128 length array v1: {0 : Coq_nval, 1 : Coq_nval, 2 : Coq_nval, ...., 127 : Coq_nval}, 2^128
    # x --> v1 --> cal(v1) --> integer
    # Coq_nval(b,r) b == |0> | |1>, r == e^(2 pi i * 1 / n), r = 0 Coq_nval(b, 0)
    # x -> v1 ----> run simulator -----> v2 ---> calInt(v2,128) == (x + 2^10) % 2^128
    def __init__(self, state: dict, env: dict):
        self.state = state
        self.env = env
        # self.rmax = rmax rmax is M_find(x,env), a map from var to int

    def visitLet(self, ctx: XMLProgrammer.QXLet):
        f = ctx.ID()
        self.state.update({f: ctx})
        #print("f", ctx)
        #ctx.exp().accept(self)

    # def visitMatchexp(self, ctx: XMLExpParser.MatchexpContext):
    #     print('1')
    #     return
    #     match_ID = ctx.idexp().accept(self)
    #     print('match_ID:', match_ID)
    #     print(self.st)
    #     match_state_value = self.st.get(match_ID)
    #     i = 0
    #     while ctx.exppair(i) is not None:
    #         vexp_node = ctx.exppair(i).vexp()
    #         if vexp_node.OP() is not None:
    #             va = vexp_node.accept(self)
    #             if match_state_value == va:
    #                 # ctx.exppair(i).exp().accept(self)
    #                 return
    #         else:
    #             # y : list= ctx.exppair(i).vexp().vexp()
    #             y = ctx.exppair(i).vexp().vexp()
    #             print('Y')
    #             print(y)
    #             print(type(y))
    #             #self.st.update({y: match_state_value - 1})
    #            # ctx.exppair(i).exp().accept(self)
    #         i += 1

    def visitMatch(self, ctx: XMLProgrammer.QXMatch):
        x = ctx.ID()
        value = self.state.get(x)
        #print("old value", value)
        if value <= 0:
            ctx.zero().program().accept(self)
        else:
            va = ctx.multi().elem().ID()
            tmpv = self.state.get(va)
            self.state.update({va: int(value) - 1})
            ctx.multi().program().accept(self)
            self.state.update({va:tmpv})

    def visitApp(self, ctx: XMLProgrammer.QXApp):
        vx = ctx.ID()
        ctxa = self.state.get(vx)
        #print("here",ctx.idexp().Identifier())
        #print("herea",ctxa.idexp(0).Identifier())
        #ctxa = self.st.get(f)
        i = 0
        tmpv = dict()
        tmpa = dict()
        while ctxa.idexp(i) is not None:
            x = ctxa.idexp(i).ID()
            #print("here",x)
            #print("var",ctxa.idexp(i+1).Identifier())
            v = ctx.vexp(i).accept(self)
            #print("val",v)
            tmpv.update({x:self.state.get(x)})
            tmpa.update({x:v})
            i += 1

        while len(tmpa) != 0:
            xv,re = tmpa.popitem()
            self.state.update({xv: re})
            #print("vara",xv,"vala",re)

        ctxa.program().accept(self)
        while len(tmpv) != 0:
            xv,re = tmpv.popitem()
            if re is not None:
                self.state.update({xv:re})
            else:
                self.state.pop(xv, None)

            #print ("var",xv)
            #print("val",re)

    def visitIf(self, ctx: XMLProgrammer.QXIf):
        v = ctx.vexp().accept(self)
        if v == 1:
            #print("here", ctx.left())
            ctx.left().accept(self)
        else:
            #print("here",ctx.right())
            ctx.right().accept(self)

    def get_state(self):
        return self.state

    def sr_rotate(self, x, n):
        val = self.state.get(x)[0]
        if isinstance(val, CoqQVal):
            self.state.get(x)[0] = CoqQVal(val.r1, (val.r2 + pow(2, val.getNum() - n)) % pow(2, val.getNum()), val.getRest(), val.getNum())

    def srr_rotate(self, x, n):
        #print("here")
        val = self.state.get(x)[0]
        if isinstance(val, CoqQVal):
            self.state.get(x)[0] = CoqQVal(val.r1, ((val.r2 +
                                                     pow(2, val.getNum()) - pow(2, val.getNum() - n)) % pow(2, val.getNum())), val.getRest(), val.getNum())

    # should do nothing
    def visitSKIP(self, ctx: XMLProgrammer.QXSKIP):
        return

    # X posi, changed the following for an example
    def visitX(self, ctx: XMLProgrammer.QXX):
        vx = ctx.ID()
        x = self.state.get(vx)[0]
        p = ctx.vexp().accept(self)  # this will pass the visitor to the child of ctx
        exchange(x, p)

    def visitRZ(self, ctx: XMLProgrammer.QXRZ):
        vx = ctx.ID()
        val = self.state.get(vx)[0]
        p = ctx.num().accept(self)  # this will pass the visitor to the child of ctx
        if p >= 0:
            times_rotate(val, p, val.getNum())
        else:
            times_r_rotate(val, p, val.getNum())

    def visitRY(self, ctx: XMLProgrammer.QXRY):
        vx = ctx.ID()
        val = ctx.vexp().accept(self)
        p = ctx.num().accept(self)  # this will pass the visitor to the child of ctx
        x = self.state.get(vx)[0]
        if isinstance(x.getBits()[val], CoqYVal):
            x.getBits()[val].addLocal(p)

    # we will first get the position in st and check if the state is 0 or 1,
    # then decide if we go to recursively call ctx.exp
    def visitCU(self, ctx: XMLProgrammer.QXCU):
        vx = ctx.ID()
        x = self.state.get(vx)[0]
        p = ctx.vexp().accept(self)  # this will pass the visitor to the child of ctx
        if x.getBits()[p]:
            ctx.program().accept(self)
        else:
            return  # do nothing

    # my previous rz parsing is wrong
    # it should be RZ q posi
    # def visitRzexp(self, ctx: XMLExpParser.RzexpContext):
    #     q = int(ctx.vexp(0).accept(self))  # I guess then you need to define vexp
    #     # we can first define the var and integer case
    # I guess Identifier and int are all terminal
    # does it means that we do not need to define anything?
    #     x = ctx.idexp().accept(self)
    #    p = ctx.vexp(1).accept(self)  # this will pass the visitor to the child of ctx
    #   if q >= 0:
    #      self.st.update({x: times_rotate(self.st.get(x), q, self.env.get(x))})
    #  else:
    #     self.st.update({x: times_r_rotate(self.st.get(x), abs(q), self.env.get(x))})

    # SR n x, now variables are all string, are this OK?
    def visitSR(self, ctx: XMLProgrammer.QXSR):
        n = int(ctx.vexp().accept(self))
        x = ctx.ID()
        if n >= 0:
            self.sr_rotate(x, n)
        else:
            self.srr_rotate(x, abs(n))

    def lshift(self, x, n):
        if n == 0:
            return

        tmp = self.state.get(x)[0].getBits()
        tmpv = tmp[0]
        for i in range(n - 1):
            tmp[i] = tmp[i + 1]
        tmp[n - 1] = tmpv
        self.state.get(x)[0] = CoqNVal(tmp, self.state.get(x)[0].getPhase())

    def visitLshift(self, ctx: XMLProgrammer.QXLshift):
        x = ctx.ID()
        self.lshift(x, self.env.get(x))

    def rshift(self, x, n):
        if n == 0:
            return

        tmp = self.state.get(x)[0].getBits()
        tmpv = tmp[n - 1]
        for i in range(n - 1, -1, -1):
            tmp[i] = tmp[i - 1]

        tmp[0] = tmpv
        self.state.get(x)[0] = CoqNVal(tmp, self.state.get(x)[0].getPhase())

    def visitRshift(self, ctx: XMLProgrammer.QXRshift):
        x = ctx.ID()
        self.rshift(x, self.env.get(x))

    def reverse(self, x, n):
        if n == 0:
            return

        size = n
        tmp = self.state.get(x)[0].getBits()
        tmpa = []
        for i in range(n):
            tmpa.append(tmp[size - i])
        self.state.get(x)[0] = CoqNVal(tmp, self.state.get(x)[0].getPhase())

    def visitRev(self, ctx: XMLProgrammer.QXRev):
        x = ctx.ID()
        self.reverse(x, self.env.get(x))

    def turn_qft(self, x, n):
        val = self.state.get(x)[0]
        r1 = val.getPhase()
        r2 = 0
        if isinstance(val, CoqNVal):
            for i in range(n):
                r2 = (r2 + pow(2, i) * int(val.getBits()[i])) % pow(2, n)
        result = val.getBits()[n:]
        #print("val", result)
        self.state.get(x)[0] = CoqQVal(r1, r2, result, n)

        # actually, we need to change the QFT function
        # the following QFT is only for full QFT, we did not have the case for AQFT

    def visitQFT(self, ctx: XMLProgrammer.QXQFT):
        x = ctx.ID()
        v = ctx.vexp().accept(self)
        b = int(v)
        self.turn_qft(x, self.env.get(x) - b)
        #print("qft_exp val",self.env.get(x)-b)
        #print("qft_exp x",self.st.get(x))
        # TODO implement

    def turn_rqft(self, x):
        val = self.state.get(x)[0]
        n = val.getNum()
        if isinstance(val, CoqQVal):
            tmp = val.getLocal()
            tov = [False] * n
            for i in range(n):
                b = tmp % 2
                tmp = tmp // 2
                tov[i] = bool(b)
            result = tov + val.getRest()
            self.state.get(x)[0] = CoqNVal(result, val.getPhase())

    def visitRQFT(self, ctx: XMLProgrammer.QXRQFT):
        x = ctx.ID()
        self.turn_rqft(x)
        #print("rqftexp end")

    def visitIDExp(self, ctx: XMLProgrammer.QXIDExp):
        # print("idexp var",ctx.Identifier().accept(self))
        # print("idexp val",self.get_state().get(ctx.Identifier().accept(self)))
        return self.get_state().get(ctx.ID())

    def visitQID(self, ctx: XMLProgrammer.QXQID):
            # print("idexp var",ctx.Identifier().accept(self))
            # print("idexp val",self.get_state().get(ctx.Identifier().accept(self)))
        return self.get_state().get(ctx.ID())
        # Visit a parse tree produced by XMLExpParser#vexp.

    def visitBin(self, ctx: XMLProgrammer.QXBin):
        x = ctx.left().accept(self)
        y = ctx.right().accept(self)
            #print("val",y)
        #print(ctx.OP())
        if ctx.OP() == "+":
            return x + y
        elif ctx.OP() == "-":
            return x - y
        elif ctx.OP() == "*":
            return x * y
        elif ctx.OP() == "/":
            if y == 0:
                return 0
            return x // y
        elif ctx.OP() == "^":
            return x ** y
        elif ctx.OP() == "%":
            if y == 0:
                return 0
            return x % y
        elif ctx.OP() == "$":
            #print("here1")
            tmp = (calBinNoLength(x))
                #print("val",tmp)
                #print("val",tmp)
                #print("vala", y)
            if y < len(tmp):
                #print("here",tmp[y])
                return int(tmp[y])
        return 0
    # def visitIDExp(self, ctx: XMLProgrammer.QXIDExp):
    #     ctx.type().accept(self)

    def visitNum(self, ctx: XMLProgrammer.QXNum):
        #print("nonecc",ctx.num())
        return ctx.num()

    #def visitIda(self, ctx: XMLExpParser.IdaContext):
    #    return ctx.Identifier().getText()

        # the only thing that matters will be 48 and 47
