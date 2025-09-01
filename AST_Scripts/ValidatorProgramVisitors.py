import random

from Source.quantumCode.AST_Scripts import XMLProgrammer
from Source.quantumCode.AST_Scripts.ProgramVisitor import ProgramVisitor
from Source.quantumCode.AST_Scripts.Retrievers import RPFRetriever
from Source.quantumCode.AST_Scripts.XMLProgrammer import QXApp, QXMatch, QXNum, QXIf
from Source.quantumCode.AST_Scripts.simulator import Simulator


def calBinNoLength(v):
    val = []
    while v != 0:
        b = v % 2
        v = v // 2
        val.append(b)
    return val


class SimulatorValidator(ProgramVisitor):

    def visitLet(self, ctx: XMLProgrammer.QXLet):
        ctx.program().accept(self)

    def visitMatch(self, ctx: XMLProgrammer.QXMatch):
        counter = 0
        i = 0
        while ctx.multi().program().exp(i) is not None:
            if isinstance(ctx.multi().program().exp(i), QXApp):
                # Disallow more than 1 App inside pair
                if counter > 0:
                    raise Exception("Found more than one app in pair")
                else:
                    ctx.multi().program().exp(i).accept(self)
                    counter += 1
            else:
                ctx.multi().program().exp(i).accept(self)
            i += 1

        if counter == 0:
            raise Exception("Found no app in pair")

    def visitApp(self, ctx: XMLProgrammer.QXApp):
        return

    def visitIf(self, ctx: XMLProgrammer.QXIf):
        return

    def visitIDExp(self, ctx: XMLProgrammer.QXIDExp):
        return 1

    def visitQID(self, ctx: XMLProgrammer.QXQID):
        return 1

    def visitNum(self, ctx: XMLProgrammer.QXNum):
        return 1


class AppRPFValidator(ProgramVisitor):

    def __init__(self, rpf_retriever: RPFRetriever):
        self.fs = {}

        # For now, we assume index 0 is the RPF and set the initial value to be greater than 0 to test RPF decrement
        # condition.
        self.rpf_0 = -1
        self.rpf_i_it_vexp_id = None

        self.rpf_retriever = rpf_retriever

    def visitLet(self, ctx: XMLProgrammer.QXLet):
        f_id = ctx.ID()
        self.fs[f_id] = ctx

    def visitMatch(self, ctx: XMLProgrammer.QXMatch):
        # It is guaranteed here that RPF current value will be greater than 0, therefore no need to check for 0 condition.
        # Directly addressing multi
        i = 0
        while ctx.multi().program().exp(i) is not None:
            if isinstance(ctx.multi().program().exp(i), QXApp):
                rpf_i_vexp = ctx.multi().program().exp(i).vexp(self.rpf_retriever.get_rpf_index())
                return rpf_i_vexp.accept(self)

            i += 1

        # TODO: There are certainly programs with no Match tags (for non-recursive app calls), so check here for such programs.
        # If no match is found, we do not let run, fail here.
        return self.rpf_0 + 1

    def visitApp(self, ctx: XMLProgrammer.QXApp):
        vx = ctx.ID()
        ctxa = self.fs[vx]

        # Perform checks for 10000 iterations
        for _ in range(10000):
            self.rpf_0 = random.randint(1, 10000)

            i = 0
            while ctxa.program().exp(i) is not None:
                if isinstance(ctxa.program().exp(i), QXMatch):
                    rpf_i = ctxa.program().exp(i).accept(self)

                    if self.rpf_0 <= rpf_i:
                        raise Exception("Non-Decreasing Recursive Fixed Point Factor. Infinite Loop Detected.")

                    break

                i += 1

    def visitIDExp(self, ctx: XMLProgrammer.QXIDExp):
        if ctx.ID() == self.rpf_retriever.get_rps_var_id():
            return self.rpf_0 - 1  ## m = n - 1
        else:
            return random.randint(0, 10000)  ## Otherwise every vexp returns a random number between 0 & 10000

    def visitNum(self, ctx: XMLProgrammer.QXNum):
        return ctx.num()

    def visitBin(self, ctx: XMLProgrammer.QXBin):
        x = ctx.left().accept(self)
        y = ctx.right().accept(self)
        # print("val",y)
        # print(ctx.OP())
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
            # print("here1")
            tmp = (calBinNoLength(x))
            # print("val",tmp)
            # print("val",tmp)
            # print("vala", y)
            if y < len(tmp):
                # print("here",tmp[y])
                return int(tmp[y])
        return 0
