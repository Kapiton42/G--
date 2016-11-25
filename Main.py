# -----------------------------------------------------------------------------
# calc.py
#
# A simple calculator with variables -- all in one file.
# -----------------------------------------------------------------------------

tokens = (
    'FIGOPEN', 'FIGCLOSE', 'NAME', 'NUMERIC', 'STRING', 'LOGIC', 'PROC', 'TYPE',
    'LPLUS', 'RPLUS', 'MINUS', 'TIMES', 'DIVIDE', 'EQUALS',
    'LPAREN', 'RPAREN', 'PIRS', 'LESS', 'MORE',
    'XZ', 'ADIN', 'WHILEO',
    'WHILEZ', 'AND', 'MOVEUPPROC', 'MOVEDOWNPROC',
    'MOVELEFTPROC', 'MOVERIGHTPROC', 'PINGUPPROC',
    'VISIONPROC', 'VOICEPROC', 'DATA', 'CONVTO',
    'CONVFR', 'SKOBKVO', 'SKOBKVZ', 'TYPEDEF',
    'UNDEF', 'ZAP',
)

# Tokens

t_LPLUS = r'\.\+'
t_RPLUS = r'\+\.'
t_MINUS = r'-'
t_TIMES = r'\*'
t_DIVIDE = r'/'
t_EQUALS = r'='
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_PIRS = r'\^'
t_LESS = r'<'
t_MORE = r'>'
t_XZ = r'\?'
t_ADIN = r'!'
t_FIGOPEN = r'block'
t_FIGCLOSE = r'unblock'
t_WHILEO = r'{'
t_WHILEZ = r'}'
t_AND = r'&'
t_ZAP = r','

t_MOVEUPPROC = r'MOVEUP'
t_MOVEDOWNPROC = r'MOVEDOWN'
t_MOVELEFTPROC = r'MOVELEFT'
t_MOVERIGHTPROC = r'MOVERIGHT'
t_PINGUPPROC = r'PINGUP'
t_VISIONPROC = r'VISION'
t_VOICEPROC = r'VOICE'

# My tokens
ident = r'[a-z]\w+'

t_DATA = r'DATA'
t_PROC = r'PROC'
t_CONVTO = r'conversion to'
t_CONVFR = r'conversion from'

t_SKOBKVO = r'\['
t_SKOBKVZ = r'\]'
t_TYPEDEF = r'RECORD'
t_UNDEF = r'undef'
t_STRING = r'"(\\.|[^"])*"'
t_LOGIC = r'true|false'
t_TYPE = r'[A-Z][a-z]+'

def t_NAME(t):
    r'[a-z][a-zA-Z0-9]*'
    if t.value.lower() == 'block':
        t.type = 'FIGOPEN'
    if t.value.lower() == 'unblock':
        t.type = 'FIGCLOSE'
    return t

def t_NUMERIC(t):
    r'[1-9]\d*|0'
    try:
        t.value = int(t.value)
    except ValueError:
        print("Integer value too large %d", t.value)
        t.value = 0
    return t


# Ignored characters
t_ignore = " \t"


def t_newline(t):
    r'\n+'
    t.lexer.lineno += t.value.count("\n")


def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)


# Build the lexer
import ply.lex as lex

lexer = lex.lex()
#print lexer.input('PROC test[] 2*2')
#while True:
#    tok = lexer.token()
#    if not tok: break
#    print tok

# Parsing rules


class Variable(object):
    typeOfVariable = ''
    value = ''

    def __init__(self, typeOfVariable, value):
        self.value = value
        self.typeOfVariable = typeOfVariable

    def __str__(self):
        # print(str(self.value))
        return str(self.value)


class ExpressionReturn(object):
    typeOfExpr = ''
    value = ''

    def __init__(self, typeOfExpr, value):
        self.value = value
        self.typeOfExpr = typeOfExpr

    def __str__(self):
        # print(str(self.value))
        return str(self.value)


precedence = (
    ('left', 'LPLUS', 'MINUS', 'RPLUS'),
    ('left', 'TIMES', 'DIVIDE'),
    ('right', 'UMINUS'),
)

# dictionary of names
names = [{}]
funcs = {}
preds = []

curFuncPred = []

funcNow = False
nameCurFunc = ''
argsCurFunc = ''
blockState = False

whileExpr = ''
whileNow = False


def predsAppend(pred):
    global funcNow
    global blockState
    global curFuncPred
    global whileNow

    if funcNow:
        curFuncPred.append(pred)
        if not blockState:
            funcNow = False
            preds.append(('declProc', nameCurFunc, argsCurFunc, curFuncPred))
            curFuncPred = []
    elif whileNow:
        curFuncPred.append(pred)
        if not blockState:
            whileNow = False
            preds.append(('while', whileExpr, curFuncPred))
            curFuncPred = []
    else:
        preds.append(pred)


def p_pred_while(t):
    'pred : WHILEO expression WHILEZ'
    global whileExpr
    global whileNow
    whileExpr = t[2]
    whileNow = True


def p_pred_block(t):
    'pred : FIGOPEN'
    global blockState
    blockState = True


def p_pred_unblock(T):
    'pred : FIGCLOSE'
    global funcNow
    global whileNow
    global blockState
    global curFuncPred
    if funcNow:
        if blockState:
            funcNow = False
            preds.append(('declProc', nameCurFunc, argsCurFunc, curFuncPred))
            curFuncPred = []
    elif whileNow:
        if blockState:
            whileNow = False
            preds.append(('while', whileExpr, curFuncPred))
            curFuncPred = []
    blockState = False


def p_pred_proc(t):
    'pred : PROC NAME SKOBKVO argsType SKOBKVZ'
    #funcs[t[2]] = (t[4], [])
    global funcNow
    global nameCurFunc
    global argsCurFunc
    funcNow = True
    nameCurFunc = t[2]
    argsCurFunc = t[4]

def p_pred_assign(t):
    '''pred : NAME EQUALS expression
                 | declarationVariable EQUALS expression'''
    #names[t[1]].value = doType(t[3].value, names[t[1]].typeOfVariable)
    predsAppend(('assign', t[1], t[3]))



def p_pred_declarationVariable(t):
    'pred : declarationVariable'
    predsAppend(t[1])


def p_pred_expr(t):
    'pred : expression'
    predsAppend(t[1])
    #if funcNow:
    #    curFuncPred.append(t[0])
    #else:
    #    preds.append(t[0])


def p_declarationVariable(t):
    'declarationVariable : TYPE NAME'
    t[0] = ('declVar', t[1], t[2])
    #if t[2] in names:
    #    print('Variable with name ' + t[2] + ' exist')
    #    raise NameError()
    #    return
    #names[t[2]] = Variable(t[1], 'undefined')
    #t[0] = t[2]


def p_argsType_nul(t):
    'argsType : '
    t[0] = []


def p_argsType_one(t):
    'argsType : TYPE NAME'
    t[0] = [ExpressionReturn(t[1], t[2])]


def p_argsType_many(t):
    'argsType : argsType ZAP TYPE NAME'
    t[1].append(ExpressionReturn(t[3], t[4]))
    t[0] = t[1]



def p_expr_func(t):
    'expression : NAME SKOBKVO args SKOBKVZ'
    t[0] = ('Func', t[1], t[3])


def p_args_nul(t):
    'args : '
    t[0] = []


def p_args_one(t):
    'args : expression'
    t[0] = [t[1]]


def p_args_many(t):
    'args : args ZAP expression'
    t[1].append(t[3])
    t[0] = t[1]


def p_expression_binop(t):
    '''expression : expression LPLUS expression
                  | expression RPLUS expression
                  | expression MINUS expression
                  | expression TIMES expression
                  | expression DIVIDE expression'''
    t[0] = ('Binop', t[1], t[2], t[3])


def p_expression_uminus(t):
    'expression : MINUS expression %prec UMINUS'
    t[0] = ('Uminus', t[2])


def p_expression_group(t):
    'expression : LPAREN expression RPAREN'
    t[0] = ('Group', t[2])


def p_expression_numeric(t):
    'expression : NUMERIC'
    t[0] = ('Constant', ExpressionReturn('Numeric', t[1]))


def p_expression_name(t):
    'expression : NAME'
    t[0] = ('Variable', t[1])


def p_expression_string(t):
    'expression : STRING'
    t[0] = ('Constant', ExpressionReturn('String', t[1][1:-1]))


def p_expression_logic(t):
    'expression : LOGIC'
    t[0] = ('Constant', ExpressionReturn('Logic', t[1]))


def p_error(t):
    print("Syntax error at '%s'" % t.value)


def doType(var, type):
    if type == 'Numeric':
        return int(var)
    elif type == 'String':
        return str(var)
    elif type == 'Logic':
        return bool(var)

def executeProc(args, func):
    if len(args) != len(func[0]):
        #print(len(args), len(func[0]), func)
        raise Exception
    names.append(names[-1].copy())
    for (argType, arg) in zip(func[0], args):
        temp = runTree(arg)
        names[-1][argType.value] = Variable(argType.typeOfExpr, doType(temp.value, argType.typeOfExpr))

    for tree in func[1]:
        temp = runTree(tree)
        if temp is not None:
            print("I SHOW YOU", runTree(tree).value)
    names.pop()


def runTree(tree):
    if tree[0] == 'print':
        print(tree[1:])
    elif tree[0] == 'Constant':
        return tree[1]
    elif tree[0] == 'Variable':
        try:
            return ExpressionReturn(getVar(tree[1]).typeOfVariable, getVar(tree[1]).value)
        except LookupError:
            print("Undefined name '%s'" % tree[1])
    elif tree[0] == 'Func':
        try:
            executeProc(tree[2], funcs[tree[1]])
            return
        except LookupError:
            print("Undefined func '%s'" % tree[1])
    elif tree[0] == 'Binop':
        firstLit = runTree(tree[1])
        secondLit = runTree(tree[3])
        if tree[2] == '.+':
            return ExpressionReturn(secondLit.typeOfExpr, firstLit.value + doType(secondLit.value, firstLit.typeOfExpr))
        elif tree[2] == '+.':
            return ExpressionReturn(firstLit.typeOfExpr, doType(firstLit.value, secondLit.typeOfExpr) + secondLit.value)
        elif tree[2] == '-':
            return ExpressionReturn(secondLit.typeOfExpr, firstLit.value - secondLit.value)
        elif tree[2] == '*':
            return ExpressionReturn(secondLit.typeOfExpr, firstLit.value * secondLit.value)
        elif tree[2] == '/':
            return ExpressionReturn(secondLit.typeOfExpr, firstLit.value / secondLit.value)
    elif tree[0] == 'Group':
        return runTree(tree[1])
    elif tree[0] == 'Uminus':
        cur_expr = runTree(tree[1])

        if cur_expr.typeOfExpr == 'Logic':
            cur_expr.value = not cur_expr.value
            return cur_expr
        if cur_expr.typeOfExpr == 'Numeric':
            cur_expr.value = - cur_expr.value
            return cur_expr
    elif tree[0] == 'declProc':
        funcs[tree[1]] = (tree[2], tree[3])
        return
    elif tree[0] == 'while':
        while doType(runTree(tree[1]).value, 'Logic'):
            for tree1 in tree[2]:
                print(tree1)
                runTree(tree1)
        return
    elif tree[0] == 'declVar':
        names[-1][tree[2]] = Variable(tree[1], tree[2])
        return
    elif tree[0] == 'assign':
        setVar(tree[1], runTree(tree[2]).value)
        return

    raise Exception()


def getVar(name):
    for i in range(0, len(names)):
        try:
            temp = names[len(names) - 1 - i][name]
            return temp
        except LookupError:
            pass
    raise Exception


def setVar(name, value):
    for i in range(0, len(names)):
        try:
            temp = names[len(names) - 1 - i][name]
            names[len(names) - 1 - i][name] = \
                Variable(temp.typeOfVariable, doType(value, temp.typeOfVariable))
            return
        except LookupError:
            pass
    raise Exception

import ply.yacc as yacc
parser = yacc.yacc()
while True:
    try:
        s = raw_input('calc > ')  # Use raw_input on Python 2
    except EOFError:
        break
    parser.parse(s)
    print(preds)
    if len(preds) > 0:
        #try:
            print(runTree(preds.pop()))
        #except Exception:
        #    print 'ooops'
