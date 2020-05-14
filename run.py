import os
import torch
import numpy as np

data = {}
dataset = []
count = 0
for file in os.listdir('clean_AutoTutorWithTrue'):
    data = {}
    with open('clean_AutoTutorWithTrue/' + file, 'r') as f:
        neg_yet = False
        for i, line in enumerate(f):
            if i == 0:
                data['false'] = line.strip()
            elif i == 1:
                data['true'] = line.strip()
            else:
                if '+++' in line:
                    continue
                if "---" in line:
                    neg_yet = True
                    continue
                if 'pos' not in data:
                    data['pos'] = []
                if neg_yet == False:
                    data['pos'].append(line.strip())
                if 'neg' not in data:
                    data['neg'] = []
                if neg_yet == True:
                    data['neg'].append(line.strip())
    dataset.append(data)
    count += 1

print(dataset)


from lark import Lark, Transformer, v_args
import lark

calc_grammar = '''
    ?start: product

    ?product: atom

    ?atom: A
        | B
        | atom "*" -> kleene
        | atom atom -> concat
        | "(" product ")"

    A: "a"

    B: "b"
'''

def run_instruction(t):
    str = ''
    if isinstance(t, lark.Tree):
        if t.data == 'concat':
            str += run_instruction(t.children[0])
            str += run_instruction(t.children[1])
        elif t.data == 'kleene':
            str += 'inv' + run_instruction(t.children[0])
    else:
        if t.type == 'A':
            str += 'A'
        else:
            str += 'B'
    print(str)
    return str


def run_conversion(program):
    str = ''
    for inst in program.children:
        str += run_instruction(inst)
    return str

def cln_prep(t, exp_param):
    result = []
    if isinstance(t, lark.Tree):
        if t.data == 'concat':
            for i in cln_prep(t.children[0], exp_param):
                for j in cln_prep(t.children[1], exp_param):
                    result.append(i + j)
            return result
        elif t.data == 'kleene':
            for i in cln_prep(t.children[0], exp_param):
                for j in range(exp_param):
                    result.append(i * j)
            return result
    else:
        if t.type == 'A':
            return ['a']
        else:
            return ['b']

total_len = 20
total_cnt = 0
new_param = 3

def cln_prep_smt(t):
    global new_param
    global total_cnt
    indexes = []
    values = []
    index_cst = []
    value_cst = []

    values = ['x_%s' % i for i in range(100)]
    if isinstance(t, lark.Tree):
        if t.data == 'concat':
            x = cln_prep_smt(t.children[0])
            y = cln_prep_smt(t.children[1])
            index_cst.append('%s == %s - 1' % (x[-1], y[0]))
            return x[0] + y[0], values, x[2], x[3]
        elif t.data == 'kleene':
            vals = []
            x = cln_prep_smt(t.children[0])
            for i in x[0]:
                for j in range(0, new_param):
                    vals.append(i + str(j))
            return vals, values, index_cst, value_cst
    else:
        if t.type == 'A':
            total_cnt += 1
            return ['x_0'], [], [], ['a']
        else:
            total_cnt += 1
            return ['x_1'], [], [], ['b']

def get_formula(calc):
    return calc

def to_z3(form):
    i = 0
    indexes5 = []
    indexes4 = []
    indexes3 = []
    indexes2 = []
    indexes1 = []
    while (i < len(form)):
        if form[i:i+5] == 'aaaaa' or form[i:i+5] == 'bbbbb':
            indexes5.append(i)
            indexes5.append(i+5)
            i += 5
        elif form[i:i+4] == 'aaaa' or form[i:i+4] == 'bbbb':
            indexes4.append(i)
            indexes4.append(i+4)
            i += 4
        elif form[i:i+3] == 'aaa' or form[i:i+3] == 'bbb':
            indexes3.append(i)
            indexes3.append(i+3)
            i += 3
        elif form[i:i+2] == 'aa' or form[i: i+2] == 'bb':
            indexes2.append(i)
            indexes2.append(i+2)
            i += 2
        elif form[i:i+1] == 'a' or form[i: i+1] == 'b':
            indexes1.append(i)
            indexes1.append(i+1)
            i += 1
        else:
            i += 1
    return indexes5, indexes4, indexes3, indexes2, indexes1

from itertools import groupby, product

def max_to_ind(form):
    groups = groupby(form)
    result = [(label, sum(1 for _ in group)) for label, group in groups]
    return result

import z3
from z3 import Int, And, Or, Solver

def flip(num):
    if num == 0:
        num = 1
    else:
        num = 0

def get_distances(indexes):
    X = [Int("x_%s" % i) for i in range(len(indexes))]
    csts = And([X[i] - X[j] <= indexes[i][1] for (i,j) in zip(range(len(indexes)), range(len(indexes))[1:])])
    csts2 = And([(X[i] - X[j] >= 0) for (i,j) in zip(range(len(indexes)), range(len(indexes))[1:])])
    csts = And(csts, csts2)
    Y = [Int("y_%s" % i) for i in range(20)]
    prod = product(*[range(len(indexes))], *[(range(20))])
    val_csts = And([])
    for a in prod:
        #this is for each possible assignment
        A = And([X[w-1] == t for (w,t) in enumerate(a)])
        B = And([])
        _v = 0
        for start in [0, 1]:
            while (_v < len(a)):
                if _v in a:
                    start = flip(start)
                B = And(B, Y[_v] == start)
                _v += 1
        val_csts = Or(Or(val_csts, A), B)
        #val_csts = And([i for i in range(10)])

    #val_csts = Or(And(([X[i] == 1 for i in range(20)]), [Y[1] == 1 for i in range(20)]))
    return X, csts, Y, val_csts

def get_example(example, X):
    ret = And([])
    print(example, len(X))
    for (i,x) in enumerate(example):
        if x == 'b':
            ret = And(ret, X[i] == 1)
        else:
            ret = And(ret, X[i] == 0)
    return ret

for data in dataset:
    try:
        l = Lark(calc_grammar, parser = 'lalr')
        calc = l.parse(data['false'])
        for i in [data['true']]:
            total_cnt = 0
            calc = l.parse(i)
            print("formula is " + i)
            print("examples include ")
            i = 4
            #print(cln_prep(calc, i))
            for (i_j, j) in enumerate([data['pos'], data['neg']]):
                if i_j == 0:
                    sat = 0
                    unsat = 0
                    for k in j:
                        #print(max(cln_prep(calc, i), key=len))
                        #print(to_z3(max(cln_prep(calc, i), key=len)))
                        grouped = max_to_ind(max(cln_prep(calc, i), key=len))
                        #print(grouped)
                        dist = get_distances(grouped)
                        s = Solver()
                        s.add(dist[1])
                        s.add(dist[3])
                        s.add(get_example(k, dist[0]))
                        #print(s.check())
                        if str(s.check()) == 'sat':
                            sat += 1
                        else:
                            unsat += 1
                    print(str(sat) + 'out of ' + str(len(j)))
                else:
                    sat = 0
                    unsat = 0
                    for k in j:
                        #print(max(cln_prep(calc, i), key=len))
                        #print(to_z3(max(cln_prep(calc, i), key=len)))
                        grouped = max_to_ind(max(cln_prep(calc, i), key=len))
                        #print(grouped)
                        dist = get_distances(grouped)
                        s = Solver()
                        s.add(dist[1])
                        s.add(dist[3])
                        s.add(get_example(k, dist[0]))
                        #print(s.check())
                        if str(s.check()) == 'sat':
                            sat += 1
                        else:
                            unsat += 1
                    print(str(unsat) + 'out of ' + str(len(j)))
            #print(cln_prep_smt(calc))
            #print(len(cln_prep_smt(calc)[0]))
    except:
        pass
#print(get_example(data['pos'][0], X))

def to_z3(indexes):
    count = 0
    vars = []
    cnstr = []
    for (x,y) in zip(indexes, indexes[1:]):
        var.append('x_%s' % count)
        cnstr.append('x_%s <= y_%s - %s' % count, count + 1)
        count += 1


X = [Int ("x_%s" % i) for i in range(20)]
I = [Int ("i_%s")]
Y = [Int ("x_%s")]
