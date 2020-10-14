import z3
import functools

#mc_file = open('mc.z3', 'r')
#joinlines = lambda f: functools.reduce(lambda l1,l2: l1 + l2, f)
#js = joinlines(mc_file.readlines())
#print(js)
parsed = z3.parse_smt2_file('mc.z3')
