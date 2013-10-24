#!/usr/bin/python2
#import inspect
import math
import os
import random
import re
import sys
import zcc_parser_static
import collections
import var_table
import merkle

verbose = 1

INPUT_TAG = "INPUT"
OUTPUT_TAG = "OUTPUT"
CONSTRAINTS_TAG = "CONSTRAINTS"
VARIABLES_TAG = "VARIABLES"

END_TAG = "END_"
START_TAG = "START_"

m = 0  # input size
chi = 0 # number of constraints
NzA = 0 # Number of nonzero elements in the A matrices
NzB = 0 # Number of nonzero elements in the B matrices
NzC = 0 # Number of nonzero elements in the C matrices
    
input_vars = False  # input
output_vars = False  # output
variables = False  #variables

proverBugginess = 0 # a number from 0 to 1 determining the probability of
                    # the prover skipping a proof variable.
class_name = ""
printMetrics = False


# Merkle stuff
has_state = False
uses_ram = False

merkle_gen = False
db_size = -1
ram_cell_num_bits = -1
db_hash_vars = []

num_hash_var_sets = 0
num_ramgets = 0

num_substs = 0

const_vars = {}


def process_spec_section(spec_file, start_tag, end_tag, func):
  in_section = False
  for line in spec_file:
    if not in_section:
      in_section = line.startswith(start_tag)
    elif line.startswith(end_tag):
      break
    else:
      func(line)

def make_hash_vars(vt):
  global merkle_gen, num_hash_var_sets

  hash_vars = []
  for i in range(0, merkle_gen.num_hash_elts()):
    hash_vars.append(vt.read_var("DB_HASH_%d_%d //__merkle_DB_HASH_%d_%d int bits 64" % \
                                 (num_hash_var_sets, i, num_hash_var_sets, i)))
  num_hash_var_sets += 1
  return hash_vars

def insert_db_hash_inputs(spec_file):
  global has_state, uses_ram

  for line in spec_file:
    match = re.search('RAMGET|RAMPUT|HASHGET|HASHPUT|HASHFREE|GENERICGET|GENERICPUT|GENERICFREE', line)
    if match:
      has_state = True
      if match.group() == "RAMGET" or match.group() == "RAMPUT":
        uses_ram = True
        break

  spec_file.seek(0)

  if not uses_ram:
    return

  global db_hash_vars
  db_hash_vars = make_hash_vars(input_vars)

def expand_db_ops_in_spec(spec_file):
  global has_state

  if not has_state:
    return spec_file

  new_spec_file = open(spec_file.name + ".expanded", "w+")
  new_spec_file.write(START_TAG + CONSTRAINTS_TAG + "\n")

  def f(line):
    terms = line.split()

    if line.startswith("RAMGET"):
      expand_ramget(new_spec_file, terms[2], int(terms[4]), terms[6:])
    elif line.startswith("RAMPUT"):
      expand_ramput(new_spec_file, terms[2], int(terms[4]), terms[6:])
    elif line.startswith("HASHGET") or line.startswith("HASHPUT"):
      hash_vars_start = 4
      hash_vars_end = hash_vars_start + int(terms[2])
      hash_bit_vars = terms[hash_vars_start : hash_vars_end]
      terms = terms[hash_vars_end:]
      num_val_bits = int(terms[1])

      if line.startswith("HASHGET"):
        expand_hashget(new_spec_file, hash_bit_vars, num_val_bits, terms[3:])
      else:
        expand_hashput(new_spec_file, hash_bit_vars, num_val_bits, terms[3:])
    elif line.startswith("HASHFREE"):
      hash_vars_start = 4
      hash_vars_end = hash_vars_start + int(terms[2])
      hash_bit_vars = terms[hash_vars_start : hash_vars_end]
      expand_hashfree(new_spec_file, hash_bit_vars)
    else:
      new_spec_file.write(line + "\n")

  process_spec_section(spec_file, START_TAG + CONSTRAINTS_TAG, END_TAG + CONSTRAINTS_TAG, f)
  spec_file.close()

  new_spec_file.write(END_TAG + CONSTRAINTS_TAG + "\n")
  new_spec_file.seek(0)
  return new_spec_file


# Alas, for now we have to replace constants with variables. That's the cost of using pre-built
# constraint templates rather than compiler-optimized constraints.
def const_to_var(val, extra_assigns):
  global const_vars

  try:
    const = int(val)

    if const in const_vars:
      return const_vars[const]
    else:
      var_name = "CONST_TO_VAR_%d" % len(const_vars)
      variables.read_var(var_name)
      const_vars[const] = var_name
      extra_assigns.append("(  ) * (  ) + ( %d - %s )" % (const, var_name))
      return var_name
  except ValueError:
    return val # not a constant

def consts_to_vars(vals, extra_assigns):
  for i in range(len(vals)):
    vals[i] = const_to_var(vals[i], extra_assigns)


def expand_ramget(new_spec_file, index, num_bits, bit_vars):
  global num_ramgets, db_hash_vars, ram_cell_num_bits

  if num_bits > ram_cell_num_bits:
    raise Exception("Tried to get too many bits from a RAM cell. expected=%d actual=%d"
                    % (ram_cell_num_bits, num_bits))

  extra_assigns = []
  index = const_to_var(index, extra_assigns)
  consts_to_vars(bit_vars, extra_assigns)

  for _ in range(len(bit_vars), ram_cell_num_bits):
    var_name = "RAMGET_PAD_%d" % num_ramgets
    variables.read_var(var_name)
    bit_vars.append(var_name)

  def subst(name):
    return ram_subst(name, index, bit_vars, None)

  cons_entry = merkle_gen.generate_get_bits(db_size, ram_cell_num_bits)
  merkle_replace_vars(cons_entry, new_spec_file, subst, extra_assigns)

  num_ramgets += 1

def expand_ramput(new_spec_file, index, num_bits, bit_vars):
  global db_hash_vars, ram_cell_num_bits

  if num_bits > ram_cell_num_bits:
    raise Exception("Tried to put too many bits to a RAM cell. expected=%d actual=%d"
                    % (ram_cell_num_bits, num_bits))

  for _ in range(len(bit_vars), ram_cell_num_bits):
    bit_vars.append('0')

  extra_assigns = []
  index = const_to_var(index, extra_assigns)
  consts_to_vars(bit_vars, extra_assigns)
  new_hash_vars = make_hash_vars(variables)

  def subst(name):
    return ram_subst(name, index, bit_vars, new_hash_vars)

  cons_entry = merkle_gen.generate_put_bits(db_size, ram_cell_num_bits)
  merkle_replace_vars(cons_entry, new_spec_file, subst, extra_assigns)

  db_hash_vars = new_hash_vars

def expand_hashget(new_spec_file, hash_bits, num_val_bits, val_bits):
  extra_assigns = []
  consts_to_vars(hash_bits, extra_assigns)
  consts_to_vars(val_bits, extra_assigns)

  def subst(name):
    return block_subst(name, hash_bits, val_bits)

  cons_entry = merkle_gen.generate_get_block_by_hash(num_val_bits)
  merkle_replace_vars(cons_entry, new_spec_file, subst, extra_assigns)

def expand_hashput(new_spec_file, hash_bits, num_val_bits, val_bits):
  extra_assigns = []
  consts_to_vars(hash_bits, extra_assigns)
  consts_to_vars(val_bits, extra_assigns)

  def subst(name):
    return block_subst(name, hash_bits, val_bits)

  cons_entry = merkle_gen.generate_put_block_by_hash(num_val_bits)
  merkle_replace_vars(cons_entry, new_spec_file, subst, extra_assigns)

def expand_hashfree(new_spec_file, hash_bits):
  tokens = ["FREE_BLOCK_BY_HASH"]
  tokens += hash_bits
  new_spec_file.write(" ".join(tokens) + "\n")

def ram_subst(name, index, vals, out_hash_vars):
  global db_hash_vars
  new_var = False
  rv = None

  if name.startswith("VAR"):
    parts = name.split("_")

    if parts[1] == "INDEX":
      rv = index
    elif parts[1] == "VALUE":
      rv = vals[int(parts[2])]
      if rv.startswith("V") and not rv in variables.named_vars:
          new_var = True
    elif parts[1] == "INHASH":
      rv = db_hash_vars[int(parts[2])]["name"]
    elif parts[1] == "OUTHASH":
      rv = out_hash_vars[int(parts[2])]["name"]
      
  if rv == None:
    raise Exception("ram_subst: Unknown var: " + name)

  return rv, new_var

def block_subst(name, hash_bits, val_bits):
  new_var = False
  rv = None

  if name.startswith("VAR"):
    parts = name.split("_")

    if parts[1] == "VALUE":
      rv = val_bits[int(parts[2])]
    elif parts[1] == "INHASH" or parts[1] == "OUTHASH":
      rv = hash_bits[int(parts[2])]
        
  if rv == None:
    raise Exception("block_subst: Unknown var: " + name)
  elif rv.startswith("V") and not rv in variables.named_vars:
    new_var = True

  return rv, new_var
    
def merkle_replace_vars(cons_entry, new_spec_file, subst, extra_assigns):
  new_spec_file.write("\n".join(extra_assigns) + "\n")
  
  subst_entry = merkle.SubstEntry()
  
  def subst_vars(name):
    new_name, create_var = subst(name)
    if create_var:
      variables.read_var(new_name)
      
    # Get the final name of the variable so that we can fill the template.
    _, subst_entry.table[name] = to_var(new_name)
    
  map(subst_vars, cons_entry.external_vars)
  subst_entry.internal_var_offset = variables.add_vars(cons_entry.num_internal_vars)
  
  global num_substs
  merkle_gen.add_subst_entry(str(num_substs), subst_entry)
  new_spec_file.write("EXTERN %s %d\n" % (cons_entry.key, num_substs))
  num_substs += 1
  
def template_subst(dst_file, src_tmpl, subst_entry, cons_offset=0, shuffled_indices=None):
  for line in src_tmpl:
    i = 0
    words = line.split()
    last = len(words) - 1
    
    for word in words:
      if word[0] == "$":
        if word.startswith("${CONS_"):
          dst_file.write(str(int(word[7:-1]) + cons_offset))
        else:
          name = word[2:-1]
          if name in subst_entry.table:
            dst_file.write(subst_entry.table[name])
          else:
            var_num = int(name[1:]) + subst_entry.internal_var_offset
            
            if shuffled_indices != None:
              var_num = shuffled_indices[var_num] + 1
              dst_file.write(str(var_num))
            else:
              dst_file.write("V%d" % var_num)
      else:
        dst_file.write(word)
      
      if i < last:
        dst_file.write(" ")
      i += 1
      
    dst_file.write("\n")

def parse_spec_file(spec_file):
  def r(spec_file, tag, vt):
    process_spec_section(spec_file, START_TAG + tag, END_TAG + tag, \
                         lambda line: vt.read_var(line))

  global input_vars
  input_vars = var_table.VarTable(0)
  insert_db_hash_inputs(spec_file)
  r(spec_file, INPUT_TAG, input_vars) #number inputs starting at 0
  
  global output_vars
  output_vars = var_table.VarTable(input_vars.num_vars) #number outputs starting where inputs left off
  r(spec_file, OUTPUT_TAG, output_vars) 
  
  global variables
  variables = var_table.VarTable(0) #start over again in numbering variables
  r(spec_file, VARIABLES_TAG, variables) 

  spec_file.seek(0)

#  	print "INPUT_VARS:", input_vars
#  	print "OUTPUT_VARS:", output_vars
#  	print "VARIABLES:", variables

def get_bits_signed_difference(arg0, var0, arg1, var1):
  adjusted_na1 = var0["na"]
  if (var0["type"] == "uint"):
    adjusted_na1 = adjusted_na1 + 1
  adjusted_na2 = var1["na"]
  if (var1["type"] == "uint"):
    adjusted_na2 = adjusted_na2 + 1
  na1 = max(adjusted_na1, adjusted_na2)
  nb1 = max(var0["nb"], var1["nb"])

  if (nb1 == 0):
    # Special case for compare against 0.
    if (arg0 == "0" or arg1 == "0"):
      na1 = na1;
    else:
      na1 = na1 + 1;
  else:
    # Special case for compare against 0.
    if (arg0 == "0" or arg1 == "0"):
      na1 = na1;
    else:
      na1 = na1 + nb1 + 1;

  return (na1, nb1);

def less_than_as_basic_constraints(arg0, arg1, target):
  (var0, _) = to_var(arg0)
  (var1, _) = to_var(arg1)

  (na1, nb1) = get_bits_signed_difference(arg0, var0, arg1, var1);

  if (nb1 == 0):
    return less_than_as_basic_constraints_i(na1, arg0, arg1, target)
  else:
    return less_than_as_basic_constraints_f(na1, nb1, arg0, arg1, target)

def less_than_as_basic_constraints_i(na2, arg0, arg1, target):
  def f(varName):
    return "%s$%s" % (target, varName)
  toRet = []

  # Check the relationship between Ni and N
  # Python ints are arbitrary precision! Yay!
  pot = 1
  diffFromPot = ""
#   Nsum = "( ) * ( ) + ( "
  for i in range(0, na2-1):
    Ni = f("N%d" % (i))
    toRet += ["( %s ) * ( %s - %s ) + ( )" % (Ni, pot, Ni)]
    diffFromPot += " - %s" % (Ni)
    pot = pot * 2
  diffFromPot += " + %s" % (pot)

  # Check relationship between Mlt, Meq, Mgt
  Mlt = f("Mlt")
  Meq = f("Meq")
  Mgt = f("Mgt")
  toRet += [
    "( %s ) * ( %s - 1 ) + ( )" % (Mlt, Mlt),
    "( %s ) * ( %s - 1 ) + ( )" % (Meq, Meq),
    "( %s ) * ( %s - 1 ) + ( )" % (Mgt, Mgt),
    "( ) * ( ) + ( %s + %s + %s - 1 )" % (Mlt, Meq, Mgt),
    ]

  # If Mlt, check Y1 < Y2
  toRet += ["( %s ) * ( %s - %s + %s ) + ( )" %
    (Mlt, arg0, arg1, diffFromPot)]

  # If Meq, check Y1 = Y2
  toRet += ["( %s ) * ( %s - %s ) + ( )" %
    (Meq, arg0, arg1)]

  # If Mlt, check Y2 < Y1
  toRet += ["( %s ) * ( %s - %s + %s ) + ( )" %
    (Mgt, arg1, arg0, diffFromPot)]

  # Output matching constraint
  toRet += ["( ) * ( ) + ( %s  - %s )" % (f("Mlt"), target)]

  return toRet


def less_than_as_basic_constraints_f(na2, nb2, arg0, arg1, target):
  def f(varName):
    return "%s$%s" % (target, varName)
  toRet = []

  #XXX Currently we ignore the type system, and always use fixed-size less than gates.
  #When the type system starts being more agressive, we will use its bounds instead.

  #na2 = 100
  #nb2 = 32

  #print "Warning - na=", na2, "/nb=", nb2," '<' gate being used, ignoring input type!";

  # Check the relationship between Ni and N
  # Python ints are arbitrary precision! Yay!
  pot = 1
  Nsum = "( ) * ( ) + ( "
  for i in range(0, na2):
    Ni = f("N%d" % (i))
    toRet += ["( %s ) * ( %s - %s ) + ( )" % (Ni, pot, Ni)]
    pot = pot * 2
    Nsum += "- %s " % (Ni)
  Nsum += "+ %s + %s ) " % (f("N"), pot)
  toRet += [Nsum]

  # Check relationship between Di and D
  Dsum = "( ) * ( ) + ( "
  Dcount = "( ) * ( ) + ( "
  for i in range(0, nb2+1):
    Di = f("D%d" % (i))
    toRet += ["( %s ) * ( %s - 1 ) + ( )" % (Di, Di)]
    Dsum += "- %s * %s " % (2**(nb2 - i),Di)
    Dcount += "+ %s " % (Di)
  Dsum += "+ %s * %s ) " % (2**nb2, f("D"))
  Dcount += " - 1 ) "
  toRet += [Dsum, Dcount]

  # Check relationship between Mlt, Meq, Mgt
  Mlt = f("Mlt")
  Meq = f("Meq")
  Mgt = f("Mgt")
  toRet += [
    "( %s ) * ( %s - 1 ) + ( )" % (Mlt, Mlt),
    "( %s ) * ( %s - 1 ) + ( )" % (Meq, Meq),
    "( %s ) * ( %s - 1 ) + ( )" % (Mgt, Mgt),
    "( ) * ( ) + ( %s + %s + %s - 1 )" % (Mlt, Meq, Mgt),
    ]

  # Check relationship between N, D, and ND
  toRet += ["( %s ) * ( %s ) + ( - %s )" % (f("N"), f("D"), f("ND"))]

  # If Mlt, check Y1 < Y2
  toRet += ["( %s ) * ( %s - %s - %s ) + ( )" %
    (Mlt, arg0, arg1, f("ND"))]

  # If Meq, check Y1 = Y2
  toRet += ["( %s ) * ( %s - %s ) + ( )" %
    (Meq, arg0, arg1)]

  # If Mlt, check Y2 < Y1
  toRet += ["( %s ) * ( %s - %s - %s ) + ( )" %
    (Mgt, arg1, arg0, f("ND"))]

  # Output matching constraint
  toRet += ["( ) * ( ) + ( %s  - %s )" % (f("Mlt"), target)]
  return toRet

def not_equal_as_basic_constraints(arg0, arg1, target):
  def f(varName):
    return "%s$%s" % (target, varName)
  toRet = []

  X1 = arg0
  X2 = arg1
  M = f("M")
  Y = target

  if target in output_vars.named_vars and framework == "GINGER":
    Y = f("M2")

  # Constraint: Y - (X1 - X2) M
  toRet += ["( %s ) * ( %s - %s ) + ( - %s )" % (M, X1, X2, Y)]
  # Constraint: (X1 - X2) - (X1 - X2)*Y = Y*(X1 - X2) + (- X1 + X2) (multiplying by -1)
  toRet += ["( %s ) * ( %s - %s ) + ( - %s + %s )" % (Y, X1, X2, X1, X2)]

  if target in output_vars.named_vars and framework == "GINGER":
    toRet += ["( ) * ( ) + ( %s - %s )" % (Y, target)]

  return toRet

def division_as_basic_constraints(arg0, op, arg1, target):
  def pn(name):
    return "%s$%s" % (target, name)
  def pn_type(name, templatename):
    return "%s$%s" % (target, name)

  a = arg0
  b = arg1

  (a_var, _) = to_var(arg0)
  (b_var, _) = to_var(arg1)

  if (a_var["nb"] != 0 or b_var["nb"] != 0):
    raise Exception("Constraints for rational division not yet implemented")

  q = pn_type("Q",a)
  r = pn_type("R",b)
  rless0 = pn("Rless0")
  rnon0 = pn("Rnon0")
  bless0 = pn("Bless0")
  aless0 = pn("Aless0")
  qless0 = pn("Qless0") #Not satisfiable if q is not an N bit integer
  absr = pn_type("Absr",r)
  absb = pn_type("Absb",b)
  absrlessabsb = pn("Absrlessabsb")

  computation = []
  computation += to_basic_constraints_lines("".join([
      "%s < 0 - %s\n" % (r, rless0),
      "%s != 0 - %s\n" % (r, rnon0),
      "%s < 0 - %s\n" % (b, bless0),
      "%s < 0 - %s\n" % (a, aless0),
      "%s < 0 - %s\n" % (q, qless0),
      "( %s ) * ( -2 * %s ) + ( %s - %s )\n" %
          (rless0, r, r, absr),
      "( %s ) * ( -2 * %s ) + ( %s - %s )\n" %
          (bless0, b, b, absb),
      "%s < %s - %s\n" % (absr, absb, absrlessabsb),
      "( %s ) * ( %s ) + ( %s - %s )\n" %
          (b, q, r, a),
      "( ) * ( ) + ( 1 - %s )\n" % (absrlessabsb),
      "( %s ) * ( %s - %s ) + ( )\n" % (rnon0, rless0, aless0)
    ]))

  if (op == "/"):
    computation += to_basic_constraints("( ) * ( ) + ( %s - %s )\n"
      % (q, target))
  elif (op == "%"):
    computation += to_basic_constraints("( ) * ( ) + ( %s - %s )\n"
      % (r, target))
  else:
    raise Exception("Assertion error - bad division op %s" % (op))

  return computation

def split_int_le_as_basic_constraints(terms):
  # No auxilliary variables needed.
  toRet = []
  terms = collections.deque(terms)

  terms.popleft() #SIL
  typename = terms.popleft() #uint or int
  signed = {
    "int": True,
    "uint": False,
    } [typename]
  terms.popleft() #bits
  numBits = int(terms.popleft()) #length
  terms.popleft() #X
  toSplit = terms.popleft()
  terms.popleft() #Y0

  #output_start = int(terms.pop(0)[1:]) #output starting variable (must start with V. )
  output_start_var =  terms.popleft() # <output starting variable>
  match = re.search("(.*[^\d])(\d+)", output_start_var)
  if not match:
    raise Exception("split_int_le_as_basic_constraints: invalid output var: " + output_start_var)
  prefix = match.group(1)
  output_start = int(match.group(2))

  matchConstraint = ""
  pot = 1
  for i in range(0, numBits):
    #bitvar = "V%d"%(output_start + i)
    bitvar = "%s%d" % (prefix, output_start + i)
    #Check that this var is boolean in value
    toRet += ["( %s ) * ( %s - 1 ) + ( )" % (bitvar, bitvar)]

    signedPot = pot
    if (i == numBits - 1 and signed):
      signedPot = -pot
    matchConstraint += "+ %s * %s " % (signedPot, bitvar)
    pot *= 2

  toRet += ["( ) * ( ) + ( %s - %s )" % (matchConstraint, toSplit)]

  return toRet

def split_unsignedint_as_basic_constraints(terms):
  # No auxilliary variables needed.
  toRet = []
  terms = collections.deque(terms)

  terms.popleft() # "SI"
  toSplit = terms.popleft()
  terms.popleft() # "into"
  numBits = int(terms.popleft()) # <length>
  terms.popleft() # "bits"
  terms.popleft() # "at"

  output_start_var =  terms.popleft() # <output starting variable>
  match = re.search("(.*[^\d])(\d+)", output_start_var)
  if not match:
    raise Exception("split_unsignedint_as_basic_constraints: invalid output var: " + output_start_var)
  prefix = match.group(1)
  output_start = int(match.group(2))

  matchConstraint = ""
  for i in range(0, numBits):
    bitvar = "%s%d" % (prefix, output_start + i)
    #Check that this var is boolean in value
    toRet += ["( %s ) * ( %s - 1 ) + ( )" % (bitvar, bitvar)]

    coeff = 1 << (numBits - 1 - i)
    matchConstraint += "+ %s * %s " % (coeff, bitvar)

  toRet += ["( ) * ( ) + ( %s - %s )" % (matchConstraint, toSplit)]

  return toRet


def is_exogenous_cons(line):
  # These commands take exogenous values, and so they don't belong in a QAP
  ops = ["DB_GET_SIBLING_HASH", "DB_GET_BITS", "DB_PUT_BITS", \
         "GET_BLOCK_BY_HASH", "PUT_BLOCK_BY_HASH", "FREE_BLOCK_BY_HASH" \
         "GENERICPUT", "GENERICFREE", "PRINTF", "MATRIX_VEC_MUL"]
  for op in ops:
    if line.startswith(op):
      return True

  return False

def to_basic_constraints_lines(text):
  toRet = []

  lines = text.splitlines()
  for line in lines:
    line = line.strip()
    toRet += to_basic_constraints(line)

  return toRet

#converts a general constraint to a list of basic constraints, or throws an error if this is not possible.
def to_basic_constraints(line):
  #shortcircuiting
  if (line.startswith("}") or line.startswith("shortcircuit")):
    return []

  toRet = []
  if is_exogenous_cons(line) or line == "":
    pass
  elif line.startswith("ASSERT_POLY_ZERO"):
    #Trim off first token and pass remainder of line as raw constraint
    terms = line.split(" ",1)
    toRet = [terms[1]]
  elif line.startswith("ASSERT_ZERO"):
    terms = line.split()
    toRet = ["( ) * ( ) + ( %s )" % (terms[1])]
  elif "!=" in line: #Format of line is Var != Var - Var
    terms = line.split()
    toRet = not_equal_as_basic_constraints(terms[0], terms[2], terms[4])
  elif "<" in line: #Format of line is Var < Var - Var
    terms = line.split()
    toRet = less_than_as_basic_constraints(terms[0], terms[2], terms[4])
  elif "/" in line or "%" in line: #Format of line is Var op Var - Var
    terms = line.split()
    toRet = division_as_basic_constraints(terms[0], terms[1], terms[2], terms[4])
  elif line.startswith("SIL"):
    terms = line.split()
    toRet = split_int_le_as_basic_constraints(terms)
  elif line.startswith("SI"):
    terms = line.split()
    toRet = split_unsignedint_as_basic_constraints(terms)
  elif line.startswith("GENERICGET"):
    #Verify that all of the bits retrieved are 0 or 1 values.
    terms = line.split()
    hash_vars_start = 5
    hash_vars_end = hash_vars_start + int(terms[3])
    terms = terms[hash_vars_end:]
    val_bits_start = 3
    val_bits_end = val_bits_start + int(terms[1])
    val_bits = terms[val_bits_start : val_bits_end]
    toRet = []
    for valbit in val_bits:
      toRet += ["( %s ) * ( %s - 1 ) + ( )" %
        (valbit, valbit)]
  else:
    toRet = [line]

  toRet_expanded = []
  for bc in toRet:
    toRet_expanded += [expand_basic_constraint(bc)]
  toRet = toRet_expanded

  return toRet

def expand_basic_constraint(bc):
  tokens = collections.deque(bc.split())
  expansion = ""

  global framework
  if (framework == "GINGER"):
    tokens.appendleft("(")
    tokens.append(")")
    expansion += expand_polynomial_str(tokens)
  if (framework == "ZAATAR"):
    expansion += "( "
    expansion += expand_polynomial_str(tokens)
    expansion += " ) "
    expansion += tokens.popleft()
    expansion += " ( "
    expansion += expand_polynomial_str(tokens)
    expansion += " ) "
    expansion += tokens.popleft()
    expansion += " ( "
    expansion += expand_polynomial_str(tokens)
    expansion += " )"

  return expansion

def expand_polynomial_str(tokens):
  expanded = expand_polynomial(tokens)

  expanded_list = []
  for term in expanded:
    expanded_list += [" * ".join(term)]
  return " + ".join(expanded_list)

#Takes a polynomial which starts with a (, reads a polynomial until the matching ) is reached,
#and returns the expanded polynomial of the terms inside the parens.
#An expanded polynomial always has terms of the form constant * v1 * ... vn
def expand_polynomial(tokens):
  nesting = 1

  if (tokens[0] != "("):
    raise Exception("expand_polynomial: Format error: " + str(tokens))
  tokens.popleft()

  multiply = []
  expansion = {}

  while(nesting > 0):
    if (tokens[0] == "("): #Recurse
      subPoly = expand_polynomial(tokens)
      if (multiply == []):
        multiply = subPoly
      else:
        newMult = []
        for term1 in multiply:
          for term2 in subPoly:
            newMult += product_term(term1,term2)
        multiply = newMult
    else:
      token = tokens.popleft()

      if (token == ")" or token == "+" or token == "-"):
        for term in multiply:
          expand_add_term(expansion, term)
        multiply = []

      if (token == ""):
        continue
      elif (token == ")"):
        nesting = nesting - 1
      elif (token == "+"):
        pass
      elif (token == "-"):
        multiply += [["-1"]]
      elif (token == "*"):
        pass
      else:
        if (multiply == []):
          multiply = product_term(["1"], [token])
        else:
          newMult = []
          for term1 in multiply:
            newMult += product_term([token], term1)
          multiply = newMult

  for term in multiply:
    expand_add_term(expansion, term)
  return expansion.values()

def expand_add_term(expansion, termlist):
  termlistNoConst = termlist
  mults = 1
  try:
    a = int(termlist[0])
    mults = a
    termlistNoConst = termlist[1:]
  except:
    pass

  termlistNoConst.sort()
  key = "!".join(termlistNoConst)
  if key in expansion:
    gotlist = expansion[key]
    del expansion[key]
    multo = int(gotlist[0])
    multo += mults;
    gotlist[0] = str(multo)
    if (multo != 0):
      expansion[key] = gotlist
  else:
    termo = [str(mults)]
    termo += termlistNoConst
    expansion[key] = termo

#Returns a list holding the list of the union of two factor lists, but always puts the constant term at the start of the union
#Note that if the constant term ends up being 0, the empty list is returned
def product_term(a, b):
  if (a == [] or b == [] or a == ['']):
    raise Exception("Assertion error")

  aHasConst = True
  bHasConst = True
  try:
    int(a[0])
  except:
    aHasConst = False

  try:
    int(b[0])
  except:
    bHasConst = False

  if (aHasConst and bHasConst):
    product = int(a[0]) * int(b[0])
    if (product == 0):
      return []
    return [[str(product)] + a[1:] + b[1:]]
  if (bHasConst):
    return [[b[0]] + a + b[1:]]
  return [a + b]

#converts a basic constraint (a degree two polynomial constraint) to a tuple useful in filling in the gamma0 / gamma1/2 vectors.
def parse_basic_constraint(line):
  #print constraint
  deg1_pos = []
  deg1_coeff = []
  deg2_pos = []
  deg2_coeff = []
  ip_op_pos = []
  ip_op_coeff = []
  consts = []

  #Split on terms
  line = re.sub("\\s+\\*\\s+", "*", line)
  terms = line.split()
  while terms != []:
    neg = False
    while True:
      if (terms[0] == "+"):
        terms = terms[1:]
      elif (terms[0] == "-"):
        neg = not neg
        terms = terms[1:]
      elif (terms[0] == ""):
        terms = terms[1:]
      else:
        break

    term = terms[0]
    terms = terms[1:]

    coeff = "1"
    factors = term.split("*")
    for i in range(0, len(factors)):
      factor = factors[i]
      if factor[i].isdigit() or (factor[i] == "-"):
        coeff = factor
        factors[i] = ""
        break
    factors = filter(None, factors)
    term = "*".join(factors) # Factors not including the coeff

    if neg:
      coeff = "-" + coeff

    if (term != ""):
      if term in input_vars.named_vars: #Input / Output
        index = input_vars.named_vars[term]["index"]
        ip_op_pos.append(index)
        ip_op_coeff.append(coeff)
      elif term in output_vars.named_vars:
        index = output_vars.named_vars[term]["index"]
        ip_op_pos.append(index)
        ip_op_coeff.append(coeff)
      else: # Variables
        degree = term.count("*") + 1
        if degree >= 3:
          print "ERROR: degree of a term more than 2 in constraint"
          print line
          sys.exit(1)

        if degree == 1:
          index = variables.named_vars[term]["index"]
          deg1_pos.append(" F1_index[%d] " % (index))
          deg1_coeff.append(coeff)
        elif degree == 2:
          term_vars = term.split("*")
          index1 = variables.named_vars[term_vars[0]]["index"]
          index2 = variables.named_vars[term_vars[1]]["index"]
          index = " F1_index[%d] * num_vars + F1_index[%d] " % (index1, index2)
          deg2_pos.append(index)
          deg2_coeff.append(coeff)
    else:
      consts.append(coeff)

  return (consts, ip_op_pos, ip_op_coeff, deg1_pos, deg1_coeff, deg2_pos, deg2_coeff)

def generate_ginger_comp_params():
  num_constraints = chi
  num_inputs = input_vars.num_vars
  num_outputs = output_vars.num_vars
  num_vars = variables.num_vars
  file_name_f1_index = "bin/" + class_name + ".f1index"

  code = """
  num_cons = %s;
  num_inputs = %s;
  num_outputs = %s;
  num_vars = %s;
  const char *file_name_f1_index = \"%s\";
  """ % (num_constraints, num_inputs, num_outputs, num_vars, file_name_f1_index)

  if (printMetrics):
    print("""
metric_num_constraints %s %d
metric_num_input_vars %s %d
metric_num_output_vars %s %d
metric_num_intermediate_vars %s %d
    """ % (class_name, num_constraints, class_name, num_inputs, class_name, num_outputs, class_name, num_vars))

  return code

def generate_zaatar_comp_params():
  num_constraints = chi #count_lines(text, CONSTRAINTS_TAG)
  num_inputs = input_vars.num_vars #count_lines(text, INPUT_TAG)
  num_outputs = output_vars.num_vars #count_lines(text, OUTPUT_TAG)
  num_vars = variables.num_vars # count_lines(text, VARIABLES_TAG)
  file_name_qap = "bin/" + class_name + ".qap"
  file_name_f1_index = "bin/" + class_name + ".f1index"

  num_aij = NzA
  num_bij = NzB
  num_cij = NzC

  code = """
  num_cons = %s;
  num_inputs = %s;
  num_outputs = %s;
  num_vars = %s;
  num_aij = %s;
  num_bij = %s;
  num_cij = %s;
  const char *file_name_qap = \"%s\";
  const char *file_name_f1_index = \"%s\";
  """ % (num_constraints, num_inputs, num_outputs, num_vars, num_aij, num_bij, num_cij, file_name_qap, file_name_f1_index)

  if (printMetrics):
    print("""
metric_num_constraints %s %d
metric_num_input_vars %s %d
metric_num_output_vars %s %d
metric_num_intermediate_vars %s %d
metric_num_Nz(A) %s %d
metric_num_Nz(B) %s %d
metric_num_Nz(C) %s %d
    """ % (class_name, num_constraints, class_name, num_inputs,
    class_name, num_outputs, class_name, num_vars, class_name, num_aij,
    class_name, num_bij, class_name, num_cij))

  return code

def convert_to_compressed_polynomial(j, polynomial, shuffled_indices):
#   num_inputs = input_vars.num_vars #count_lines(text, INPUT_TAG)
#   num_outputs = output_vars.num_vars #count_lines(text, OUTPUT_TAG)
  num_vars = variables.num_vars # count_lines(text, VARIABLES_TAG)

  i = -1
  coefficient = 0
  entries = []

  terms = polynomial.split(" + ")
  for term in terms:
    i = -1
    coefficient = 0
    if term.find(" * ") == -1:
      # a constant term
      i = 0
      term = term.lstrip()
      term = term.rstrip()
      if (0 == int(term)):
        continue
      else:
        coefficient = term
    else:
      (coefficient, variable) = term.split(" * ")
      index = int(variable[1:]) #remove the first character and store in index
      if (variable.startswith("V")):
        i = 1 + shuffled_indices[index]
      elif (variable.startswith("I")):
        i = 1 + num_vars + index
      elif (variable.startswith("O")):
        i = 1 + num_vars + index

    entries += ["%d %d %s\n" % (i, j, coefficient)]
  return "".join(entries)

def append_files(fp, file_name_to_append):
  with open(file_name_to_append) as file_object:
    for line in file_object:
      fp.write(line);

def generate_zaatar_matrices(spec_file, shuffled_indices, qap_file_name):

  #print "In generate_zaatar_matrices"
  file_matrix_a = qap_file_name + ".matrix_a";
  file_matrix_b = qap_file_name + ".matrix_b";
  file_matrix_c = qap_file_name + ".matrix_c";

  fp_matrix_a = open(file_matrix_a, "w");
  fp_matrix_b = open(file_matrix_b, "w");
  fp_matrix_c = open(file_matrix_c, "w");

  #Alist = []
  #Blist = []
  #Clist = []

  global NzA
  global NzB
  global NzC

  NzA = 0
  NzB = 0
  NzC = 0

  if (verbose):
    print("Writing QAP matrices to "+qap_file_name);

  num_constraints = 0
  storage_ops_constraints = 0
  split_ops = 0
  num_normal_constraints = 0
  j = 1

  # Why do I need this closure_vars nonsense? See:
  # http://eli.thegreenplace.net/2011/05/15/understanding-unboundlocalerror-in-python/#id8
  # I hate Python.
  closure_vars = {}
  closure_vars["num_constraints"] = num_constraints
  closure_vars["storage_ops_constraints"] = storage_ops_constraints
  closure_vars["split_ops"] = split_ops
  closure_vars["num_normal_constraints"] = num_normal_constraints
  closure_vars["j"] = j
  closure_vars["fp_matrix_a"] = fp_matrix_a
  closure_vars["fp_matrix_b"] = fp_matrix_b
  closure_vars["fp_matrix_c"] = fp_matrix_c

  def f(line):
    global NzA, NzB, NzC

    num_constraints = closure_vars["num_constraints"]
    storage_ops_constraints = closure_vars["storage_ops_constraints"]
    split_ops = closure_vars["split_ops"]
    num_normal_constraints = closure_vars["num_normal_constraints"]
    j = closure_vars["j"]
    fp_matrix_a = closure_vars["fp_matrix_a"]
    fp_matrix_b = closure_vars["fp_matrix_b"]
    fp_matrix_c = closure_vars["fp_matrix_c"]

    line = line.strip()
    
    if line.startswith("EXTERN"):
      terms = line.split()
      cons_entry = merkle_gen.get_cons_entry(terms[1])
      subst_entry = merkle_gen.get_subst_entry(terms[2])
      
      for old_name, new_name in subst_entry.table.iteritems():
        var_num = int(new_name[1:])
        if new_name[0] == "I" or new_name[0] == "O":
          var_num += variables.num_vars
        else:
          var_num = shuffled_indices[var_num]
        var_num += 1
        
        subst_entry.table[old_name] = str(var_num)
      
      for v in zip(["qapA", "qapB", "qapC"], [fp_matrix_a, fp_matrix_b, fp_matrix_c]):
        key, f = v
        with open(cons_entry.tmpls[key], "r") as src_tmpl:  
          template_subst(f, src_tmpl, subst_entry, j - 1, shuffled_indices)
          
      j += cons_entry.num_constraints
      num_constraints += cons_entry.num_constraints
      storage_ops_constraints += cons_entry.num_constraints

      NzA += cons_entry.Aij
      NzB += cons_entry.Bij
      NzC += cons_entry.Cij
    else:
      basic_constraints = to_basic_constraints(line)
      if line.startswith("SI") or line.startswith("SIL"):
        split_ops += len(basic_constraints)
      else:
        num_normal_constraints += len(basic_constraints)

      for bc in basic_constraints:
        tokens = collections.deque(bc.split())
        (nasub, A2) = expand_polynomial_matrixrow(tokens)
        A3 = convert_to_compressed_polynomial(j, A2, shuffled_indices)
        #A += A2 + "\n"
        #Alist += [A3]
        fp_matrix_a.write(A3);
        NzA = NzA + nasub
        if (tokens.popleft() != "*"):
          raise Exception("Format error")
        (bsub, B2) = expand_polynomial_matrixrow(tokens)
        #B += B2 + "\n"
        B3 = convert_to_compressed_polynomial(j, B2, shuffled_indices,)
        #Blist += [B3]
        fp_matrix_b.write(B3);
        NzB = NzB + bsub
        if (tokens.popleft() != "+"):
          raise Exception("Format error")
        (csub, C2) = expand_polynomial_matrixrow(tokens)
        NzC = NzC + csub
        C3 = convert_to_compressed_polynomial(j, C2, shuffled_indices)
        #C += C2 + "\n"
        #Clist += [C3]
        fp_matrix_c.write(C3)
  
        j = j + 1
        num_constraints = num_constraints + 1

    closure_vars["num_constraints"] = num_constraints
    closure_vars["storage_ops_constraints"] = storage_ops_constraints
    closure_vars["split_ops"] = split_ops
    closure_vars["num_normal_constraints"] = num_normal_constraints
    closure_vars["j"] = j
    closure_vars["fp_matrix_a"] = fp_matrix_a
    closure_vars["fp_matrix_b"] = fp_matrix_b
    closure_vars["fp_matrix_c"] = fp_matrix_c

  process_spec_section(spec_file, START_TAG + CONSTRAINTS_TAG, END_TAG + CONSTRAINTS_TAG, f)

  num_constraints = closure_vars["num_constraints"]
  storage_ops_constraints = closure_vars["storage_ops_constraints"]
  split_ops = closure_vars["split_ops"]
  num_normal_constraints = closure_vars["num_normal_constraints"]
  j = closure_vars["j"]
  fp_matrix_a = closure_vars["fp_matrix_a"]
  fp_matrix_b = closure_vars["fp_matrix_b"]
  fp_matrix_c = closure_vars["fp_matrix_c"]

  # The following is much faster than repeated concatenation
  #A = ''.join(Alist)
  #B = ''.join(Blist)
  #C = ''.join(Clist)

  global chi
  # set it to next power of 2 minus 1 so that \chi+1 is a power of 2
  num = num_constraints + 1;
  #bit_length = num.bit_length();
  #chi = int(math.pow(2, bit_length)) - 1
  chi = int(pow(2, math.ceil(math.log(num, 2)))) - 1
  #chi = num_constraints

  print "metric_num_constraints_for_storage_ops %s %d" % (class_name, storage_ops_constraints);
  print "metric_num_constraints_for_split_ops %s %d" % (class_name, split_ops);
  print "metric_num_constraints_for_other_ops %s %d" % (class_name, num_normal_constraints);
  print "metric_num_constraints_before_round %s %d" % (class_name, num_constraints);
  print "metric_num_constraints_after_round %s %d" % (class_name, chi);

  print "metric_num_constraints_nonpot %s %d" % (class_name, num_constraints);

  if NzA == 0:
    NzA = 1
    fp_matrix_a.write("0 0 0\n")

  if NzB == 0:
    NzB = 1
    fp_matrix_b.write("0 0 0\n")

  if NzC == 0:
    NzC = 1
    fp_matrix_c.write("0 0 0\n")


  fp_matrix_a.close()
  fp_matrix_b.close()
  fp_matrix_c.close()

  if (verbose):
    print("Merging QAP matrices, will re-write to "+qap_file_name);

  fp = open(qap_file_name, "w")
  append_files(fp, file_matrix_a)
  fp.write("\n");
  append_files(fp, file_matrix_b)
  fp.write("\n");
  append_files(fp, file_matrix_c)
  fp.write("\n");
  fp.close();

  os.system("rm " + file_matrix_a)
  os.system("rm " + file_matrix_b)
  os.system("rm " + file_matrix_c)

  return (NzA, NzB, NzC, chi)

# Expands a polynomial, and replaces variable names with the (unshuffled) variable numbering
def expand_polynomial_matrixrow(tokens):
  expanded = expand_polynomial(tokens)

  variablesChanged = []
  for term in expanded:
    newList = []
    for factor in term:
      (_, renumbered_name) = to_var(factor)
      newList += [renumbered_name]

    variablesChanged += [newList]

  expanded = variablesChanged

  if (expanded == []):
    return (0, "0")

  numNonZeroTerms = 0
  expanded_list = []
  for term in expanded:
    numNonZeroTerms = numNonZeroTerms + 1
    expanded_list += [" * ".join(term)]
  return (numNonZeroTerms, " + ".join(expanded_list))

def generate_gamma0(spec_file):
#   num_deg1_terms = 0
#   num_deg2_terms = 0
#   deg1_pos = []
#   deg2_pos = []
#   ip_op_pos = []
#   deg1_alpha = []
#   deg2_alpha = []
#   ip_op_alpha = []
#   deg1_coeff = []
#   deg2_coeff = []
#   ip_op_coeff = []
#   count = 0

  constraint_id = 0
  code = []

  # Why do I need this closure_vars nonsense? See:
  # http://eli.thegreenplace.net/2011/05/15/understanding-unboundlocalerror-in-python/#id8
  # I hate Python.
  closure_vars = {}
  closure_vars["constraint_id"] = constraint_id
  closure_vars["code"] = code

  def f(line):
    constraint_id = closure_vars["constraint_id"]
    code = closure_vars["code"]

    basic_constraints = to_basic_constraints(line)
    for bc in basic_constraints:
#       (consts, io_varid, io_coeff, deg1_varid, deg1_coeff, deg2_varid, deg2_coeff) = parse_basic_constraint(bc)
      (consts, io_varid, io_coeff, _, _, _, _) = parse_basic_constraint(bc)

      # use alpha[constraint_id] and fill in \gamma_0

      #literal const * input/output variable constants
      term_id = 0
      for var_id in io_varid:
        code+= ["G %s %d %d" % (io_coeff[term_id], constraint_id, var_id)]
        term_id = term_id + 1

      #literal constants
      for const in consts:
        code+= ["C %s %d 0" % (const, constraint_id)]

      constraint_id = constraint_id + 1

    closure_vars["constraint_id"] = constraint_id
    closure_vars["code"] = code

  process_spec_section(spec_file, START_TAG + CONSTRAINTS_TAG, END_TAG + CONSTRAINTS_TAG, f)
  spec_file.seek(0)

  constraint_id = closure_vars["constraint_id"]
  code = closure_vars["code"]

  #We have just discovered how many basic constraints are in the specification.
  global chi
  chi = constraint_id

  if (printMetrics):
    print "metric_num_gamma0 %s %d" % (class_name, len(code))

  return "\n".join(code)

#always called BEFORE generate_gamma0 (in the actual ginger framework)
def generate_gamma12(spec_file):
#   num_deg1_terms = 0
#   num_deg2_terms = 0
#   deg1_pos = []
#   deg2_pos = []
#   ip_op_pos = []
#   deg1_alpha = []
#   deg2_alpha = []
#   ip_op_alpha = []
  deg1_coeff = []
  deg2_coeff = []
#   ip_op_coeff = []
#   count = 0

  constraint_id = 0
  code = []

  # Why do I need this closure_vars nonsense? See:
  # http://eli.thegreenplace.net/2011/05/15/understanding-unboundlocalerror-in-python/#id8
  # I hate Python.
  closure_vars = {}
  closure_vars["deg1_coeff"] = deg1_coeff
  closure_vars["deg2_coeff"] = deg2_coeff
  closure_vars["constraint_id"] = constraint_id
  closure_vars["code"] = code

  def f(line):
    deg1_coeff = closure_vars["deg1_coeff"]
    deg2_coeff = closure_vars["deg2_coeff"]
    constraint_id = closure_vars["constraint_id"]
    code = closure_vars["code"]

    basic_constraints = to_basic_constraints(line)
    for bc in basic_constraints:
#       (consts, io_varid, io_coeff, deg1_varid, deg1_coeff, deg2_varid, deg2_coeff) = parse_basic_constraint(bc)
      (_, _, _, deg1_varid, deg1_coeff, deg2_varid, deg2_coeff) = parse_basic_constraint(bc)

      # use alpha[constraint_id] and fill in \gamma_1, & \gamma_2

      term_id = 0
      for var_id in deg1_varid:
        var_id = var_id.replace(" F1_index[", "");
        var_id = var_id.replace("] ", "");
        code += ["1 %s %s %s 0" % (deg1_coeff[term_id], constraint_id, var_id) ]

      term_id = term_id + 1

      term_id = 0
      for var_id in deg2_varid:
        var_id = var_id.replace(" F1_index[", "");
        var_id = var_id.replace("] ", "");
        var_id = var_id.replace("num_vars +", "");
        (i, j) = var_id.split("*");
        code += ["2 %s %s %s %s" % (deg2_coeff[term_id], constraint_id, i, j) ]

      term_id = term_id + 1

      constraint_id = constraint_id + 1

    closure_vars["deg1_coeff"] = deg1_coeff
    closure_vars["deg2_coeff"] = deg2_coeff
    closure_vars["constraint_id"] = constraint_id
    closure_vars["code"] = code

  process_spec_section(spec_file, START_TAG + CONSTRAINTS_TAG, END_TAG + CONSTRAINTS_TAG, f)
  spec_file.seek(0)

  deg1_coeff = closure_vars["deg1_coeff"]
  deg2_coeff = closure_vars["deg2_coeff"]
  constraint_id = closure_vars["constraint_id"]
  code = closure_vars["code"]

  #We have just discovered how many basic constraints are in the specification.
  global chi
  chi = constraint_id

  if (printMetrics):
    print "metric_num_gamma12 %s %d" % (class_name, len(code))

  return "\n".join(code)

##########################
## Generate computation dynamic (i.e. with pws file)
##########################

#Returns (null, varname) if varname is not a constant or variable.
def to_var(varname):
  if varname in input_vars.named_vars:
    var = input_vars.named_vars[varname]
    return (var, "I%d" % (var["index"]))
  elif varname in output_vars.named_vars:
    var = output_vars.named_vars[varname]
    return (var, "O%d" % (var["index"]))
  elif varname in variables.named_vars:
    var = variables.named_vars[varname]
    return (var, "V%d" % (var["index"]))
  elif varname == "-":
    return (None, varname)
  elif varname[0].isdigit() or varname[0] == '-':
    #Fractions are handled in the frontend. All constants here are integers.
    constVar = {}
    constVar["name"] = varname
    constVar["type"] = "int"
    val = int(varname)
    if val == 0:
      constVar["na"] = 2
    else:
      #Number of bits in the signed integer representation
      constVar["na"] = int(math.ceil(math.log(-val if val < 0 else val + 1,2)) + 1)
    constVar["nb"] = 0
    return (constVar, varname)
  else:
    return (None, varname)

#helper function for adding variables during the prover's computation
def prover_var(prefix, varName):
  return variables.read_var("%s$%s" % (prefix, varName)) # New variable

# Honest prover's implementation of not equal
def generate_computation_not_equals(arg0, arg1, target):
  def pv(name):
    var = prover_var(target, name)
    return "V%d" % (var["index"])
  def f(varname):
    (_, renumbered_name) = to_var(varname)
    return renumbered_name

  Mvar = pv("M")
  if target in output_vars.named_vars and framework == "GINGER":
    # Make an intermediate for the output in this case
    Mvar2 = pv("M2")
    return "".join(["!= M %s X1 %s X2 %s Y %s\n" % (Mvar, f(arg0), f(arg1), Mvar2),
		   "P %s = %s E\n" %(f(target), Mvar2)])
  else:
    return "!= M %s X1 %s X2 %s Y %s\n" % (Mvar,
	f(arg0), f(arg1), f(target))

def generate_computation_divide(arg0, op, arg1, target):
  def pn(name):
    var = prover_var(target, name)
    return var["name"]
  def pn_type(name, templatename):
    var = prover_var(target, name)
    (templatevar, _) = to_var(templatename)
    var["type"] = "int" #templatevar["type"] No unsigned ints here.
    var["na"] = templatevar["na"]
    if (templatevar["type"] == "uint"):
      var["na"] = var["na"] + 1
    var["nb"] = 0 #templatevar["nb"]
    return var["name"]
  def f(varname):
    (_, renumbered_name) = to_var(varname)
    return renumbered_name

  a = arg0
  b = arg1

  (a_var, _) = to_var(arg0)
  (b_var, _) = to_var(arg1)

  if (a_var["nb"] != 0 or b_var["nb"] != 0):
    raise Exception("Constraints for rational division not yet implemented")

  q = pn_type("Q",a)
  r = pn_type("R",b)
  rless0 = pn("Rless0")
  rnon0 = pn("Rnon0")
  bless0 = pn("Bless0")
  aless0 = pn("Aless0")
  qless0 = pn("Qless0") #Not satisfiable if q is not an N bit integer
  absr = pn_type("Absr",r)
  absb = pn_type("Absb",b)
  absrlessabsb = pn("Absrlessabsb")

  computation = ""
  computation += "/I %s = %s /I %s\n" % (f(q), f(a), f(b))
  computation += "%%I %s = %s %%I %s\n" % (f(r), f(a), f(b))

  computation += generate_computation_lines("".join([
      "%s < 0 - %s\n" % (r, rless0),
      "%s != 0 - %s\n" % (r, rnon0),
      "%s < 0 - %s\n" % (b, bless0),
      "%s < 0 - %s\n" % (a, aless0),
      "%s < 0 - %s\n" % (q, qless0),
      "( %s ) * ( -2 * %s ) + ( %s - %s )\n" %
          (rless0, r, r, absr),
      "( %s ) * ( -2 * %s ) + ( %s - %s )\n" %
          (bless0, b, b, absb),
      "%s < %s - %s\n" % (absr, absb, absrlessabsb)
    ]))

  if (op == "/"):
    computation += generate_computation_line("( ) * ( ) + ( %s - %s )\n"
      % (q, target))
  elif (op == "%"):
    computation += generate_computation_line("( ) * ( ) + ( %s - %s )\n"
      % (r, target))
  else:
    raise Exception("Assertion error - bad division op %s" % (op))

  return computation 

# Honest prover's implementation of less than
def generate_computation_less(arg0, arg1, target):
  (var0, _) = to_var(arg0)
  (var1, _) = to_var(arg1)

  (na1, nb1) = get_bits_signed_difference(arg0, var0, arg1, var1);

  if (nb1 == 0):
    return generate_computation_less_i(na1, arg0, arg1, target)
  else:
    return generate_computation_less_f(na1, nb1, arg0, arg1, target)

def generate_computation_less_i(N, arg0, arg1, target):
  def pv(name):
    var = prover_var(target, name)
    return "V%d" % (var["index"])
  def f(varname):
    (_, renumbered_name) = to_var(varname)
    return renumbered_name

  MltVar = pv("Mlt")
  MeqVar = pv("Meq")
  MgtVar = pv("Mgt")

  N0Var = pv("N0")
  for i in range(1,N-1): #1, ... N-2
    pv("N%d" % (i))

  return "<I N_0 %s N %d Mlt %s Meq %s Mgt %s X1 %s X2 %s Y %s\n" % (
      N0Var, N, MltVar, MeqVar, MgtVar,
      f(arg0), f(arg1), f(target))

def generate_computation_less_f(na2, nb2, arg0, arg1, target):
  def pv(name):
    var = prover_var(target, name)
    return "V%d" % (var["index"])
  def f(varname):
    (_, renumbered_name) = to_var(varname)
    return renumbered_name

  MltVar = pv("Mlt")
  MeqVar = pv("Meq")
  MgtVar = pv("Mgt")
  NumVar = pv("N")
  DenVar = pv("D")
  NDVar = pv("ND")

  N0Var = pv("N0")
  for i in range(1,na2): #1, ... na2 - 1
    pv("N%d" % (i))

  D0Var = pv("D0")
  for i in range(1,nb2+1): #1, ... nb2
    pv("D%d" % (i))

  return "<F N_0 %s Na %d N %s D_0 %s Nb %d D %s ND %s Mlt %s Meq %s Mgt %s X1 %s X2 %s Y %s\n" % (
      N0Var, na2, NumVar, D0Var, nb2,
      DenVar, NDVar, MltVar, MeqVar, MgtVar,
      f(arg0), f(arg1), f(target))

def renumber_vars(terms):
  def f(varname):
    (_, renumbered_name) = to_var(varname)
    return renumbered_name

  toRet = ""
  for term in terms:
    toRet += f(term) + " "
  toRet += "\n"

  return toRet

def generate_computation_exact_divide(target, source, constant):
  def f(varname):
    (_, renumbered_name) = to_var(varname)
    return renumbered_name

  return  "/ %s = %s / %s\n" % (f(target), f(source), constant)

# Honest prover's implementation of a polynomial, passed in as a sequence of tokens
def generate_computation_poly(target, tokens):
  def f(varname):
    (_, renumbered_name) = to_var(varname)
    return renumbered_name

  poly = "P %s = " % (f(target))

  for token in tokens:
    if (token != ""):
      poly += f(token) + " "
  poly += "E\n"
  return poly

#Given a list of tokens that starts with a (, pop(0) tokens from tokens until the matching ) is found. Pop that matching paren.
#All tokens between the parenthesis are returned as a list.
def read_poly(tokens):
  toRet = []
  nesting = 1
  if (tokens.popleft() != "("):
    raise Exception("Format error: " + str(tokens))
  while(nesting > 0):
    token = tokens.popleft()
    if (token == ")"):
      nesting = nesting-1
    elif (token == "("):
      nesting = nesting+1

    toRet += [token]

  toRet.pop() #Dont return the last )
  return toRet

def only_renumber(term):
  ops = ["SIL", "SI", "DB_GET_SIBLING_HASH", "DB_GET_BITS", "DB_PUT_BITS", \
         "GET_BLOCK_BY_HASH", "PUT_BLOCK_BY_HASH", "FREE_BLOCK_BY_HASH", \
         "GENERICGET", "GENERICPUT", "GENERICFREE",
         "ASSERT_ZERO", "PRINTF"]
  return (term in ops)

def generate_computation_line(line):
  #determine what kind of computation is taking place
  terms = collections.deque(line.split())
  if only_renumber(terms[0]):
    toRet = renumber_vars(terms)
    #print(terms,"\n",toRet,"\n")
    return toRet
  elif line.startswith("ASSERT_POLY_ZERO"):
    return "" #Do nothing on asserts
  #elif line.startswith("ASSERT_ZERO") or line.startswith("ASSERT_POLY_ZERO"):
    #return "" #Do nothing on asserts
  elif "!=" in line: #Line has format Var != Var - Var
    return generate_computation_not_equals(terms[0], terms[2], terms[4])
  elif "<" in line: #Line has format Var < Var - Var
    return generate_computation_less(terms[0], terms[2], terms[4])
  elif "%" in line or "/" in line: #Line has format Var %/ Var - Var
    return generate_computation_divide(terms[0], terms[1], terms[2], terms[4])
  else:
    # Depends on whether we have zaatar or ginger constraints
    global framework
    if (framework == "GINGER"):
      (constant, target) = get_poly_output(terms)
      worksheet = ""
      worksheet += generate_computation_poly(target, terms)
      if (constant != "1"):
        worksheet += generate_computation_exact_divide(target, target, constant)
      return worksheet
    if (framework == "ZAATAR"):
      polyA = read_poly(terms)
      star = terms.popleft()
      if (star != "*"):
        raise Exception("Format error")
      polyB = read_poly(terms)
      plus = terms.popleft()
      if (plus != "+"):
        raise Exception("Format error")
      polyC = read_poly(terms)
      (constant, target) = get_poly_output(polyC)

      poly = []
      if ((polyA == [] and polyB != []) or (polyA != [] and polyB == [])):
        raise Exception("Format error - nonempty A but empty B %s )" % line)
      if (polyA != []):
        poly += ["("] + polyA + [")","*","("] + polyB + [")"]
      if (polyC != []):
        if (polyA != []):
          poly += ["+"]
        poly += polyC

      worksheet = ""
      worksheet += generate_computation_poly(target, poly)
      if (constant != "1"):
        worksheet += generate_computation_exact_divide(target, target, constant)
      return worksheet

# For a polynomial constraint such as x1 * x2 - 4 * x3, returns ("4", x3)
# For a polynomial constraint x1 * x2 - x3, returns ("1", x3)
def get_poly_output(tokens):
  target = tokens.pop()
  constant = "1"
  if (tokens[-1] == "*"):
    tokens.pop()
    constant = tokens.pop()
  if (tokens[-1] != "-"):
    raise Exception("Polynomial expression didn't end with - (some variable), to provide an output variable")
  tokens.pop() # -
  return (constant, target)

def generate_computation_lines(text):
  lines = text.splitlines()
 
  worksheet = ""

  for line in lines:
    line = line.strip()
    if line != "":
      computationForLine = generate_computation_line(line)
      worksheet += computationForLine 
 
  return worksheet

def generate_computation_worksheet(spec_file, pws_loc):
  with open(pws_loc, "w") as pws_file:
    def f(line):
      line = line.strip()
      if line.startswith("EXTERN"):
        terms = line.split()
        cons_entry = merkle_gen.get_cons_entry(terms[1])
        subst_entry = merkle_gen.get_subst_entry(terms[2])
        with open(cons_entry.tmpls["pws"], "r") as src_tmpl:  
          template_subst(pws_file, src_tmpl, subst_entry)
      elif line != "":
        computationForLine = generate_computation_line(line)
        pws_file.write(computationForLine)

    process_spec_section(spec_file, START_TAG + CONSTRAINTS_TAG, END_TAG + CONSTRAINTS_TAG, f)

  global input_vars
  global output_vars
  global variables
  return (input_vars.num_vars + output_vars.num_vars, variables.num_vars)

def generate_load_qap(qap_file):
  code = """load_qap("%s");""" % (qap_file)
  return code

def generate_computation_dynamic(worksheet_file):
  code = """compute_from_pws("%s");""" % (worksheet_file)
  return code

##########################
## Generate computation static (i.e. no pws file)
##########################

def generate_computation_static(spec_file):
  global m
  global chi
  global variables

  zcc_parser_static.m = m
  zcc_parser_static.chi = chi
  zcc_parser_static.variables = variables.named_vars
  zcc_parser_static.input_vars = input_vars.named_vars
  zcc_parser_static.output_vars = output_vars.named_vars

  code = zcc_parser_static.generate_computation(spec_file)

  m = zcc_parser_static.m
  chi = zcc_parser_static.chi
  variables.named_vars = zcc_parser_static.variables
  variables.num_vars = len(zcc_parser_static.variables)

  return code

##########################
## Other functions
##########################

def generate_F1_index():
  shuffled_indices = range(0, variables.num_vars)
  random.shuffle(shuffled_indices)

  code = ""
  for i in range(0, variables.num_vars):
    code += "%d " % (shuffled_indices[i])
  return (code, shuffled_indices)

def generate_constants(consts_path):
  with open(consts_path, "r") as f:
    code = ""
    for line in f:
      line = line.strip()
      if (line != ""):
        code += """const %s;\n""" % (line)

  return code

def generate_mapred_header(class_name):
  code = ""
  is_mapred_comp = "0"
  is_mapper = "0"
  is_reducer = "0"
  if (class_name.startswith("mr_")):
    is_mapred_comp = "1"
    if (class_name.endswith("_map")):
      is_mapper = "1"
    else:
      is_reducer = "1"

    code = """
#define IS_MAPRED_COMP %s
#define IS_MAPPER %s
#define IS_REDUCER %s
""" % (is_mapred_comp, is_mapper, is_reducer)
  return code

##########################
## Generate input
##########################

def generate_create_input():
  code = """
  //gmp_printf("Creating inputs\\n");
  """

  for k in sorted(input_vars.named_vars.keys()):
    ivar = input_vars.named_vars[k];
    i = ivar["index"]
    if (ivar["type"] == "int"):
      code += """
    v->get_random_signedint_vec(1, input_q + %d, %d);
    """ % (i, ivar["na"])

    elif (ivar["type"] == "uint"):
      code += """
    v->get_random_vec_priv(1, input_q + %d, %d);
    """ % (i, ivar["na"])

    elif (ivar["type"] == "float"):
      code += """
    v->get_random_rational_vec(1, input_q + %d, %d, %d);
    """ % (i, ivar["na"], ivar["nb"])

    else:
      raise Exception("Untyped input variable %s" % (ivar["name"]))

  return code
