#!/usr/bin/env python3

from symbolic import box, Result
from tinyscript_util import (
	check_sat,
	stringify,
	vars_prog,
	vars_formula,
	vars_term,
	fmla_enc,
	state_from_z3_model,
)
import tinyscript as tn
import z3
from interpreter import exc


INV_VAR = '#inv_true'

def instr_termcheck(terms: list[tn.Var]) -> tn.Prog:
	"""
	A helper function in the instrumentation of defuse. All it does is instrument
	the tinyscript program alpha to become (for variable in alpha, if variable is not
	defined yet, set the invariant flag to zero); alpha. Ensures that no variable is
	accessed before use.

	Args:
		terms(list[tn.Var]): a list of tinyscript variables to be checked for whether
		they have been defined yet.

	Returns:
		tn.Prog: a tinyscript program instrumented as described before, so that it
		checks whether all of those tinyscript variables have been defined.	
	
	"""
	base = tn.Skip()
	for var in terms:
		name = var.name
		check = tn.If(tn.EqF(tn.Var(name+'_def'), tn.Const(0)), tn.Asgn(INV_VAR, tn.Const(0)), tn.Skip())
		base = tn.Seq(base, check)
	return base

#def checkterm(term : tn.Term) -> list[tn.Var]: 
	#return vars_term(term)
	"""match term:
		case tn.Const(a):
			return []
		case tn.Var(name):
			return [name]
		case tn.Difference(t1, t2):
			return checkterm(t1) + checkterm(t2)
		case tn.Sum(t1, t2):
			return checkterm(t1) + checkterm(t2)
		case tn.Product(t1, t2):
			return checkterm(t1) + checkterm(t2)
		case _:
			raise TypeError(
                f"checkterm got {type(term)} ({term}), not Term"
            )
	"""
	#return: list of terms


#def checkformula(form : tn.Formula) -> list[tn.Var]:
	##return vars_formula(form)
	"""match form:
		case tn.FalseC():
			return []
		case tn.TrueC():
			return []
		case tn.NotF(f):
			return checkformula(f)
		case tn.AndF(f1, f2):
			return checkformula(f1) + checkformula(f2)
		case tn.OrF(f1, f2):
			return checkformula(f1) + checkformula(f2)
		case tn.ImpliesF(f1, f2):
			return checkformula(f1) + checkformula(f2)
		case tn.EqF(t1, t2):
			return checkterm(t1) + checkterm(t2)
		case tn.LtF(t1, t2):
			return checkterm(t1) + checkterm(t2)
		case _:
			raise TypeError(
                f"checkformula got {type(form)} ({form}), not Formula"
            )	"""
			
	#return: list of terms

def instrument_help(alpha: tn.Prog) -> tn.Prog:
	"""
	Recursive helper function for instrumentation; handles all of the main logic. 

	Args:
		alpha (tn.Prog): program subset to be instrumented.
	
	Returns:
		tn.Prog: an instrumented version of alpha, to be returned and used in an outer
		recursive call or by instrument.
	
	"""
	match alpha:
        # assignments can violate the invariant, so instrument them directly
		case tn.Asgn(name, aexp):
			used = vars_term(aexp)
			checkused = instr_termcheck(used)
			markdef = tn.Asgn(name+'_def', tn.Const(1))
			return tn.Seq(tn.Seq(checkused, alpha), markdef)
        # composition cannot violate the invariant unless through either
        # of its constituents, so recurse and do not add instrumentation directly
		case tn.Seq(alpha_p, beta_p):
			ins_alpha = instrument_help(alpha_p)
			ins_beta = instrument_help(beta_p)
			return tn.Seq(ins_alpha, ins_beta)
        # same with conditionals
		case tn.If(p, alpha_p, beta_p):
			ins_alpha = instrument_help(alpha_p)
			ins_beta = instrument_help(beta_p)
			used = vars_formula(p)
			checkused = instr_termcheck(used)
			return tn.Seq(checkused, tn.If(p, ins_alpha, ins_beta))
        # same with while loops
		case tn.While(q, alpha_p):
			used = vars_formula(q)
			checkused = instr_termcheck(used)
			ins_alpha = instrument_help(alpha_p)
			return tn.Seq(checkused, tn.While(q, ins_alpha))
		case tn.Skip():
			return alpha
		case tn.Output(a):
			used = vars_term(a)
			checkused = instr_termcheck(used)
			return tn.Seq(checkused, alpha)
		case tn.Abort():
			return alpha
		case _:
			raise TypeError(
                f"instrument got {type(alpha)} ({alpha}), not Prog"
            )
	return

def instrument(alpha: tn.Prog) -> tn.Prog:
	"""
	Instruments a program to support symbolic checking 
	for violations of the define-before-use policy.
	
	Args:
	    alpha (tn.Prog): A tinyscript program to instrument
	
	Returns:
	    tn.Prog: The instrumented program. It should be possible
	    	to use the box modality and a satisfiability solver
	    	to determine whether a trace in the original program
	    	`alpha` exists that uses an undefined variable.
	""" 
	vars = vars_prog(alpha)
	init = tn.Asgn(INV_VAR, tn.Const(1))
	for var in vars:
		name = var.name
		init = tn.Seq(init, tn.Asgn(name+'_def', tn.Const(0)))
	#what uses variables?
	#Output: a is a term
	#Check ifs, 
	instr = instrument_help(alpha)
	#print(stringify(instr))
	return tn.Seq(init, instr)

def symbolic_check(
	alpha: tn.Prog, 
	max_depth: int=1,
	timeout: int=10
) -> Result:
	"""
	Uses the box modality and a satisfiability solver to determine
	whether there are any traces that attempt to use an undefined
	variable. This function only considers traces generated after
	unrolling loops up to `max_depth` times, and will terminate
	the solver after `timeout` seconds.
	
	Args:
	    alpha (tn.Prog): Program to check
	    max_depth (int, optional): Loop unrolling depth
	    timeout (int, optional): In seconds; if `None`, then the
	    	solver cannot timeout
	
	Returns:
	    Result: The status of the check, one of three values:
	    	- Result.Satisfies: All traces, up to the given unrolling 
	    	  depth, only attempt to use variables that were previously
	    	  defined. This result *does not* signify anything about
	    	  traces that exceed the unrolling depth.
	    	- Result.Violates: There exists a trace within the unrolling
	    	  depth that attempts to use an undefined variable.
	    	- Result.Unknown: The result is indeterminate (e.g. the
	    	  solver timed out, returning z3.unknown).

	"""
	alpha_p = instrument(alpha)
	post = tn.EqF(tn.Var(INV_VAR), tn.Const(1))
	weakest_pre = box(alpha_p, fmla_enc(post), max_depth, False)
	res, model = check_sat([z3.Not(weakest_pre)], timeout=timeout)
	if res == z3.unsat:
		return Result.Satisfies
	elif res == z3.sat:
		state = state_from_z3_model(alpha, model, complete=True)
		final_state = exc(state, alpha_p, max_steps=1.e6, quiet=True)
		if final_state[0].variables[INV_VAR] == 0:
			return Result.Violates
	return Result.Unknown

if __name__ == "__main__":
	from parser import parse, fmla_parse
	import sys
	from pathlib import Path

	TEST_DIR = Path('.') / 'tests'

	if not TEST_DIR.is_dir():
		raise ValueError(f"Expected {TEST_DIR} to be a directory")

	passed = 0
	violate = 0
	unknown = 0

	for test_file in list(TEST_DIR.iterdir()):
		if not str(test_file).endswith('tinyscript'):
			continue
		with test_file.open() as f:
			prog = parse(f.read())
			res = symbolic_check(prog)
			print((
				f"{test_file} result:" 
				f"{res}"))
			match res:
				case Result.Satisfies:
					passed += 1
				case Result.Violates:
					violate += 1
				case Result.Unknown:
					unknown += 1

	print(f"\n{passed=}, {violate=}, {unknown=}")
