#!/usr/bin/env python3

from symbolic import box, Result
from tinyscript_util import (
	check_sat,
	fmla_enc,
	state_from_z3_model,
	stringify,
	vars_formula,
	vars_prog,
	vars_term,
)
from functools import reduce
from interpreter import exc
import tinyscript as tn
import z3

INV_VAR = '#inv_true'

def checktaint(term: tn.Term) -> tn.Formula:
	"""
	A helper function in the instrumentation of taint. This will help build the
	conditional to check whether a term is tainted or not.

	Args:
		term(tn.Term): a tinyscript term to be inspected for whether it
		contains tainted variables.

	Returns:
		tn.Formula: a tinyscript formula representing the idea: "At lease one of the
		tinyscript variables in this term is tainted."
	
	"""
	vars = vars_term(term)
	form = tn.FalseC()
	for var in vars:
		name = var.name
		form = tn.OrF(form, tn.EqF(tn.Var(name+'_taint'), tn.Const(1)))
	return form

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
			tainted = checktaint(aexp)
			marktainted = tn.If(tainted, tn.Asgn(name+'_taint', tn.Const(1)), tn.Asgn(name+'_taint', tn.Const(0)))

			return tn.Seq(alpha, marktainted)
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

			return tn.If(p, ins_alpha, ins_beta)
        # same with while loops
		case tn.While(q, alpha_p):
			ins_alpha = instrument_help(alpha_p)
			return tn.While(q, ins_alpha)
		case tn.Skip():
			return alpha
		case tn.Output(a):
			tainted = checktaint(a)
			checktainted = tn.If(tainted, tn.Asgn(INV_VAR, tn.Const(0)), tn.Skip())
			return tn.Seq(checktainted, alpha)
		case tn.Abort():
			return alpha
		case _:
			raise TypeError(
                f"instrument got {type(alpha)} ({alpha}), not Prog"
            )

def instrument(alpha: tn.Prog, source_prefix: str='sec_') -> tn.Prog:
	"""
	Instruments a program to support symbolic checking 
	for violations of a taint policy that considers any variable 
	prefixed with `secret_prefix` to be a source, and the argument 
	to any `output` statement to be a sink.
	
	Args:
	    alpha (tn.Prog): A tinyscript program to instrument
	    source_prefix (str, optional): The string prefix for
	    	source variables
	
	Returns:
	    tn.Prog: The instrumented program. It should be possible
	    	to use the box modality and a satisfiability solver
	    	to determine whether a trace in the original program
	    	`alpha` exists that violates the taint policy.
	"""
	vars = vars_prog(alpha)
	init = tn.Asgn(INV_VAR, tn.Const(1))
	for var in vars:
		name = var.name
		if(name.startswith(source_prefix)):
			init = tn.Seq(init, tn.Asgn(name+'_taint', tn.Const(1)))
		else:
			init = tn.Seq(init, tn.Asgn(name+'_taint', tn.Const(0)))
	instr = instrument_help(alpha)
	#print(stringify(instr))
	return tn.Seq(init, instr)


def symbolic_check(
	alpha: tn.Prog, 
	source_prefix: str='sec_', 
	max_depth: int=1,
	timeout: int=10) -> Result:
	"""
	Uses the box modality and a satisfiability solver to determine
	whether there are any traces that violate a taint policy that 
	considers any variable prefixed with `secret_prefix` to be a 
	source, and the argument to any `output` statement to be a sink.
	This function only considers traces generated after unrolling 
	loops up to `max_depth` times, and will terminate the solver 
	after `timeout` seconds.
	
	Args:
	    alpha (tn.Prog): Program to check
	    source_prefix (str, optional): String prefix for source
	    	variables
	    max_depth (int, optional): Loop unrolling depth
	    timeout (int, optional): Solver timeout, in seconds
	
	Returns:
	    Result: The status of the check, one of three values:
	    	- Result.Satisfies: All traces up to the unrolling depth
	    	  satisfy the taint policy. This result *does not* signify 
	    	  anything about traces that exceed the unrolling depth.
	    	- Result.Violates: There exists a trace within the unrolling
	    	  depth that violates the taint policy.
	    	- Result.Unknown: The result is indeterminate (e.g. the
	    	  solver timed out, returning z3.unknown).
	"""
	alpha_p = instrument(alpha, source_prefix)
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