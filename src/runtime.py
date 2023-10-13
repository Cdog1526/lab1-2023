#!/usr/bin/env python3
from typing import Optional
from symbolic import box, Result
from tinyscript_util import (
	check_sat,
	stringify,
	fmla_enc,
	state_from_z3_model,
	term_stringify
)
import tinyscript as tn
import z3
from interpreter import exc

INV_VAR = '#inv_true'
COUNTER = '#counter'
BOUND = '#bound'

def check(alpha: tn.Prog) -> tn.Prog:
	"""
	A helper function in the instrumentation of runtime. All it does is instrument a single
	line the exact same way every time:
	alpha -> (if counter = bound, invariant flag = 0);alpha;(counter++)

	Args:
		alpha(tn.Prog): a (time-using) tinyscript program line that needs to be instrumented

	Returns:
		tn.Prog: a tinyscript program instrumented as described before, so that for each
		time using step, it is checked whether the counter variable has reached the bound;
		if not, the counter is incremented	
	
	"""
	fail = tn.EqF(tn.Var(BOUND), tn.Var(COUNTER))
	check = tn.If(fail, tn.Asgn(INV_VAR, tn.Const(0)), tn.Skip())
	inc = tn.Asgn(COUNTER, tn.Sum(tn.Const(1), tn.Var(COUNTER)))

	return tn.Seq(tn.Seq(check, alpha), inc)

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
			return check(alpha)
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
			return check(alpha)
		case tn.Output(a):
			return check(alpha)
		case tn.Abort():
			return check(alpha)
		case _:
			raise TypeError(
                f"instrument got {type(alpha)} ({alpha}), not Prog"
            )
	return

def instrument(alpha: tn.Prog, step_bound: Optional[int]=None) -> tn.Prog:

	"""
	Instruments a program to support symbolic checking 
	for violations of the maximum execution length policy.
	
	Args:
	    alpha (tn.Prog): A tinyscript program to instrument
	    step_bound (int, optional): A bound on runtime steps
	
	Returns:
	    tn.Prog: The instrumented program. It should be possible
	    	to use the box modality and a satisfiability solver
	    	to determine whether a trace in the original program
	    	`alpha` exists that executes for longer than the bound
	    	on steps. A step occurs when the program executes an
	    	assignment, output, abort, or skip statement.
	"""
	if(step_bound == None):
		return alpha
	initialize = tn.Seq(tn.Seq(tn.Asgn(INV_VAR, tn.Const(1)), tn.Asgn(COUNTER, tn.Const(0))),
		tn.Asgn(BOUND, tn.Const(step_bound)))
	instr = instrument_help(alpha)
	#print(stringify(instr))
	return tn.Seq(initialize, instr)
	

def symbolic_check(
	alpha: tn.Prog, 
	step_bound: int,
	max_depth: int=1,
	timeout: int=10) -> Result:
	"""
	Uses the box modality and a satisfiability solver to determine
	whether there are any traces that execute more than `step_bound`
	steps. A step occurs when the program executes an assignment, 
	output, abort, or skip statement. This function only considers 
	traces generated after unrolling loops up to `max_depth` times, 
	and will terminate the solver after `timeout` seconds.
	
	Args:
	    alpha (tn.Prog): Program to check
	    step_bound (int): Step bound to check
	    max_depth (int, optional): Loop unrolling depth
	    timeout (int, optional): Solver timeout, in seconds
	
	Returns:
	    Result: The status of the check, one of three values:
	    	- Result.Satisfies: All traces, up to the given unrolling 
	    	  depth, terminate within `step_bound` steps. 
	    	- Result.Violates: There exists a trace that violates the
	    	  step bound. This result *includes* traces that do not 
	    	  terminate within the unrolling depth, e.g., 
	    	  the program "while(true) skip" should yield this result
	    	  with an unrolling depth of 1 if the solver is able to 
	    	  provide a state that causes the interpreter to execute
	    	  at least `step_bound` steps.
	    	- Result.Unknown: The result is indeterminate. This could
	    	  mean that the solver timed out, returning z3.unknown. It
	    	  could also signify that there is a trace that fails to
	    	  terminate within the unrolling bound, but the solver did
	    	  not return a state that caused the interpreter to execute
	    	  at least `step_bound` steps.
	"""
	alpha_p = instrument(alpha, step_bound)
	post = tn.EqF(tn.Var(INV_VAR), tn.Const(1))
	#print(stringify(alpha_p))
	weakest_pre = box(alpha_p, fmla_enc(post), max_depth, True)
	#print(weakest_pre)
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

	cap = 20

	for test_file in list(TEST_DIR.iterdir()):
		#if(cap < 0):
		#	break
		#cap -= 1
		if not str(test_file).endswith('tinyscript'):
			continue
		with test_file.open() as f:
			prog = parse(f.read())
			res = symbolic_check(prog, 100)
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
