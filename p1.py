"""
Jibreel Campbell
Abdullah Alsayyar
Andres Delgado

Project 1: DP-based SAT solver

9/20/18
"""

def proveFormula(F):
	###########################################################
	# note: All these if statements are just used for testing #
	###########################################################

	#print("Given:     ", F)

	#Stores a binary tree list of the given input F
	formulaList = MakeList(F)
	if formulaList:
		if type(formulaList) is str:
			return 'S'
	else: return

	# Extracts all variables from formula into variableList
	variableList = FindVariables(formulaList)

	# Converting to CNF: Theroem 4.3, Step 1
	cnfList = EliminateOps(formulaList)
	if cnfList:
		if type(cnfList) is str:
			return 'S'
	else: return

	# Steps 2/3 combined
	cnfList = DeMorgans(cnfList)
	if cnfList:
		if type(cnfList) is str:
			return 'S'
	else: return

	#cnfList = doDistributive(cnfList)
	cnfList = Distribute(cnfList)

	cnfList = ClasualForm(cnfList)
	#print(cnfList)

	return checkSatisfyability(cnfList, variableList)


def checkSatisfyability(formula, variables):
	# Will stop branch if it was called during last variable
	if not variables:
		return 'U'

	# Here I run the dp algorithm, going through the variables and applying the individual rules.
	for x in variables:
		pureVar = True
		varPure = 0
		newFormula = formula[:]
		unitPropag = False
		unitPropForm = 0
		branch = True

		for y in formula:
			if y == [x]:
				if unitPropForm == -1:
					return 'U'
				unitPropag = True
				unitPropForm = 1
			# Checking for unit-prop for negated literal
			elif y == [[x]]:
				if unitPropForm == 1:
					return 'U'
				unitPropag = True
				unitPropForm = -1
			# elim clause, case: (p v -p v ...) -> can assign pure lit for both forms,
			# because clause with any form of p can be satisfied, go to next iter
			if x in y and [x] in y:
				newFormula.remove(y)
				varPure = 2
				continue
			if x in y and varPure == 0:
				varPure = 1
			elif [x] in y and varPure == 0:
				varPure = -1

			if varPure == -1 and x in y:
				pureVar = False
			elif varPure == 1 and [x] in y:
				pureVar = False
		formula = newFormula[:]

		# Check form of single literal, unit-prop can be applied to both forms
		if unitPropag:
			branch = False
			for y in formula:
				# if unit-prop literal is positive
				if unitPropForm == 1:
					if x in y:
						newFormula.remove(y)
					elif [x] in y:
						newFormula[newFormula.index(y)].remove([x])
				# if unit-prop literal is negative
				elif unitPropForm == -1:
					if [x] in y:
						newFormula.remove(y)
					elif x in y:
						newFormula[newFormula.index(y)].remove(x)
		formula = newFormula[:]

		# Pure literal rule for both forms. Case: (p v -p v ...)
		if varPure == 2:
			branch = False
			for y in formula:
				if x in y or [x] in y:
					newFormula.remove(y)
		# pureVar will still be True when current variable has been deleted from all clauses
		# elif varPure == 0 and pureVar:
		# 	pureVar = False
		elif pureVar and varPure != 0:
			branch = False
			for y in formula:
				if varPure == 1:
					if x in y:
						newFormula.remove(y)
				elif varPure == -1:
					if [x] in y:
						newFormula.remove(y)

		formula = newFormula[:]

		# If first 2 rules dont apply and if current variable x is in formula
		# Assign boolean value to x so that it satisfies its current clause (Unit-Prop)
		# Branch formula with assumed variable. Returns 'S' if branch is satisfied, continue to resolution otherwise.
		if branch:
			branchFormula = formula[:] # a compy of the formula
			xIndex = [1 if x in y else -1 if [x] in y else 0 for y in formula] # look for all occurences x and ~x in each clause
			# Found positive form of x in the formula
			# after making a guess it will do unit propogation with the variable in that form
			# after removing the appropriate statements, we call checkSatisfyability on branched output
			if 1 in xIndex:
				for y in formula:
					if x in y:
						branchFormula.remove(y)
					elif [x] in y:
						branchFormula[branchFormula.index(y)].remove([x])
			# Found negative form of x in the formula
			elif -1 in xIndex:
				for y in formula:
					if [x] in y:
						branchFormula.remove(y)
					elif x in y:
						branchFormula[branchFormula.index(y)].remove(x)
			if branchFormula != formula:
				checkBranch = checkSatisfyability(branchFormula, variables[variables.index(x) + 1:])
				if checkBranch == 'S':
					return 'S'

		if newFormula == []:
			return 'S'
		elif [] in newFormula:
			return 'U'
		else:
			print("do resolution")
			newFormula = doResolution(newFormula, x)
	return 'U'

def doDistributive(formula):
	#check if the formula is in cnf form
	cnf = True
	for x in formula:
		if type(x) is list and x[0] == 'AND':
			andIn = formula.index(x)
			if formula[0] == 'OR':
				cnf = False

			break

	# if it is not CNF you are going to have to use the distributive property to
	# convert the formula to cnv
	# Here I make the and value the first value and then it distrubutes the and variables with the rest of the or's
	if not cnf:
		newFormula = []
		alors = []

		for i ,x in enumerate(formula):
			if i != 0 and i != andIn and x[0] == 'OR':
				alors.append(x[1:])

		newFormula.append('AND')

		for x in formula[andIn][1:]:
			newFormula.append(['OR', x])
			for y in alors:
				newFormula[-1].extend(y)

		formula = newFormula

	# Here I transform the resultant formula into the clausal form that is require for dp
	# so if there is just an or it will double bracket the whole expression.
	# if it starts with an and it will remove the OR's and NOT's from the sub arrays by looping
	# through the list.
	cnfForm = []
	if formula[0] == 'OR':
		orForm = []
		for x in formula[1:]:
			if type(x) is list:
				orForm.append(x[1:])
			else:
				orForm.append(x)
		cnfForm.append(orForm)
		return cnfForm

	for x in formula[1:]:
		if type(x) is list:
			if x[0] == 'OR':
				orForm = []
				for y in x[1:]:
					if type(y) is list:
						orForm.append(y[1:])
					else:
						orForm.append(y)
				cnfForm.append(orForm)
			else:
				cnfForm.append([x[1:]])
		else:
			cnfForm.append([x])


	return cnfForm

def doResolution(currentFormula, currentVar):
	# Here I check if any resolvents can be made.
	# I check if there is [[p, a, b], [[p], c, d]] and it turns into [[a, b, c, d]] and I can eliminate clauses containing p or ~p
	# I also make sure that things like [[a, a], [[a], [a]]] can't be used for resolvents
	resolvent = False

	for y in currentFormula:
		if currentVar in y:
			for z in formula:
				if z != y and [currentVar] in z and list(filter(lambda a: a != currentVar, y)) != [] and list(filter(lambda a: a != [currentVar], z)) != []:
					temp1 = list(filter(lambda a: a != currentVar, y))
					temp2 = list(filter(lambda a: a != [currentVar], z))
					temp1.extend(temp2)
					currentFormula.append(temp1)
					resolvent = True

	if resolvent:
		for y in formula:
			if currentVar in y:
				currentFormula.remove(y)
			if [currentVar] in y:
				currentFormula.remove(y)

	return currentFormula



def ClasualForm(formula):

	if formula[0] == "NOT":
		return formula[1:]
	else: stack = []

	for arg in range(len(formula)):
		if type(formula[arg]) is list:
			if (formula[0] == "AND") and (formula[arg][0] == "NOT"):
				formula[arg] = [formula[arg][1:]]
			else:
				formula[arg] = ClasualForm(formula[arg])
		elif (arg > 0) and (formula[0] == "AND"):
			formula[arg] = [formula[arg]]

		if (arg > 0) and (formula[arg] not in stack):
			stack.append(formula[arg])

	if stack and (stack != formula[1:]):
		formula[1:] = stack

	if (formula[0] == "AND") or (formula[0] == "OR"):
		return formula[1:]
	return formula

def EliminateOps(formula):
	"""Step 1 of Theorem 4.3: Recursively eliminates IFs."""

	# cnf stores the altered formula
	operations = ["AND", "OR", "IF", "NOT"]
	cnf = []

	# Checks if index 0 is an operation
	if formula[0] in operations:
		opIndex = operations.index(formula[0])
	else: return formula

	# Initializes list of booleans to help check if expressions are lists
	nestedArgs = [False] * (len(formula)-1)
	i = 0
	for arg in formula[1:]:
		if type(arg) is list:
			nestedArgs[i] = True
		i += 1

	# IF operation: [IF A B] -> [OR [NOT A] B]
	if (opIndex == 2) and (len(formula) == 3):
		cnf.append('OR')
		if nestedArgs[0] and nestedArgs[1]:
			cnf.append(['NOT', EliminateOps(formula[1])])
			cnf.append(EliminateOps(formula[2]))
			return cnf
		elif nestedArgs[0]:
			cnf.append(['NOT', EliminateOps(formula[1])])
			cnf.append(formula[2])
			return cnf
		elif nestedArgs[1]:
			cnf.append(['NOT', formula[1]])
			cnf.append(EliminateOps(formula[2]))
			return cnf
		else:
			cnf.append(['NOT', formula[1]])
			cnf.append(formula[2])
			return cnf

	# Checks the formula for nested arguments and searches inside them
	# Appends each argument to cnf
	cnf.append(formula[0])
	for arg in range(1, len(formula)):
		if type(formula[arg]) is list:
			cnf.append(EliminateOps(formula[arg]))
		else:
			cnf.append(formula[arg])
	return cnf

def DeMorgans(formula, negation = False):
	"""Steps 2 and 3 from Theorem 4.3:
	Recursively applies De Morgan's laws and eliminates double negations.
	negation == True when there was a negation outside the current argument.
	"""

	# When operator is NOT:
	# Checks for double negations and nested arguments
	if formula[0] == "NOT":
		if type(formula[1]) is list:
			# Case where there is a double negation outside a nested argument:
			# Ignores both negations, returns the result of searching the argument
			if negation:
				return DeMorgans(formula[1])
			# Applies De Morgan's laws to the nested argument
			return DeMorgans(formula[1], True)

		# Case where there is a double negation on a single variable
		elif negation:
			return formula[1]
		return formula

	# Operator is AND/OR if this line is reached
	# Flips AND/OR if applying De Morgan's
	if negation:
		if formula[0] == "AND":
			formula[0] = "OR"
		else: formula[0] = "AND"

	# Iterates through all arguments of the formula
	# Applies De Morgan's to nested argument or variable if negation == true
	for arg in range(1, len(formula)):
		if type(formula[arg]) is list:
			# Applies De Morgan's to nested argument
			if negation:
				formula[arg] = DeMorgans(formula[arg], True)
			else: formula[arg] = DeMorgans(formula[arg])
		# Negates the single variable
		elif negation:
			formula[arg] = ['NOT', formula[arg]]
	return formula

def Distribute(formula, inside = False):
	"""Step 4 of Theorem 4.3: Uses distributive laws to elimiate conjunctions within disjunctions.
	inside is used to check if the original, or modified original formula, is just 1 OR argument.
	Returns a CNF formula in S-Expression"""

	operations = ["AND", "OR"]

	# Checks if index 0 is AND/OR
	# else, Formula is a single variable
	if formula[0] in operations:
		opIndex = operations.index(formula[0])
	else:
		return [[formula]]

	# Post-Order traversal to the innermost nested argument
	for arg in range(1, len(formula)):
		if (type(formula[arg]) is list) and (formula[arg][0] != "NOT"):
			formula[arg] = Distribute(formula[arg], True)

	# Iterates through formula and checks if nested arguments are AND/OR lists
	# Applies appropriate distribution if needed
	for arg in range(1, len(formula)):

		# Re-assign opIndex if original formula has been changed
		if formula[0] != operations[opIndex]:
			opIndex = operations.index(formula[0])

		# Current formula is AND/OR
		if (type(formula[arg]) is list) and (formula[arg][0] != "NOT"):

			# Current formula is OR and arguemnt is AND: applies distributive law
			# Case: formula is (A v (B ^ C)) or ((A ^ B) v C)
			if (opIndex == 1) and (formula[arg][0] == "AND"):
				aFormula = formula.pop(arg)

				newFormula = ['AND',]
				for x in aFormula[1:]:
					stack = ['OR', x]
					for y in formula[1:]:
						stack.append(y)
					newFormula.append(stack)

				# recursive call is needed because the indices could have been changed
				return Distribute(newFormula)

			# Current formula is the same operation as inside argument
			# Case is some variation of: ((A v B) v C) or (A ^ (B ^ C))
			elif opIndex == (operations.index(formula[arg][0])):
				newFormula = formula.pop(arg)
				formula = formula + [x for x in newFormula[1:]]

				# recursive call is needed because the indices could have been changed
				return Distribute(formula, inside)

	# Case where formula is just one argument of disjunctions or a single variable:
	# (p v q v r)  -->  ((p v q v r)) so program can read it as CNF
	if ((not inside) and (formula[0] == "OR")):
		return [formula]
	return formula

def MakeList(F):
	"""Takes original F input and returns a binary tree list, or a string if it's a single variable.
	If F has more than 1 expression,
		Index 0 is the operator and index 1/2 are expressions (another binary tree list or variable).
	else, returns the variable string.
	"""

	# Checks if F is just a single variable
	if (len(F) > 0) and (F[0] != '('):
		return F

	invalidChars = ('\t', ' ', '\n')
	formula = [[]]
	expression = ""

	# iterates through each char in F and stores the resulting list in formula
	for char in range(len(F)):
		if F[char] == '(':
			formula.append([])

		# Example of elif:	[[], ['NOT'], ['NOT', 'not']]
		# 			   to:	[[], ['NOT', ['NOT', 'not']]]
		elif F[char] == ')':
			# Checks if current ')' is following non ')' chars
			if expression != "":
				formula[-1].append(expression)
				expression = ""
			inExp = formula[-1]
			del formula[-1]
			formula[-1].append(inExp)

		# Stores char if it's not an S-Expression specific char
		elif F[char] not in invalidChars:
			expression += F[char]

		# Appends the stored chars to the list
		elif expression != "":
			formula[-1].append(expression)
			expression = ""

	# Being careful...
	if len(formula):
		if len(formula[0]):
			if len(formula[0][0]):
				return formula[0][0]
			else:
				return formula[0]
		else:
			return formula
	return

def FindVariables(formula, variables = None):
	"""Recursively searches and returns a list of all unique variables in the formula."""

	normalOps = ['AND', 'OR', 'IF']
	if variables is None:
		variables = []

	# The following ifs check index 0 of formula for operators or a variable
	# Then recursively searches inside the arguments if it's a list
	# Checks for 2-ary operators
	if formula[0] in normalOps:
		for i in range(1, len(formula)):
			if type(formula[i]) is list:
				variables = FindVariables(formula[i], variables)
			elif formula[i] not in variables:
				variables.append(formula[i])

	# Checks for 1-ary operator (NOT)
	elif formula[0] == "NOT":
		if type(formula[1]) is list:
			variables = FindVariables(formula[1], variables)
		elif formula[1] not in variables:
			variables.append(formula[1])

	# formula is a single variable
	elif formula[0] not in variables:
		variables.append(formula[0])
	return variables

# def resolution(clausalFormFormula, vars):
# 	"""
# 	performs the resolution rule on a bool formula in clausal form:
#
# 	Given some CNF formula F
# 	For some variable p:
# 		For every clause C1 containing p:
# 			For every clause C2 containing ¬p:
# 				Create the resolvent CR from C1 and C2, add it to assignments
# 				nOTE: even if CR is empty, it must be kept!
# 	Remove all clauses containing p or ¬p from F
#
# 	clausalForm = a list of clauses representing a cnf formula
# 	[ [p, q], [[p]], [p, [q], r, s, t, u, v] ]
# 	if only considering the 'q's,the function will return this:
# 	[ [[p]], [p, p, r, s, t, u, v] ]
# 	the second term is the resolvent of the 1st and 3rd terms of the previous
#
# 	vars = a list containing all the variables found in the statement
# 	[p, q, r, s, t, u, v]
#
#
# 	a list within an inner list if considered a negative variable
# 	"""
#
# 	 # Will store all of the statements after resolution operation has finished
# 	expressionWithResolution = [];
#
# 	for var in vars: # apply resolution to each variable
# 		clausesWithVar = findClausesWithVariable(clausalFormFormula, var) # a list containing the clauses that use the var
# 		clausesWithNegVar = findClausesWithVariable(clausalFormFormula, [var])
#
# 		#print('\nvar:', var, '\nclauses:\n', clausesWithVariable)
# 		print('\nvar:', var, '\nclauses:\n', clausesWithVar)
# 		print('\nvar:', var, '\nneg clauses:\n', clausesWithNegVar)
#
#
# 	return expressionWithResolution;

def findClausesWithVariable(clausalFormFormula, variable):
	"""
	takes a clausal form boolean formula and returns a list storing the clauses
	that contain the variable

	to find the negative version of the variable, pass in a list containing only
	the variable
	"""
	clausesWithVar = []


	for clause in clausalFormFormula:
		if variable in clause: # variabies
			clausesWithVar.append(clause)

	return clausesWithVar

# if __name__ == "__main__":

	# problems = [#'p', '(NOT p)',
	# '(NOT (NOT (NOT (NOT not))  )		)',	### 2nd from grader
	# '(IF p p)',
	# '(AND p (NOT p) q (NOT t) gf)',         # cnf0
	# '(OR five (OR three four))',
	# '(IF (AND q123 (NOT p) t) p)', 			#Test DM
	# 'anAtom123',
	# '(NOT (NOT (NOT (IF p q))))',			#Test DM
	# '(NOT (AND p q))',            			#Test DM
	# '(NOT (NOT (AND p q)))'       			#Test DM
	# '(IF (IF (NOT p) (NOT q)) (IF p q))',       ### cnf1 Example from slide 59
	# '(OR p (NOT p) q (NOT q))',                 ### cnf2 3rd from P1_grader
	# '(AND p (NOT p) (NOT (NOT querty123)))',    ### cnf3 4th from P1_grader
	# '(IF (IF p (IF q r)) (IF q (IF p r)))',     ### cnf4 4th Example from slide 71
	# '(IF (NOT (OR p q123)) (AND q123 (NOT p)))', ### cnf5 Complex example
	# '(NOT (OR (AND (NOT p) q t) (IF (NOT q) (NOT t))))', ### cnf6 complex example
	# '(AND (AND (OR p q) (OR (NOT p) u r s t u v)))',
	# '(AND (AND (OR p q) (OR (NOT p) u r s t u v)))',
	# '(AND (OR p q r s) (OR a b c d (NOT p)))',
	# '(AND (OR p q r) (OR (NOT s) (NOT t) (NOT u)))',
	# '(AND (IF p q) p (NOT q))'
	# ]
	#
	# cnf0 = [['p'], [['p']], ['q'], [['t']], ['gf']]
	# cnf1 = [[['p'], ['p'], 'q'], ['q', ['p'], 'q']] # (-p v -p v q) ^ (q v -p v q)
	# cnf2 = [['p', ['p'], 'q', ['q']]]               # (p v -p v q v -q)
	# cnf3 = [['p'], [['p']], ['querty123']]          # (p) ^ (-p) ^ (querty123)
	# cnf4 = [['p', ['q'], ['p'], 'r'], ['q', ['q'], ['p'], 'r'], [['r'], ['q'], ['p'], 'r']] # (p v -q v -p v r) ^ (q v -q v -p v r) ^ (-r v -q v -p v r)
	# cnf5 = [['p', 'q123', 'q123'], ['p', 'q123', ['p']]]  # (p v q v q) ^ (p v q v -p)
	# cnf6 = [['p', ['q'], ['t']], [['q']], ['t']]    # (p v -q v -t) ^ (-q) ^ (-t)
	#
	# ## If you prefer a list of the cnfs use this
	#
	# cnfProblems = [[['p'], [['p']], ['q'], [['t']], ['gf']],
	# #[[['p'], ['p'], 'q'], ['q', ['p'], 'q']],
	# #[['p', ['p'], 'q', ['q']]],
	# #[['p'], [['p']], ['querty123']],
	# #[['p', ['q'], ['p'], 'r'], ['q', ['q'], ['p'], 'r'], [['r'], ['q'], ['p'], 'r']],
	# #[['p', 'q123', 'q123'], ['p', 'q123', ['p']]],
	# #[['p', ['q'], ['t']], [['q']], ['t']]
	# [['p', 'q'], ['p', ['r'], ['t']], ['p', 't', 's'], ['a', 'b'], [['c'], ['r'], 'd'], [['c'], 't', ['d']], ['c', 't', ['m']], ['c', ['m'], ['s']]],
	# [[['a'], 'b', 'c'], ['a', 'b', 'd'], ['a', 'c', ['d']], ['a', ['c'], 'd'], ['a', ['c'], ['d']], [['b'], ['c'], 'd'], [['a'], 'b', ['c']], [['a'], ['b'], 'c']]
	# ]
	#
	# variables = [['p', 'q', 't', 'gf'],
	# #['p', 'q'],
	# #['p', 'q'],
	# #['p', 'q', 'r'],
	# ['p', 'q', 'r', 't', 's', 'a', 'b', 'c', 'd', 'm'],
	# ['a', 'b', 'c', 'd']
	# ]

	# for i in range(len(problems)):
	# 	print(proveFormula(problems[i]), end = '\n\n')
	# 	#print(checkSatisfyability(cnfProblems[i], variables[i]))
