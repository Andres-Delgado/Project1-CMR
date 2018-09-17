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

	print("Given:     ", F)

	#Stores a binary tree list of the given input F
	formulaList = MakeList(F)
	if formulaList:
		print("Formula:   ", formulaList)
	else: return

	# Extracts all variables from formula into variableList
	variableList = FindVariables(formulaList)
	if variableList:
		print("Variables: ", variableList)
	else: return

	# Converting to CNF: Theroem 4.3
	# Step 1
	cnfList = EliminateOps(formulaList)
	if cnfList:
		print("1.	Elim Ops:     ", cnfList)
	else: return

	# Steps 2/3 combined
	cnfList = DeMorgans(cnfList)
	if cnfList:
		print("2/3.	DM/Negations: ", cnfList)
	else: return


	#
	#print(formulaList)
	return "Good"


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

		# Case where there is a double negation on a signle variable
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

def resolution(clausalFormFormula, vars):
	"""
	performs the resolution rule on a bool formula in clausal form:

	Given some CNF formula F
	For some variable p:
		For every clause C1 containing p:
			For every clause C2 containing ¬p:
				Create the resolvent CR from C1 and C2, add it to assignments
				NOTE: even if CR is empty, it must be kept!
	Remove all clauses containing p or ¬p from F

	clausalForm = a list of clauses representing a cnf formula
	[ [p, q], [[p]], [p, [q], r, s, t, u, v] ]
	if only considering the 'q's,the function will return this:
	[ [[p]], [p, p, r, s, t, u, v] ]
	the second term is the resolvent of the 1st and 3rd terms of the previous

	vars = a list containing all the variables found in the statement
	[p, q, r, s, t, u, v]


	a list within an inner list if considered a negative variable
	"""

	 # Will store all of the statements after resolution operation has finished
	expressionWithResolution = [];

	for var in vars: # apply resolution to each variable
		clausesWithVar = findClausesWithVariable(clausalFormFormula, var) # a list containing the clauses that use the var
		clausesWithNegVar = findClausesWithVariable(clausalFormFormula, [var])

		#print('\nvar:', var, '\nclauses:\n', clausesWithVariable)
		print('\nvar:', var, '\nclauses:\n', clausesWithVar)
		print('\nvar:', var, '\nneg clauses:\n', clausesWithNegVar)


	return expressionWithResolution;

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

if __name__ == "__main__":

	# problems = [#'p',
	# #'(NOT (NOT (NOT (NOT not))  )		)',
	# #'(IF p p)',
	# #'(AND p (NOT p) q (NOT t) gf)',
	# #'(OR five (OR three four))',
	# '(IF (IF (NOT p) (NOT q)) (IF p q))', 	### Example from slide 59
	# '(IF (AND q123 (NOT p) t) p)', 			#Test DM
	# #'(IF (NOT (OR p q123)) (AND q123 (NOT p)))',
	# #'anAtom123',
	# '(NOT (NOT (NOT (IF p q))))',			#Test DM
	# '(NOT (AND p q))',            			#Test DM
	# #'(NOT (NOT (AND p q)))'       			#Test DM
	# ]
	#
	# '''
	# problems = ['(IF a b)',
	# '(AND (NOT a) b c d)']
	# '''

	# for i in range(len(problems)):
	# 	#print("Answer: ", end = '')
	# 	print(proveFormula(problems[i]), end = '\n\n')

	test = [ ['p', 'q'], [['p'], 'u'], ['p', ['q'], 'r', 's', 't', 'u', 'v'] ]
	print("\nfinal result", resolution(test, ['p', 'q', 'r', 's', 't', 'u', 'v']))
