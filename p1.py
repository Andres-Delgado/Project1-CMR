"""
Jibreel Campbell
Abdullah Alsayyar
Andres Delgado

Project 1: DP-based SAT solver

9/20/18
"""

def proveFormula(F):
	"""Andres Delgado, Abdullah Alsayyar, Jibreel Campbell
	This function prepares the input F for the algorithm by performing the following steps:
	- Convert the formula into a S-Expression list
	- Convert the formula to CNF Form in S-Expression by applying Theorem 4.3.
	- Convert the formula to a clausal form.
	- Find all variables.
	- Run the Algorithm"""

	# Stores a binary tree list of the given input F
	formulaList = MakeList(F)
	if formulaList:
		if type(formulaList) is str:
			return 'S'
	else: return

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

	# Step 4
	cnfList = Distribute(cnfList)
	# Converts the CNF S-Expression to clausal form
	cnfList = ClasualForm(cnfList)

	# Extracts all variables from formula into variableList
	variableList = FindVariables(cnfList)

	# Run Algorithm
	return checkSatisfyability(cnfList, variableList)	

def checkSatisfyability(formula, variables):
	"""This is the main function of the algorithm. It iterates through each variable and performs the following steps:
	Step 1. Checks if Unit-Prop or Pure-Literal rules can be applied. Also checks for (p) ^ (-p) and (p v (-p) v ...) cases.
		- if (p) ^ (-p) case is found, formula is 'U'
		- if (p v (-p) v ...) case is found, perform a "Real" branch and return the ORed result.
	Steps 2/3. Performs the Unit Propagation and the Pure Literal Rule respectively. If any are applied, restart algorithm on next variable 
	Step 4. Make a "Leaf" of the formula and try to satisfy that leaf. If it results in 'S' then formula is 'S'
	Step 5. Perform Resolution."""
	
	# Will stop branch if it was called during last variable
	if not variables:
		return 'U'

	# Start the algorithm, going through the variables and applying the individual rules
	for x in variables:

		# Any CNF formula with 1 clause is always satisfiable, unless it's an empty clause
		if len(formula) == 1:
			if formula[0] == []:
				return'U'
			else: return 'S'

		# Checks if the current variable is in the formula, if not restart algorithm at the next variable
		# posForm will be passed into the Leaf call 
		xInFormula, posForm = False, False
		for arg in formula:
			if x in arg:
				posForm = True
				xInFormula = True
				break
			elif [x] in arg:
				xInFormula = True
				break
		if not xInFormula:
			continue

		# pureVar will determine if we can apply the Pure Literal Rule
		# varPure == 1 if Pure Literal is positive, -1 if Pure Literal is negative
		# unitPropForm == 1 if variable is positive, -1 if it's negative, 0 if we cannot perform Unit Propagation
		pureVar = True 
		varPure, unitPropForm = 0, 0
		   
		##### Step 1: Checking for rules and special cases ####
		for y in formula:
			# Checking if Unit Propagation is applicable and if (p) ^ (-p) exists
			if y == [x]:
				if unitPropForm == -1:
					return 'U'
				unitPropForm = 1
			elif y == [[x]]: 
				if unitPropForm == 1:
					return 'U'
				unitPropForm = -1

			# Case: (p v -p v ...) -> Perform a real branch, run the algorithm on both branches
			# branch1 and branch2 are new versions of the formula where p = True and P = False respectively
			if x in y and [x] in y: 
				branch1 = Branch(formula, variables[variables.index(x):], True)
				if branch1 == 'S':
					return 'S'
				branch2 = Branch(formula, variables[variables.index(x):], False)
				if branch2 == 'S':
					return 'S'							
				return 'U'
		
			# Checking if the Pure Literal rule is applicable
			if varPure == 0 and x in y:
				varPure = 1
			elif varPure == 0 and [x] in y:
				varPure = -1
			if varPure == -1 and x in y:
				pureVar = False
			elif varPure == 1 and [x] in y:
				pureVar = False
		
		# newFormula will be used to modify the formula when performing any rule
		newFormula = formula[:]

		##### Step 2: Unit Propagation #####
		# Positive literal
		if unitPropForm == 1:
			for y in formula:
				if x in y: 
					newFormula.remove(y)
				elif [x] in y: 
					newFormula[newFormula.index(y)].remove([x])	
	
		# Negative literal
		elif unitPropForm == -1:
			for y in formula:
				if [x] in y:
					newFormula.remove(y)
				elif x in y:
					newFormula[newFormula.index(y)].remove(x)
		
		# Unit Propagation was performed: check satisfiability, continue to next variable if no conclusion.
		if unitPropForm != 0:
			if newFormula == []:
				return 'S'
			elif [] in newFormula:
				return 'U'
			else:
				formula = newFormula[:]
				continue
					
		##### Step 3: Pure Literal #####
		# If performed, check satisfiablity, continue to next variable if no conclusion.
		if pureVar and varPure != 0:
			for y in formula:
				if varPure == 1:
					if x in y:
						newFormula.remove(y)
				elif varPure == -1:
					if [x] in y:
						newFormula.remove(y)
			if newFormula == []:
				return 'S'
			elif [] in newFormula:
				return 'U'
			else:
				formula = newFormula[:]
				continue
		
		##### Step 4: Leaf #####
		# Assign boolean value to x so that it satisfies its current clause.
		# Branch formula with assumed variable. Returns 'S' if branch is satisfied, continue to resolution otherwise.
		leaf = Branch(formula, variables[variables.index(x):], posForm)
		if leaf == 'S':
			return 'S'

		##### Step 5: Resolution #####
		resoFormula = Resolution(formula, x)

		if resoFormula == []:
			return 'S'
		elif [] in resoFormula:
			return 'U'
		else: formula = resoFormula[:]
	return 'U'

def Resolution(formula, variable):
	"""This function performs the resolution rule to the formula for the given variable."""

	# resultFormula will be used to modify formula
	resultFormula = formula[:]
	posClause, negClause = [], []
	posExists, negExists = False, False

	# Iterates through the formula to find all clauses containing p or -p
	# Stores each clause with p in posClause and each clause with -p in negClause
	# Also deletes the variable p after storing the clause
	for arg in formula:
		if variable in arg:
			posExists = True
			posClause.append(arg[:])
			posClause[posClause.index(arg)].remove(variable)
			resultFormula.remove(arg)
		elif [variable] in arg:
			negExists = True
			negClause.append(arg[:])
			negClause[negClause.index(arg)].remove([variable])
			resultFormula.remove(arg)
	
	# If there was no instance of p in one clause and -p in another (posExists and negExists are both False)
	# Then Resolution doesnt apply
	if posExists and negExists:
		reso = []
	else: return formula

	# Performs resolution on all the clauses
	reso = [x+y for x in posClause for y in negClause]

	# Removes all duplicates variables in the clauses
	for arg in reso:
		stack = []
		for y in arg:
			if y not in stack:
				stack.append(y)
		resultFormula.append(stack)
	return resultFormula

def Branch(formula, variables, varForm):
	"""Branch/Leaf function: For the current variable p,
	Assigns p = varForm so that it'll satisfy a clause and runs the algorithm with that assumption.
	If the original call of branch was a "Real" branch (case (p v (-p) v ...))
		then this program will return the ORed result of this Branch call and the other Branch call
	Else if this call was a "Leaf":
		then the program will only return when 'S', and will continue with the algorithm if it finds a 'U' conclusion."""

	branchFormula = formula[:]
	x = variables[0]
	
	# Variable is assigned True
	if varForm:
		for y in formula:
			if x in y: 
				branchFormula.remove(y)
			elif [x] in y: 
				branchFormula[branchFormula.index(y)].remove([x])
	# Variable is assigned False
	elif not varForm:
		for y in formula:
			if [x] in y:
				branchFormula.remove(y)
			elif x in y:
				branchFormula[branchFormula.index(y)].remove(x)
	# A value was assigned, check satisfiability
	if branchFormula != formula:
		if branchFormula == []:
			return 'S'
		elif [] in branchFormula:
			return 'U'

		# Recursive call to the algorithm starting at the next variable
		checkBranch = checkSatisfyability(branchFormula, variables[variables.index(x) + 1:])
		if checkBranch == 'S':
			return 'S'
	return 'U'

def ClasualForm(formula):
	"""This function takes the current CNF formula in S-Expression and converts it to a clausal form.
	formula = ((p v -q) ^ (-p) ^ (q)) --> formula = [[p, [q]], [[p]], [q]]"""

	# List in a negated variable
	if formula[0] == "NOT":
		return formula[1:]
	else: stack = []

	# Iterates through the clauses in the formula
	for arg in range(len(formula)):
		if type(formula[arg]) is list:

			# There is a negated variable inside a single clause
			if (formula[0] == "AND") and (formula[arg][0] == "NOT"):
				formula[arg] = [formula[arg][1:]]
			# else, search inside the clause
			else: 
				formula[arg] = ClasualForm(formula[arg])

		# Makes the clause a list, needed when encountering single variables
		elif (arg > 0) and (formula[0] == "AND"):
			formula[arg] = [formula[arg]]

		# Stack of all the clauses/variables
		if (arg > 0) and (formula[arg] not in stack):
			stack.append(formula[arg])

	# Stores the stack to the formula, ommiting the operation
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

def FindVariables(formula):
	"""Returns a list of all the variables in the formula"""

	variables = []
	for arg in formula:
		for var in arg:
			# Checks negative variable var
			if type(var) is list:
				if var[0] not in variables:
					variables.append(var[0])
			# Checks positive variable var
			elif var not in variables:
				variables.append(var)
	return variables
