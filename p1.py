"""
Jibreel Campbell
Abdullah Alsayyar
Andres Delgado

Project 1: DP-based SAT solver

9/20/18
"""

def proveFormula(F):

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

	# Step 4
	cnfList = Distribute(cnfList)
	# Converts the CNF S-Expression to clausal form
	cnfList = ClasualForm(cnfList)

	# Run Algorithm
	return checkSatisfyability(cnfList, variableList)	


def checkSatisfyability(formula, variables):
	"""This is the main function of the algorithm. It iterates through each variable and performs the following steps:
	Step 1. Checks if Unit-Prop or Pure-Literal rules can be applied. Also checks for (p) ^ (-p) and (p v (-p) v ...) cases.
		- if (p) ^ (-p) case is found, formula is 'U'
		- if (p v (-p) v ...) case is found, perform a "Real" branch and return the ORed result.
	Steps 2/3. Performs Unit Propagation and the Pure Literal Rule respectively. 
	Step 4. If Pure Literal was not applied, Make a "Leaf" of the formula and try to satisfy that leaf. If it results in 'S' then formula is 'S'
	Step 5. Perform Resolution."""

	# Will stop branch if it was called during last variable
	if not variables:
		return 'U'

	# Start the algorithm, going through the variables and applying the individual rules.
	for x in variables:
		pureVar = True
		varPure = 0
		unitPropForm = 0
		branch = True
		   
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
				#print("Branching")
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

		newFormula = formula[:]

		####### TESTING RESOLUTION 
		print("Resolution for: ", newFormula)
		print("Variable: ", x)
		resoFormula = doResolution(newFormula, x)
		for reso in resoFormula:
			print(reso)
		print("End Resolution.", end = '\n\n')

		newFormula = formula[:]
		# Unit Propagation on positive literal
		if unitPropForm == 1:
			for y in formula:
				if x in y: 
					newFormula.remove(y)
				elif [x] in y: 
					newFormula[newFormula.index(y)].remove([x])
		# Unit Propagation on negative literal
		elif unitPropForm == -1:
			for y in formula:
				if [x] in y:
					newFormula.remove(y)
				elif x in y:
					newFormula[newFormula.index(y)].remove(x)
		
		if newFormula == []:
			return 'S'
		formula = newFormula[:]
				
		# Pure Literal Rule
		if pureVar and varPure != 0:
			branch = False
			for y in formula:
				if varPure == 1:
					if x in y:
						newFormula.remove(y)
				elif varPure == -1:
					if [x] in y:
						newFormula.remove(y)
				
		if newFormula == []:
			return 'S'
		formula = newFormula[:]
		
		# If we didn't Perform rule 2 and if current variable x is in formula
		# Assign boolean value to x so that it satisfies its current clause (Unit-Prop)
		# Branch formula with assumed variable. Returns 'S' if branch is satisfied, continue to resolution otherwise.
		if branch:
			#print("In Branch")
			leaf = Branch(formula, variables[variables.index(x):])
			#print("Out of Branch")
			if leaf == 'S':
				return 'S'

		if formula == []:
			return 'S'
		elif [] in formula:
			return 'U'

		#print("Resolution for: ", newFormula)
		#print("Variable: ", x)
		#resoFormula = doResolution(newFormula, x)
		#for reso in resoFormula:
		#	print(reso)

		#formula = newFormula[:]
		#if formula == []:
		#	return 'S'
		#elif [] in formula:
		#	return 'U'
	return 'U'

def doResolution(currentFormula, currentVar):
	# Here I check if any resolvents can be made.
	# I check if there is [[p, a, b], [[p], c, d]] and it turns into [[a, b, c, d]] and I can eliminate clauses containing p or ~p
	# I also make sure that things like [[a, a], [[a], [a]]] can't be used for resolvent
	
	resolvent = False
	for y in currentFormula:
		if currentVar in y:
			for z in currentFormula:
				if z != y and [currentVar] in z and list(filter(lambda a: a != currentVar, y)) != [] and list(filter(lambda a: a != [currentVar], z)) != []:
					temp1 = list(filter(lambda a: a != currentVar, y))
					temp2 = list(filter(lambda a: a != [currentVar], z))
					temp1.extend(temp2)
					currentFormula.append(temp1)
					resolvent = True

	if resolvent:
		for y in currentFormula:
			if currentVar in y:
				currentFormula.remove(y)
			if [currentVar] in y:
				currentFormula.remove(y)

	return currentFormula

def Branch(formula, variables, realBranch = None):
	"""Branch/Leaf function: For the current variable p,
	Scans the clauses and finds a clause with variable p. 
	Assigns p a value so that it'll satisfy the clause and perform the algorithm with that assumption.
	If the original call of branch was a "Real" branch (case (p v (-p) v ...)) realBranch == True/False
		then this program will return the ORed result of the 2 branches.
	Else if this call was a "Leaf": realbranch == None
		then the program will only return when 'S', and will continue with the algorithm if it finds a 'U' conclusion."""

	branchFormula = formula[:]
	x = variables[0]
	
	# Each element in xIndex represents the clauses in the formula. Element == 1 means there is a positive form of p in the clause
	# element == -1 means negative, and element == 0 means there was not a p in the clause

	# Leaf
	if realBranch == None:
		xIndex = [1 if x in y else -1 if [x] in y else 0 for y in formula]
	# Real Branch with p = True
	elif realBranch:
		xIndex = [1]
	# Real Branch with p = False
	else:
		xIndex = [-1]

	# Found positive form of x in the formula
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
		if branchFormula == []:
			return 'S'
		elif [] in branchFormula:
			return 'U'

		# Recursive call to the algorithm starting at the next variable
		checkBranch = checkSatisfyability(branchFormula, variables[variables.index(x) + 1:])
		if checkBranch == 'S':
			return 'S'
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

if __name__ == "__main__":
	
	problems = [#'p', '(NOT p)',
	#'(NOT (NOT (NOT (NOT not))  )		)',	### 2nd from grader
	#'(IF p p)',
	#'(AND p (NOT p) q (NOT t) gf)',         # cnf0
	#'(OR five (OR three four))',
	#'(IF (AND q123 (NOT p) t) p)', 			#Test DM
	#'anAtom123',
	#'(NOT (NOT (NOT (IF p q))))',			#Test DM 
	#'(NOT (AND p q))',            			#Test DM
	#'(NOT (NOT (AND p q)))'       			#Test DM
	#'(IF (IF (NOT p) (NOT q)) (IF p q))',       ### cnf1 Example from slide 59
	#'(OR p (NOT p) q (NOT q))',                 ### cnf2 3rd from P1_grader
	#'(AND p (NOT p) (NOT (NOT querty123)))',    ### cnf3 4th from P1_grader
	#'(IF (IF p (IF q r)) (IF q (IF p r)))',     ### cnf4 4th Example from slide 71
	#'(IF (NOT (OR p q123)) (AND q123 (NOT p)))', ### cnf5 Complex example
	#'(NOT (OR (AND (NOT p) q t) (IF (NOT q) (NOT t))))' ### cnf6 complex example
	]
	
	cnf0 = [['p'], [['p']], ['q'], [['t']], ['gf']]
	cnf1 = [[['p'], ['p'], 'q'], ['q', ['p'], 'q']] # (-p v -p v q) ^ (q v -p v q)
	cnf2 = [['p', ['p'], 'q', ['q']]]               # (p v -p v q v -q)
	cnf3 = [['p'], [['p']], ['querty123']]          # (p) ^ (-p) ^ (querty123)
	cnf4 = [['p', ['q'], ['p'], 'r'], ['q', ['q'], ['p'], 'r'], [['r'], ['q'], ['p'], 'r']] # (p v -q v -p v r) ^ (q v -q v -p v r) ^ (-r v -q v -p v r)
	cnf5 = [['p', 'q123', 'q123'], ['p', 'q123', ['p']]]  # (p v q v q) ^ (p v q v -p)
	cnf6 = [['p', ['q'], ['t']], [['q']], ['t']]    # (p v -q v -t) ^ (-q) ^ (-t)

	## If you prefer a list of the cnfs use this
	
	cnfProblems = [#[['p'], [['p']], ['q'], [['t']], ['gf']],
	#[[['p'], ['p'], 'q'], ['q', ['p'], 'q']], 
	#[['p', ['p'], 'q', ['q']]], 
	#[['p'], [['p']], ['querty123']], 
	#[['p', ['q'], ['p'], 'r'], ['q', ['q'], ['p'], 'r'], [['r'], ['q'], ['p'], 'r']], 
	#[['p', 'q123', 'q123'], ['p', 'q123', ['p']]], 
	#[['p', ['q'], ['t']], [['q']], ['t']]
	#[['p', 'q'], ['p', ['r'], ['t']], ['p', 't', 's'], ['a', 'b'], [['c'], ['r'], 'd'], [['c'], 't', ['d']], ['c', 't', ['m']], ['c', ['m'], ['s']]],
	#[[['a'], 'b', 'c'], ['a', 'b', 'd'], ['a', 'c', ['d']], ['a', ['c'], 'd'], ['a', ['c'], ['d']], [['b'], ['c'], 'd'], [['a'], 'b', ['c']], [['a'], ['b'], 'c']]
	#[[['e'], 'f'], ['e', 'h', 'g'], [['e']], ['e', 'j'], ['h', ['j']]]
	[['p', 'q', 't'], [['p'], 'r'], ['p', 's'], [['p']]]
	]
	
	variables = [#['p', 'q', 't', 'gf'], 
	#['p', 'q'],
	#['p', 'q'], 
	#['p', 'q', 'r'],
	#['p', 'q', 'r', 't', 's', 'a', 'b', 'c', 'd', 'm'],
	#['a', 'b', 'c', 'd']
	#['e', 'f', 'h', 'g', 'j']
	['p', 'q', 't', 'r', 's']
	]
	
	for i in range(len(cnfProblems)):
	#	#print(proveFormula(problems[i]), end = '\n\n')
		print(checkSatisfyability(cnfProblems[i], variables[i]))
