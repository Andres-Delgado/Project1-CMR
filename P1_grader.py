"""This is basically the file we will use to grade your P1 submissions.
Obviously, the test problems hard-coded in here will be different. You
can use this to test your code. I'm using Python 3.4+.
- Dr. Licato
"""

import random
import traceback
import time


studentName = "TestStudent"
#there will likely be 10-15 problems
problems = ['p',
	'(NOT (NOT (NOT (NOT not))  )		)',
	'(OR p (NOT p) q (NOT q))',
	'(AND p (NOT p) (NOT (NOT querty123)))']
answers = ['S',
	'S',
	'S',
	'U']

maxProblemTimeout = 60


outFile = open("grade_"+studentName+".txt", 'w')

def prnt(S):
	global outFile
	outFile.write(str(S) + "\n")
	print(S)

try:
	F = open("p1.py", 'r', encoding="utf-8")
	exec("".join(F.readlines()))
except Exception as e:
	prnt("Couldn't open or execute 'p1.py': " + str(traceback.format_exc()))
	prnt("FINAL SCORE: 0")
	exit()


currentScore = 100
for i in range(0, len(problems)):
	#print("i", i)
	P = problems[i]
	A = answers[i]

	prnt('='*30)
	prnt("TESTING ON INPUT PROBLEM:")
	prnt(P)
	prnt("CORRECT OUTPUT:")
	prnt(str(A))
	prnt("YOUR OUTPUT:")
	try:
		startTime = time.time()
		result = proveFormula(P)
		prnt(result)
		endTime = time.time()
		if endTime-startTime > maxProblemTimeout:
			prnt("Time to execute was " + str(int(endTime-startTime)) + " seconds; a maximum of " + str(maxProblemTimeout) + " is allowed (-10 points)")
		elif result==A:
			prnt("Correct!")
		else:
			prnt("Incorrect (-10 points)")
			currentScore -= 10

	except Exception as e:
		prnt("Error while executing this problem: " + str(traceback.format_exc()))
		currentScore -= 10

prnt('='*30)
prnt('='*30)
prnt('='*30)
prnt("FINAL SCORE:" + str(currentScore))
