import os
os.system('minisat \'try.cnf\' \'output\'.txt')

output = open('output.txt', 'r')
data = output.readlines()
for line in data[1:]:
	words = line.split()
	for word in words:
		if word[0] != '-':
			number = int(word)
			fluent = CNF.all_literals[number-1]
			print fluent
		# else:
		# 	number = int(word[1:])
		# 	fluent = CNF.all_literals[number-1]
		# 	print 'NOT-{}'.format(fluent)