DIR1 = ./Logs
DIR3 = ./Logs_Solver3

clean:
	rm -rf $(DIR1) $(DIR3)

run-ddl:
	@mkdir -p $(DIR3)
	@for i in 1 2 3 4 5; do \
		dafny /compile:0 ./DLL_Dafny_DDL.dfy /restartProver /trace /timeLimit:100 > $(DIR3)/$$i-SolverDefault.trace; \
		dafny /compile:0 ./DLL_Dafny_DDL.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:smt.arith.solver=3 > $(DIR3)/$$i-Solver3.trace; \
		echo "$$i, done"; \
	done

run-dl:
	@mkdir -p $(DIR1)
	@for i in 1 2 3 4 5; do \
		dafny /compile:0 ./DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 > $(DIR1)/$$i-SolverDefault.trace; \
		dafny /compile:0 ./DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:smt.arith.solver=1 > $(DIR1)/$$i-Solver1.trace; \
		dafny /compile:0 ./DLL_Dafny_WDL3_correctedge.dfy /restartProver /trace /timeLimit:100 /proverOpt:O:smt.arith.solver=7 > $(DIR1)/$$i-Solver7.trace; \
		echo "$$i, done"; \
	done