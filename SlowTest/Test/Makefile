SOURCES := $(shell find . -name '*.dfy')
LOG3_DIR = ./Logs_3
LOG1_DIR = ./Logs_1
LOG_DIR = ./Logs

clean:
	rm -rf $(LOG_DIR)

Bitvectors:
	@mkdir -p $(LOG_DIR)
	@d=$$(date +%s); \
	dafny /trace /compile:0 /print:$(LOG_DIR)/Bitvectors.print /dprint:$(LOG_DIR)/Bitvectors.dprint /proverLog:$(LOG_DIR)/Bitvectors-@PROC@.smt2 ./Bitvectors.dfy /printTooltips /proverOpt:O:smt.CASE_SPLIT=1 > $(LOG_DIR)/Bitvectors.trace; \
	echo "Bitvectors,	$$(($$(date +%s)-d))"

COST:
	@mkdir -p $(LOG_DIR)
	@d=$$(date +%s); \
	dafny /trace /compile:0 /print:$(LOG_DIR)/COST.print /dprint:$(LOG_DIR)/COST.dprint /proverLog:$(LOG_DIR)/COST.smt2 ./COST-verif-comp-2011-4-FloydCycleDetect.dfy /printTooltips > $(LOG_DIR)/COST.trace; \
	echo "COST,	$$(($$(date +%s)-d))"

GenericSort:
	@mkdir -p $(LOG_DIR)
	@d=$$(date +%s); \
	dafny /trace /compile:0 /print:$(LOG_DIR)/GenericSort.print /dprint:$(LOG_DIR)/GenericSort.dprint /proverLog:$(LOG_DIR)/GenericSort.smt2 ./GenericSort.dfy /printTooltips /proverOpt:O:smt.CASE_SPLIT=1 > $(LOG_DIR)/GenericSort.trace; \
	echo "GenericSort,	$$(($$(date +%s)-d))"

LetExpr:
	@mkdir -p $(LOG_DIR)
	@d=$$(date +%s); \
	dafny /trace /compile:0 /print:$(LOG_DIR)/LetExpr.print /dprint:$(LOG_DIR)/LetExpr.dprint /proverLog:$(LOG_DIR)/LetExpr.smt2 ./LetExpr.dfy /printTooltips /proverOpt:O:smt.CASE_SPLIT=1 > $(LOG_DIR)/LetExpr.trace; \
	echo "LetExpr,	$$(($$(date +%s)-d))"

NoTypeArgs:
	@mkdir -p $(LOG_DIR)
	@d=$$(date +%s); \
	dafny /trace /compile:0 /print:$(LOG_DIR)/NoTypeArgs.print /dprint:$(LOG_DIR)/NoTypeArgs.dprint /proverLog:$(LOG_DIR)/NoTypeArgs.smt2 ./NoTypeArgs.dfy /printTooltips /proverOpt:O:smt.CASE_SPLIT=1 > $(LOG_DIR)/NoTypeArgs.trace; \
	echo "NoTypeArgs,	$$(($$(date +%s)-d))"

Rippling:
	@mkdir -p $(LOG_DIR)
	@d=$$(date +%s); \
	dafny /trace /compile:0 /print:$(LOG_DIR)/Rippling.print /dprint:$(LOG_DIR)/Rippling.dprint /proverLog:$(LOG_DIR)/Rippling.smt2 ./Rippling.dfy /printTooltips /proverOpt:O:smt.CASE_SPLIT=1 > $(LOG_DIR)/Rippling.trace; \
	echo "Rippling,	$$(($$(date +%s)-d))"

Lucas-up:
	@mkdir -p $(LOG_DIR)
	@d=$$(date +%s); \
	dafny /trace /compile:0 /print:$(LOG_DIR)/Lucas-up.print /dprint:$(LOG_DIR)/Lucas-up.dprint /proverLog:$(LOG_DIR)/Lucas-up.smt2 ./Lucas-up.dfy /printTooltips /proverOpt:O:smt.CASE_SPLIT=1 > $(LOG_DIR)/Lucas-up.trace; \
	echo "Lucas-up,	$$(($$(date +%s)-d))"

ListContents:
	@mkdir -p $(LOG_DIR)
	@d=$$(date +%s); \
	dafny /trace /compile:0 /print:$(LOG_DIR)/ListContents.print /dprint:$(LOG_DIR)/ListContents.dprint /proverLog:$(LOG_DIR)/ListContents.smt2 ./ListContents.dfy /printTooltips > $(LOG_DIR)/ListContents.trace; \
	echo "ListContents,	$$(($$(date +%s)-d))"

UnionFind:
	@mkdir -p $(LOG_DIR)
	@d=$$(date +%s); \
	dafny /trace /compile:0 /print:$(LOG_DIR)/UnionFind.print /dprint:$(LOG_DIR)/UnionFind.dprint /proverLog:$(LOG_DIR)/UnionFind.smt2 ./UnionFind.dfy /printTooltips > $(LOG_DIR)/UnionFind.trace; \
	echo "UnionFind,	$$(($$(date +%s)-d))"


clean1:
	rm -rf $(LOG1_DIR)

clean3:
	rm -rf $(LOG3_DIR)

dafny3:
	@mkdir -p $(LOG3_DIR)
	@for i in $(SOURCES); do \
   		d=$$(date +%s); \
		dafny /trace /compile:0 /print:$(LOG3_DIR)/$$i.print /dprint:$(LOG3_DIR)/$$i.dprint /proverLog:$(LOG3_DIR)/$$i.smt2 $$i /printTooltips > $(LOG3_DIR)/$$i.trace; \
		echo "$$i,	$$(($$(date +%s)-d))"; \
	done

dafny1:
	@mkdir -p $(LOG1_DIR)
	@for i in $(SOURCES); do \
   		d=$$(date +%s); \
		dafny /trace /compile:0 /print:$(LOG1_DIR)/$$i.print /dprint:$(LOG1_DIR)/$$i.dprint /proverLog:$(LOG1_DIR)/$$i.smt2 $$i /printTooltips /proverOpt:O:smt.CASE_SPLIT=1 > $(LOG1_DIR)/$$i.trace; \
		echo "$$i,	$$(($$(date +%s)-d))"; \
	done

.PHONY: clean1 clean3 dafny1 dafny3
