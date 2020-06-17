SOURCES := $(shell find . -name '*.dfy')
LOG1_DIR = ./Logs_1
LOG2_DIR = ./Logs_2
LOG3_DIR = ./Logs_3
LOG4_DIR = ./Logs_4
LOG5_DIR = ./Logs_5
LOG_DIR = ./Logs

clean:
	rm -rf $(LOG_DIR) $(LOG1_DIR) $(LOG2_DIR) $(LOG3_DIR) $(LOG4_DIR) $(LOG5_DIR)
	# mkdir -p $(LOG_DIR) $(LOG1_DIR) $(LOG2_DIR) $(LOG3_DIR) $(LOG4_DIR) $(LOG5_DIR)

# make XXX file=<filename>
run1:
	@mkdir -p $(LOG1_DIR)
	@d=$$(date +%s); \
	dafny /compile:0 /print:$(LOG1_DIR)/$$file.print /dprint:$(LOG1_DIR)/$$file.dprint /proverLog:$(LOG1_DIR)/$$file.smt2 $$file /printTooltips /restartProver /proverOpt:O:smt.CASE_SPLIT=1 /trace > $(LOG1_DIR)/$$file.trace; \
	echo "CaseSplit 1,	$$file,	$$(($$(date +%s)-d))"

run2:
	@mkdir -p $(LOG2_DIR)
	@d=$$(date +%s); \
	dafny /compile:0 /print:$(LOG2_DIR)/$$file.print /dprint:$(LOG2_DIR)/$$file.dprint /proverLog:$(LOG2_DIR)/$$file.smt2 $$file /printTooltips /restartProver /proverOpt:O:smt.CASE_SPLIT=2 /trace > $(LOG2_DIR)/$$file.trace; \
	echo "CaseSplit 2,	$$file,	$$(($$(date +%s)-d))"

# default case-split (case-split = 3) settings
run3:
	@mkdir -p $(LOG3_DIR)
	@d=$$(date +%s); \
	dafny /compile:0 /print:$(LOG3_DIR)/$$file.print /dprint:$(LOG3_DIR)/$$file.dprint /proverLog:$(LOG3_DIR)/$$file.smt2 $$file /printTooltips /restartProver /trace > $(LOG3_DIR)/$$file.trace; \
	echo "CaseSplit 3,	$$file,	$$(($$(date +%s)-d))"

run4:
	@mkdir -p $(LOG4_DIR)
	@d=$$(date +%s); \
	dafny /compile:0 /print:$(LOG4_DIR)/$$file.print /dprint:$(LOG4_DIR)/$$file.dprint /proverLog:$(LOG4_DIR)/$$file.smt2 $$file /printTooltips /restartProver /proverOpt:O:smt.CASE_SPLIT=4 /trace > $(LOG4_DIR)/$$file.trace; \
	echo "CaseSplit 4,	$$file,	$$(($$(date +%s)-d))"

run5:
	@mkdir -p $(LOG5_DIR)
	@d=$$(date +%s); \
	dafny /compile:0 /print:$(LOG5_DIR)/$$file.print /dprint:$(LOG5_DIR)/$$file.dprint /proverLog:$(LOG5_DIR)/$$file.smt2 $$file /printTooltips /restartProver /proverOpt:O:smt.CASE_SPLIT=5 /trace > $(LOG5_DIR)/$$file.trace; \
	echo "CaseSplit 5,	$$file,	$$(($$(date +%s)-d))"

runall: run1 run2 run3 run4 run5

split1:
	@mkdir -p $(LOG1_DIR)
	@d=$$(date +%s); \
	dafny /compile:0 /print:$(LOG1_DIR)/$$file.print /dprint:$(LOG1_DIR)/$$file.dprint /proverLog:$(LOG1_DIR)/$$file-@PROC@.smt2 $$file /printTooltips /restartProver /proverOpt:O:smt.CASE_SPLIT=1 /timeLimit:1 /trace > $(LOG1_DIR)/$$file.trace; \
	echo "CaseSplit 1 (each query),	$$file,	$$(($$(date +%s)-d))"

split3:
	@mkdir -p $(LOG3_DIR)
	@d=$$(date +%s); \
	dafny /compile:0 /print:$(LOG3_DIR)/$$file.print /dprint:$(LOG3_DIR)/$$file.dprint /proverLog:$(LOG3_DIR)/$$file-@PROC@.smt2 $$file /printTooltips /restartProver /trace > $(LOG3_DIR)/$$file.trace; \
	echo "CaseSplit 3 (each query),	$$file,	$$(($$(date +%s)-d))"

all1:
	@mkdir -p $(LOG1_DIR)
	@for i in $(SOURCES); do \
   		d=$$(date +%s); \
		dafny /compile:0 /print:$(LOG1_DIR)/$$i.print /dprint:$(LOG1_DIR)/$$i.dprint /proverLog:$(LOG1_DIR)/$$i.smt2 $$i /printTooltips /restartProver /proverOpt:O:smt.CASE_SPLIT=1 /trace > $(LOG1_DIR)/$$i.trace; \
		echo "CaseSplit 1,	$$i,	$$(($$(date +%s)-d))"; \
	done

all3:
	@mkdir -p $(LOG3_DIR)
	@for i in $(SOURCES); do \
   		d=$$(date +%s); \
		dafny /compile:0 /print:$(LOG3_DIR)/$$i.print /dprint:$(LOG3_DIR)/$$i.dprint /proverLog:$(LOG3_DIR)/$$i.smt2 $$i /printTooltips /restartProver /trace > $(LOG3_DIR)/$$i.trace; \
		echo "CaseSplit 3,	$$i,	$$(($$(date +%s)-d))"; \
	done

