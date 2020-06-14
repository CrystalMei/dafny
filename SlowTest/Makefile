SOURCES := $(shell find . -name '*.dfy')
LOG3_DIR = ./Logs_3
LOG1_DIR = ./Logs_1

clean1:
	@rm -rf $(LOG1_DIR)

clean3:
	@rm -rf $(LOG3_DIR)

dafny3:
	@mkdir -p $(LOG3_DIR)
	@for i in $(SOURCES); do \
   		d=$$(date +%s); \
		timeout 500s dafny /trace /compile:0 /print:$(LOG3_DIR)/$$i.print /dprint:$(LOG3_DIR)/$$i.dprint /proverLog:$(LOG3_DIR)/$$i.proverlog $$i /printTooltips > $(LOG3_DIR)/$$i.trace; \
		echo "$$i,	$$(($$(date +%s)-d))"; \
	done

dafny1:
	@mkdir -p $(LOG1_DIR)
	@for i in $(SOURCES); do \
   		d=$$(date +%s); \
		timeout 500s dafny /trace /compile:0 /print:$(LOG1_DIR)/$$i.print /dprint:$(LOG1_DIR)/$$i.dprint /proverLog:$(LOG1_DIR)/$$i.proverlog $$i /printTooltips /proverOpt:O:smt.CASE_SPLIT=1 > $(LOG1_DIR)/$$i.trace; \
		echo "$$i,	$$(($$(date +%s)-d))"; \
	done

.PHONY: clean1 clean3 dafny1 dafny3
