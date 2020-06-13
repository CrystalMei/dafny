SLOW_TEST=\
cloudmake \
comp \
dafny1 \
dafny2 \
dafny3 \
hofs \
traits \
vacid0 \
VerifyThis2015 \
VSComp2010 \
VSI-Benchmarks \
vstte2012 \
dafny0 \
dafny4 \
lambdas

SUPERSLOW_TEST=\
dafny4/Lucas-up.dfy \
lambdas/MatrixAssoc.dfy

FAST_TEST=\
exceptions \
expectations \
exports \
git-issues \
irondafny0 \
patterns \
triggers \
tutorial \
wishlist \

SUPERSLOW_TEST_SPLIT=\
dafny1 \
dafny4 \
lambdas

LOG_DIR = ./Logs
SPLIT_LOG_DIR = ./SplitLogs

clean-log:
	@for i in $(SLOW_TEST) $(FAST_TEST); do \
		cd $$i; \
		make clean-log; \
		cd ..;\
	done

clean-split:
	@for i in $(SLOW_TEST) $(FAST_TEST); do \
		cd $$i; \
		make clean-split; \
		cd ..;\
	done

clean-mk:
	@for i in $(SLOW_TEST) $(FAST_TEST); do \
		cd $$i; \
		make clean-mk; \
		cd ..;\
	done

prepare:
	@for i in $(SLOW_TEST) $(FAST_TEST); do \
		mkdir -p $$i/$(LOG_DIR); \
		mkdir -p $$i/$(SPLIT_LOG_DIR); \
	done
	@mkdir -p dafny0/$(LOG_DIR)/snapshots
	@mkdir -p dafny0/$(LOG_DIR)/snapshots/Inputs
	@mkdir -p wishlist/$(LOG_DIR)/granted
	@mkdir -p dafny0/$(SPLIT_LOG_DIR)/snapshots
	@mkdir -p dafny0/$(SPLIT_LOG_DIR)/snapshots/Inputs
	@mkdir -p wishlist/$(SPLIT_LOG_DIR)/granted
	@for i in $(SLOW_TEST) $(FAST_TEST); do \
		cp Makefile.initial $$i/Makefile; \
		mkdir -p $$i/$(SPLIT_LOG_DIR); \
	done

dafny-fast:
	@for i in $(FAST_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny; \
		cd ..;\
	done

dafny-slow:
	@for i in $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny; \
		cd ..;\
	done

dafny:
	@for i in $(FAST_TEST) $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny; \
		cd ..;\
	done

dafny-split-fast:
	@for i in $(FAST_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny-split; \
		cd ..;\
	done

dafny-split-slow:
	@for i in $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny-split; \
		cd ..;\
	done

dafny-split:
	@for i in $(FAST_TEST) $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny-split; \
		cd ..;\
	done

dafny-superslow:
	@for i in $(SUPERSLOW_TEST); do \
		echo "[$$i]"; \
		d=$$(date +%s); \
		dafny /trace /compile:0 /print:$(LOG_DIR)/$$i.print /dprint:$(LOG_DIR)/$$i.dprint /proverLog:$(LOG_DIR)/$$i.proverlog $$i /printTooltips > $(LOG_DIR)/$$i.trace; \
		echo "$$i,	$$(($$(date +%s)-d))"; \
		cd ..;\
	done

dafny-split-superslow:
	@for i in $(SUPERSLOW_TEST_SPLIT); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny-superslow; \
		cd ..;\
	done

dafny-simpl:
	@for i in $(FAST_TEST) $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny-simpl; \
		cd ..;\
	done

.PHONY: clean-mk clean-log clean-split dafny dafny-simpl dafny-split
