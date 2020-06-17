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

LOG1_DIR = ./Logs1
LOG2_DIR = ./Logs2
LOG3_DIR = ./Logs3
LOG4_DIR = ./Logs4
LOG5_DIR = ./Logs5

clean-logs:
	@for i in $(SLOW_TEST) $(FAST_TEST); do \
		cd $$i; \
		make clean-logs; \
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
		mkdir -p $$i/$(LOG1_DIR); \
		mkdir -p $$i/$(LOG2_DIR); \
		mkdir -p $$i/$(LOG3_DIR); \
		mkdir -p $$i/$(LOG4_DIR); \
		mkdir -p $$i/$(LOG5_DIR); \
	done
	@mkdir -p dafny0/$(LOG1_DIR)/snapshots
	@mkdir -p dafny0/$(LOG1_DIR)/snapshots/Inputs
	@mkdir -p wishlist/$(LOG1_DIR)/granted
	@mkdir -p dafny0/$(LOG2_DIR)/snapshots
	@mkdir -p dafny0/$(LOG2_DIR)/snapshots/Inputs
	@mkdir -p wishlist/$(LOG2_DIR)/granted
	@mkdir -p dafny0/$(LOG3_DIR)/snapshots
	@mkdir -p dafny0/$(LOG3_DIR)/snapshots/Inputs
	@mkdir -p wishlist/$(LOG3_DIR)/granted
	@mkdir -p dafny0/$(LOG4_DIR)/snapshots
	@mkdir -p dafny0/$(LOG4_DIR)/snapshots/Inputs
	@mkdir -p wishlist/$(LOG4_DIR)/granted
	@mkdir -p dafny0/$(LOG5_DIR)/snapshots
	@mkdir -p dafny0/$(LOG5_DIR)/snapshots/Inputs
	@mkdir -p wishlist/$(LOG5_DIR)/granted
	@for i in $(SLOW_TEST) $(FAST_TEST); do \
		cp Makefile.initial $$i/Makefile; \
	done

dafny3-fast:
	@for i in $(FAST_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny3; \
		cd ..;\
	done

dafny3-slow:
	@for i in $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny3; \
		cd ..;\
	done

dafny1-fast:
	@for i in $(FAST_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny1; \
		cd ..;\
	done

dafny1-slow:
	@for i in $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny1; \
		cd ..;\
	done

dafny3-10:
	@for i in $(FAST_TEST) $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny3-10; \
		cd ..;\
	done

dafny1-10:
	@for i in $(FAST_TEST) $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny1-10; \
		cd ..;\
	done

dafny3-100:
	@for i in $(FAST_TEST) $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny3-100; \
		cd ..;\
	done

dafny1-100:
	@for i in $(FAST_TEST) $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny1-100; \
		cd ..;\
	done

dafny1:
	@for i in $(FAST_TEST) $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny1; \
		cd ..;\
	done
dafny2:
	@for i in $(FAST_TEST) $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny2; \
		cd ..;\
	done
dafny3:
	@for i in $(FAST_TEST) $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny3; \
		cd ..;\
	done
dafny4:
	@for i in $(FAST_TEST) $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny4; \
		cd ..;\
	done
dafny5:
	@for i in $(FAST_TEST) $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny5; \
		cd ..;\
	done

dafny-simpl:
	@for i in $(FAST_TEST) $(SLOW_TEST); do \
		echo "[$$i]"; \
		cd $$i; \
		make dafny-simpl; \
		cd ..;\
	done

.PHONY: clean-mk clean3 clean1 dafny-simpl dafny1 dafny2 dafny3 dafny4 dafny5
