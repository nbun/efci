# Makefile for generating and executing benchmarks

# Log and result files:
LOGFILE=BENCHLOG.txt
RESULTFILE=BENCHRESULTS.csv

# The binaries of the various systems:
PAKCS=/opt/pakcs/pakcs3/bin/pakcs
KICS2=/opt/kics2/kics3/bin/kics2
KMCC=../kmcc/bin/kmcc
CURRY2GO=curry2go
STACK=stack

BENCHNAMES  = AddNum AddNum5 NRev PermSort PermSortPeano PrimesHO Queens ReverseHO Select SortPrimes TakInt TakPeano YesSharingAcrossND NoSharingAcrossND
CURRYFILES  = $(foreach prog, $(BENCHNAMES), $(addsuffix .curry,   $(prog)))
PAKCSEXEC   = $(foreach prog, $(BENCHNAMES), $(addsuffix _pakcs,   $(prog)))
KICS2EXEC   = $(foreach prog, $(BENCHNAMES), $(addsuffix _kics2,   $(prog)))
KMCCEXEC    = $(foreach prog, $(BENCHNAMES), $(addsuffix _kmcc,    $(prog)))
C2GEXEC     = $(foreach prog, $(BENCHNAMES), $(addsuffix _c2g,     $(prog)))
PLUGINEXEC  = $(foreach prog, $(BENCHNAMES), $(addsuffix _plugin,  $(prog)))
PLUGINEXECD = $(foreach prog, $(BENCHNAMES), $(addsuffix _pluginD, $(prog)))

BENCHPAKCS   = $(foreach prog, $(PAKCSEXEC),   $(addprefix bench_,   $(prog)))
BENCHKICS2   = $(foreach prog, $(KICS2EXEC),   $(addprefix bench_,   $(prog)))
BENCHKMCC    = $(foreach prog, $(KMCCEXEC),    $(addprefix bench_,   $(prog)))
BENCHC2G     = $(foreach prog, $(C2GEXEC),     $(addprefix bench_,   $(prog)))
BENCHPLUGIN  = $(foreach prog, $(PLUGINEXEC),  $(addprefix benchpl_, $(prog)))
BENCHPLUGIND = $(foreach prog, $(PLUGINEXECD), $(addprefix benchpl_, $(prog)))

.PHONY: all
all:
	$(MAKE) benchall 2>&1 | tee $(LOGFILE)
	echo "Program\\treal\\tuser\\tsys" > $(RESULTFILE)
	@grep --text BENCHPROG $(LOGFILE) | cut -f2- >> $(RESULTFILE)
	@echo Benchmark results stored in file: $(RESULTFILE)

.PHONY: benchall
benchall: benchpakcs benchkics2 benchc2g benchkmcc

# Running all Curry benchmarks with PAKCS:
.PHONY: benchpakcs
benchpakcs:
	$(MAKE) $(PAKCSEXEC)
	$(MAKE) $(BENCHPAKCS)

# Running all Curry benchmarks with KICS2:
.PHONY: benchkics2
benchkics2:
	$(MAKE) $(KICS2EXEC)
	$(MAKE) $(BENCHKICS2)

# Running all Curry benchmarks with Curry2Go:
.PHONY: benchc2g
benchc2g:
	$(MAKE) $(C2GEXEC)
	$(MAKE) $(BENCHC2G)

# Running all Curry benchmarks with kmcc:
.PHONY: benchkmcc
benchkmcc: buildkmcc
	$(MAKE) $(KMCCEXEC)
	$(MAKE) $(BENCHKMCC)

# Running all Curry benchmarks with the plugin:
.PHONY: benchplugin
benchplugin: buildplugin
	$(MAKE) $(BENCHPLUGIN)
	$(MAKE) $(BENCHPLUGIND)

.PHONY: buildkmcc
buildkmcc:
	cd ../kmcc && $(MAKE)

.PHONY: buildplugin
buildplugin:
	cd curry-ghc-language-plugin && $(STACK) build sandbox --copy-bins --local-bin-path ..

.PHONY: buildplugin_prof
buildplugin_prof:
	cd curry-ghc-language-plugin && $(STACK) build sandbox --profile --copy-bins --local-bin-path ..

######################################################################

benchpl_%_plugin:
	@echo "RUNNING BENCHMARK: $*_plugin"
	@time -f "BENCHPROG:\t$*_plugin\t%e\t%U\t%S" ./sandbox $*
	@time -f "BENCHPROG:\t$*_plugin\t%e\t%U\t%S" ./sandbox $*
	@time -f "BENCHPROG:\t$*_plugin\t%e\t%U\t%S" ./sandbox $*

benchpl_%_pluginD:
	@echo "RUNNING BENCHMARK: $*_pluginD"
	@time -f "BENCHPROG:\t$*_pluginD\t%e\t%U\t%S" ./sandbox $*D
	@time -f "BENCHPROG:\t$*_pluginD\t%e\t%U\t%S" ./sandbox $*D
	@time -f "BENCHPROG:\t$*_pluginD\t%e\t%U\t%S" ./sandbox $*D

bench_%: %
	@echo "RUNNING BENCHMARK: $*"
	@time -f "BENCHPROG:\t$*\t%e\t%U\t%S" ./$*
	@time -f "BENCHPROG:\t$*\t%e\t%U\t%S" ./$*
	@time -f "BENCHPROG:\t$*\t%e\t%U\t%S" ./$*

%_pakcs: %.curry
	@echo Generating $@ from $<
	$(PAKCS) --nocypm :l $* :save :q
	mv $* $@

%_kics2: %.curry
	@echo Generating $@ from $<
	$(KICS2) --nocypm :l $* :save :q
	mv $* $@

%_c2g: %.curry
	@echo Generating $@ from $<
	$(CURRY2GO) --nocypm :l $* :save :q
	mv $* $@

%_kmcc: %.curry
	@echo Generating $@ from $<
	$(KMCC) --nocypm :l $* :save :q
	mv $* $@

.PHONY: clean
clean:
	rm -f $(PAKCSEXEC) $(KICS2EXEC) $(C2GEXEC) $(KMCCEXEC) $(PLUGINEXEC) $(PLUGINEXECD)
	rm -f $(LOGFILE) $(RESULTFILE)
	rm -f ./sandbox
	rm -rf .curry
	cd curry-ghc-language-plugin && $(STACK) clean
