-include CONFIGURE

VSTDIR=../VST-A-tool/VST-2.5
VSTADIR=../VST-A-tool/VST-A
COMPCERTDIR=../VST-A-tool/VST-2.5/compcert

COQC = $(COQBIN)coqc
COQDEP = $(COQBIN)coqdep

CPROGSDIR = .
CPROGS = heap

-include $(CPROGSDIR)/heap/Makefile.config

CPROG_FILES  = $(CPROGS:%=$(CPROGSDIR)/%/program.v)
CDEF_FILES   = $(CPROGS:%=$(CPROGSDIR)/%/definitions.v)
CANNOT_FILES = $(CPROGS:%=$(CPROGSDIR)/%/annotation.v)

CVERIF_FILES = $(CPROG_FUNCS:%=$(CPROGSDIR)/%/verif.v)
CPROG_PATH_FILES = $(CPROG_PATHS:%=$(CPROGSDIR)/%.v)
CPROG_PATH_VERIF_FILES = $(CPROG_PATHS:%=$(CPROGSDIR)/%_verif.v)

VST_DIRS = msl sepcomp veric floyd
INCLUDE_ACLIGHT = -Q $(VSTADIR)/csplit Csplit -Q $(VSTADIR)/floyd-seq FloydSeq -R $(CPROGSDIR) cprogs
INCLUDE_COMPCERT = -R $(COMPCERTDIR) compcert
INCLUDE_VST = $(foreach d, $(VST_DIRS), -Q $(VSTDIR)/$(d) VST.$(d))
INCLUDE_UTIL = -Q $(VSTADIR)/utils utils
COQFLAGS = -w -omega-is-deprecated $(INCLUDE_ACLIGHT) $(INCLUDE_VST) $(INCLUDE_COMPCERT) $(INCLUDE_UTIL)

FILES =  \
  $(CPROG_FILES) $(CDEF_FILES) $(CANNOT_FILES) \
  $(CVERIF_FILES) $(CPROG_PATH_FILES) $(CPROG_PATH_VERIF_FILES)

all:
	@test -f .depend || $(MAKE) depend
	@$(MAKE) proof

rebuild:
	@rm -f .depend
	@$(MAKE) all

proof: $(FILES:%.v=%.vo)

depend:
	@$(COQDEP) $(COQFLAGS) $(FILES) > .depend

%.vo: %.v
	@echo "COQC       $<"
	@$(COQC) $(COQFLAGS) $<

-include .depend

.PHONY: all rebuild proof depend clean cleanprogs config

clean:
	@rm -f .depend
	@rm -f $(FILES:%.v=%.vo)
	@rm -f $(FILES:%.v=%.vos)
	@rm -f $(FILES:%.v=%.vok)
	@rm -f $(FILES:%.v=%.glob)
	@rm -f .lia.cache
	@rm -f $(foreach f, $(FILES:%.v=%), $(dir $(f)).$(shell* basename $(f)).aux)

cleanprogs:
	@rm -f .depend
	@rm -f $(GENERATED:%.v=%.vo)
	@rm -f $(GENERATED:%.v=%.vos)
	@rm -f $(GENERATED:%.v=%.vok)
	@rm -f $(GENERATED:%.v=%.glob)
	@rm -f $(foreach f, $(GENERATED:%.v=%), $(dir $(f)).$(shell basename $(f)).aux)

config:
	@echo "COQBIN=" > Makefile.config
	@echo "VSTDIR=../VST-2.5-patch" >> Makefile.config
	@echo "COMPCERTDIR=../VST-2.5-patch/compcert" >> Makefile.config
	@echo "COMPCERTADIR=../compcert-for-vsta" >> Makefile.config
