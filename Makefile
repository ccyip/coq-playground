.DEFAULT_GOAL := all

COQMAKEFILE:=Makefile.coq

%: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) $@

clean: cleanall
	$(RM) $(COQMAKEFILE) $(COQMAKEFILE).conf
.PHONY: clean

$(COQMAKEFILE): _CoqProject
	@coq_makefile -f _CoqProject -o $@

Makefile _CoqProject: ;
