.DEFAULT_GOAL := all

COQMAKEFILE := Makefile.coq
COQDOCMAKEFILE ?= coqdocjs/Makefile.doc
COQDOCJS_CP := true

-include $(COQDOCMAKEFILE)

%: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) $@

clean: cleanall
	$(RM) $(COQMAKEFILE) $(COQMAKEFILE).conf
.PHONY: clean

$(COQMAKEFILE): _CoqProject
	@coq_makefile -f _CoqProject -o $@

Makefile $(COQDOCMAKEFILE) _CoqProject: ;
