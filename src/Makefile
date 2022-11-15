#
# Copyright (C) 2011  INRIA and Microsoft Corporation
#

COMPFLAGS = -annot -g -warn-error +1+2+5+6+8+10..26+29..31+36 \
            ${ADDCOMPFLAGS}
LINKFLAGS = -g ${ADDLINKFLAGS}

OPTTOOLS =

OCAMLC = ocamlc${OPTTOOLS}
OCAMLOPT = ocamlopt${OPTTOOLS}
OCAMLLEX = ocamllex${OPTTOOLS} -q
OCAMLDOC = ocamldoc${OPTTOOLS}

# NOTE: 2-space indentation is used to
# distinguish from the tabs (needed) in the recipes
FRONTEND_PACK = \
  frontend/symbol_commute \
  frontend/coalesce \
  frontend/action \
  frontend/pltl

BACKEND_PACK = \
  backend/types \
  backend/isabelle \
  backend/zenon \
  backend/ls4 \
  backend/fingerprints \
  backend/fpfile \
  backend/smt \
  backend/prep

MODULE_PACK = \
  module/m_t \
  module/m_visit \
  module/m_subst \
  module/m_fmt \
  module/m_globalness \
  module/m_gen \
  module/m_elab \
  module/m_standard \
  module/m_flatten \
  module/m_dep \
  module/m_parser \
  module/m_save

PROOF_PACK = \
  proof/p_t \
  proof/p_fmt \
  proof/p_subst \
  proof/p_visit \
  proof/p_gen \
  proof/p_simplify \
  proof/p_anon \
  proof/p_parser

PARS_PACK = \
  pars/error \
  pars/intf \
  pars/lazyList \
  pars/pco

EXPR_PACK = \
  expr/e_t \
  expr/e_fmt \
  expr/e_subst \
  expr/e_visit \
  expr/e_collect \
  expr/e_levels \
  expr/e_constness \
  expr/e_substitutive \
  expr/e_eq \
  expr/e_deref \
  expr/e_leibniz \
  expr/e_parser \
  expr/e_tla_norm \
  expr/e_temporal_props \
  expr/e_elab \
  expr/e_anon \
  expr/e_action \
  expr/e_level_comparison

TYPE_PACK = \
  type/t_t \
  type/t_visit \
  type/t_collect \
  type/t_hyps \
  type/t_synth

TYPESYSTEM_DIR = \
  typesystem/typ_t \
  typesystem/typ_e \
  typesystem/typ_c \
  typesystem/typ_cg1 \
  typesystem/typ_cg2 \
  typesystem/typ_impgraph \
  typesystem/typ_system

SMT_DIR = \
  smt/smtcommons \
  ${TYPESYSTEM_DIR} \
  smt/fmt \
  smt/boolify \
  smt/rewrite_trivial \
  smt/rewrite_arith \
  smt/rewrite \
  smt/ectx \
  smt/preprocess \
  smt/axioms

# FIXME remove useless files: dumpfp abstractor method_old backend/cooper
MODULES = \
  sysconf \
  util/ext \
  system \
  builtin \
  config \
  method \
  version \
  loc \
  toolbox_msg \
  params \
  ${PARS_PACK} \
  pars \
  util/property \
  util/util \
  ctx \
  errors \
  optable \
  util/fmtutil \
  isabelle_keywords \
  tla_parser \
  util/deque \
  alexer \
  ${EXPR_PACK} \
  expr \
  method_prs \
  ${PROOF_PACK} \
  proof \
  ${TYPE_PACK} \
  type \
  ${SMT_DIR} \
  util/timing \
  ${FRONTEND_PACK} \
  backend/toolbox \
  backend/schedule \
  ${BACKEND_PACK} \
  backend \
  ${MODULE_PACK} \
  module \
  tlapm_args \
  tlapm

INC0 = \
  -I ../backend \
  -I ../frontend \
  -I ../expr \
  -I ../module \
  -I ../proof \
  -I ../util \
  -I ../pars \
  -I ../type \
  -I ../typesystem \
  -I ../smt

INC = ${INC0:../%=%}
INC1 = ${INC0} -I ..

LIB_CMA = unix.cma str.cma
LIB_CMXA = ${LIB_CMA:.cma=.cmxa}

ML = ${MODULES:=.ml}
MLI = ${MODULES:=.mli}
MLT = ${MODULES:=.mlt}
CMO = ${MODULES:=.cmo}
CMI = ${MODULES:=.cmi}
CMX = ${MODULES:=.cmx}

.PHONY: default
default: tlapm.native

.PHONY: debug
debug: tlapm.byte

KAPUTT_COMP = \
   -package kaputt -pp "`ocamlfind query kaputt`/kaputt_pp.byte on cat"
KAPUTT_LINK = -package kaputt -linkpkg

# Warning: when you switch between debug and utest, you need
# to [make clean] because the .ml files are compiled with different options.

.PHONY: utest
utest:
	${MAKE} OCAMLC='ocamlfind ocamlc' \
	        ADDCOMPFLAGS='${KAPUTT_COMP}' ADDLINKFLAGS='${KAPUTT_LINK}' \
	        tlapm.byte

.PHONY: all
all: tlapm.byte tlapm.native

tlapm.byte: ${CMO} sysconf_stubs.o
	${OCAMLC} ${LINKFLAGS} -custom ${INC} ${LIB_CMA} ${CMO} \
	          sysconf_stubs.o -o $@

tlapm.native: ${CMX} sysconf_stubs.o
	${OCAMLOPT} ${LINKFLAGS} ${INC} ${LIB_CMXA} ${CMX} \
	            sysconf_stubs.o -o $@

sysconf_stubs.o: sysconf_stubs.c
	${OCAMLC} ${COMPFLAGS} -c $<

alexer.ml: alexer.mll
	${OCAMLLEX} alexer.mll

.PHONY: doc
doc: ${ML} ${MLI} ${CMI}
	${OCAMLDOC} ${INC} ${ML} ${MLI}

.PHONY: clean
clean:
	rm -f *.cm[iox] */*.cm[iox]
	rm -f *.annot */*.annot
	rm -f *.o */*.o
	rm -f alexer.ml
	rm -f tlapm.byte tlapm.native

.SUFFIXES: .cmi .cmo .cmx .o .ml .mli .mll

.ml.cmo:
	cd `dirname $<` \
	&& ${OCAMLC} -annot ${COMPFLAGS} -I . ${INC} ${INC1} -c `basename $<`

.mli.cmi:
	cd `dirname $<` \
	&& ${OCAMLC} ${COMPFLAGS} -I . ${INC} ${INC1} -c `basename $<`

.ml.cmx:
	cd `dirname $<` \
	&& ${OCAMLOPT} ${COMPFLAGS} -I . ${INC} ${INC1} -c `basename $<`

.PHONY: depend
depend: ${ML} ${MLI} ${MLT}
	: >.depend
	for i in ${ML} ${MLI}; do \
	  ocamldep -I `dirname $$i` ${INC} $$i \
	  | sed -e 's/^\([^.]*\).\(cm[ox]\) *:/\1.\2: \1.mlt/' >>.depend; \
	done
include .depend
