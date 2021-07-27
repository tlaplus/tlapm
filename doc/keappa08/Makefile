# these are the files that can be independently compiled
# (eg. "make main.pdf" or "make proof-language.pdf")
SRCS = main.tex \
       frontmatter.tex rearmatter.tex \
       outline.tex \
       abstract.tex introduction.tex proof-language.tex \
       obligations.tex backend.tex conclusion.tex \
       appendix.tex appendix-ll.tex appendix-discarded.tex

# these files are dependencies but CANNOT be independently compiled
SRCDEPS = easychair.cls \
          proof.sty syn.sty \
          submission.sty

.PHONY: all
all: main.pdf

.PHONY: test
test: ${SRCS:%.tex=%.ps}

# run once, then re-run until it's happy
%.dvi: %.tex ${SRCDEPS}
	if latex ${<} < /dev/null; then \
		true; \
	else \
		stat=$$?; touch ${<:%.tex=%.aux}; exit $$stat; \
	fi
	if grep -q "\\citation" ${<:%.tex=%.aux}; then \
		bibtex ${<:%.tex=%}; \
	fi
	while grep -q "Rerun to get cross" ${<:%.tex=%.log}; do \
		if latex ${<}; then \
			true; \
		else \
			stat=$$?; touch ${<:%.tex=%.dvi}; exit $$stat; \
		fi; \
	done

%.ps: %.dvi
	dvips -o ${<:%.dvi=%.ps} $<

%.pdf: %.ps
	ps2pdf $<

.PHONY: bib
bib: ${SRCS}
	bibtex ${SRCS:%.tex=%}

.PHONY: force
force: 
	${MAKE} `echo ${SRCS} ${SRCDEPS} | sed -e 's/ / -W /g' | sed -e 's/^/-W /'` all

.PHONY: clean
clean:
	${RM} ${SRCS:%.tex=%.aux} ${SRCS:%.tex=%.dvi} ${SRCS:%.tex=%.bbl} \
	    ${SRCS:%.tex=%.blg} ${SRCS:%.tex=%.log} ${SRCS:%.tex=%.inx} \
	    ${SRCS:%.tex=%.out} ${SRCS:%.tex=%.log} ${SRCS:%.tex=%.toc} \

.PHONY: spotless
spotless: clean
	${RM} ${SRCS:%.tex=%.ps} ${SRCS:%.tex=%.pdf}
