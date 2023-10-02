#!/bin/bash

##
## That's a tlapm mock for some of the tlapm_lsp_parser test cases.
##

if [ "$1" != "--toolbox" ] ; then
    echo "ERROR: Expected --toolbox as a first argument."
    exit 2
fi

# We differentiate the testcases by the last argument, which is usually a TLA file.
last_arg=${@: -1}
case "$last_arg" in
    TimingExit0.tla)
        echo Starting...
        sleep 1; echo First proof done
        sleep 1; echo Second proof fone
        sleep 1; echo All proofs OK.
        exit 0
        ;;
    TimingExit1.tla)
        echo Starting...
        sleep 1; echo First proof done
        sleep 1; echo Second proof fone
        sleep 1; echo All proofs OK.
        exit 1
        ;;
    Empty.tla)
    cat << EOF
\* TLAPM version 1.5.0
\* launched at 2023-09-30 23:39:35 with command line:
\* tlapm --toolbox 0 0 Empty.tla

@!!BEGIN
@!!type:obligationsnumber
@!!count:0
@!!END

(* created new ".tlacache/Empty.tlaps/Some.thy" *)
(* fingerprints written in ".tlacache/Empty.tlaps/fingerprints" *)
File "./Empty.tla", line 1, character 1 to line 5, character 4:
[INFO]: All 0 obligation proved.
EOF
    ;;
    Some.tla)
cat << EOF
\* TLAPM version 1.5.0
\* launched at 2023-09-30 23:43:15 with command line:
\* tlapm --toolbox 0 0 Some.tla

(* loading fingerprints in ".tlacache/Some.tlaps/fingerprints" *)
@!!BEGIN
@!!type:obligation
@!!id:1
@!!loc:5:3:5:10
@!!status:to be proved
@!!END

@!!BEGIN
@!!type:obligationsnumber
@!!count:1
@!!END

** Unexpanded symbols: ---

@!!BEGIN
@!!type:obligation
@!!id:1
@!!loc:5:3:5:10
@!!status:proved
@!!prover:smt
@!!meth:time-limit: 5; time-used: 0.0 (0%)
@!!already:false
@!!END

(* created new ".tlacache/Some.tlaps/Some.thy" *)
(* fingerprints written in ".tlacache/Some.tlaps/fingerprints" *)
File "./Some.tla", line 1, character 1 to line 6, character 4:
[INFO]: All 1 obligation proved.
EOF
    ;;
    *)
        echo "ERROR: Unexpected testcase, last_arg=$last_arg."
        exit 2
        ;;
esac
