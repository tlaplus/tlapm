#!/bin/bash

##
## That's a tlapm mock for some of the tlapm_lsp_parser test cases.
##

trap '{ echo "Interrupted."; exit 1; }' SIGINT

if [ "$1" != "--toolbox" ] ; then
    echo "ERROR: Expected --toolbox as a first argument."
    exit 2
fi

################################################################################
function CancelTiming() {
cat << EOF
@!!BEGIN
@!!type:warning
@!!msg:message before delay
@!!END
EOF
# Sleep has to be split in order to stip it faster.
for i in {1..30} ; do sleep 0.1; done
cat << EOF
@!!BEGIN
@!!type:warning
@!!msg:message after delay
@!!END
EOF
}

################################################################################
function AbnormalExit() {
cat << EOF
@!!BEGIN
@!!type:warning
@!!msg:this run is going to fail
@!!END
EOF
exit 1 # This.
}

################################################################################
function Empty() {
cat << EOF
\* TLAPM version 1.5.0
\* launched at 2023-09-30 23:39:35 with command line:
\* tlapm --toolbox 0,0 Empty.tla

@!!BEGIN
@!!type:obligationsnumber
@!!count:0
@!!END

(* created new ".tlacache/Empty.tlaps/Some.thy" *)
(* fingerprints written in ".tlacache/Empty.tlaps/fingerprints" *)
File "./Empty.tla", line 1, character 1 to line 5, character 4:
[INFO]: All 0 obligation proved.
EOF
}

################################################################################
function Some() {
cat << EOF
\* TLAPM version 1.5.0
\* launched at 2023-09-30 23:43:15 with command line:
\* tlapm --toolbox 0,0 Some.tla

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
}

################################################################################
function Echo() {
cat <<-EOF
@!!BEGIN
@!!type:warning
@!!msg:
EOF
cat # pipe stdin to stdout.
cat << EOF

@!!END
EOF
}

################################################################################
# We differentiate the testcases by the last argument, which is usually a TLA file.
last_arg=${@: -1}
case "$last_arg" in
    CancelTiming.tla) CancelTiming ;;
    AbnormalExit.tla) AbnormalExit ;;
    Empty.tla) Empty ;;
    Some.tla) Some ;;
    Echo.tla) Echo ;;
    *)
        echo "ERROR: Unexpected testcase, last_arg=$last_arg."
        exit 2
        ;;
esac
