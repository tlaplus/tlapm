#!/bin/sh

# test.sh --- regression test script
#
# Author: Damien Doligez <damien.doligez@inria.fr>
#
# Copyright (C) 2008  INRIA and Microsoft Corporation


# To add a regression test, add a *.tla file in a subdirectory here.

VERSION=5

PM=tlapm
verbose=true
quick=false
all_files=true
rm -f temp/files

while : ; do
  case $# in 0) break;; esac
  case "$1" in
    -help|--help)
       echo "usage: test.sh [options] [file...]"
       echo "options are:"
       echo "  -help or --help  display this message and exit"
       echo "  -q   do not display progress messages"
       echo "  -v   display version number and exit"
       exit 0;;
    -q) verbose=false; shift;;
    -v) echo "test.sh version $VERSION"; exit 0;;
    -quick) quick=true; shift;;
    -*) echo "unknown option $1" >&2; exit 2;;
    *) find "$1" -name *.tla -print >>temp/files; all_files=false; shift;;
  esac
done

num_failed=0

if $all_files; then
  /usr/bin/find . -name '*.tla' -print | sort >temp/files
fi
while read f; do
  if $quick && test `wc -l $f | sed -e 's/^\(.*[0-9]\) .*/\1/'` -gt 200
  then continue
  fi
  base="${f%.tla}"
  dir=`dirname $f`
  failed=false
  if $verbose; then echo "testing $base.tla: " | tr -d '\012\015'; fi

  ( cd temp;
    $PM --cleanfp -I "../$dir" -C "../$base".tla >output 2>&1
  ) || failed=true
  grep -F "Zenon error" temp/output >/dev/null && failed=true
  grep "Exported obligations in module .* verified" temp/output >/dev/null || failed=true
  case "$failed" in
    false) if $verbose; then echo "pass"; fi;;
    *) if $verbose; then echo "## FAIL ##"; fi
       num_failed=`expr $num_failed + 1`
       ;;
  esac

done <temp/files

case "$num_failed" in
  0) echo "All tests passed.";;
  1) echo "#######################"
     echo "## 1 TEST FAILED     ##"
     echo "#######################"
     ;;
  *) echo "#######################"
     echo "## $num_failed TESTS FAILED ##"
     echo "#######################"
     exit 3
     ;;
esac
