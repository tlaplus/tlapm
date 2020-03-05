#!/bin/sh
#  Copyright 2006 INRIA
#  $Id: equivbench.sh,v 1.5 2007-04-23 17:19:11 doligez Exp $

usage() { echo 'usage: equivbench.sh <n>' >&2; }

case $# in
 1) ;;
 *) usage; exit 2;;
esac

n=$1

awk 'BEGIN {
  print "$goal";
  for (i = 0; i < '$n'; i++){
    printf ("(<=> p_%d\n", i);
  }
  for (i = 0; i < '$n'; i++){
    printf ("(<=> p_%d\n", i);
  }
  print "T.";
  for (i = 0; i < 2 * '$n'; i++){
    printf ")";
  }
  print "";
}' >equivbenchtmp.znn

awk 'BEGIN {
  print "Require Import zenon.";
  print "Require Import zenon_equiv.";
  for (i = 0; i < '$n'; i++){
    printf ("Parameter p_%d : Prop.\n", i);
  }
  print "Load equivbenchtmp.";
}' >equivbenchmeta.v

#time ../zenon equivbenchtmp.znn -x equiv

time ../zenon equivbenchtmp.znn -x equiv -ocoqterm -short >equivbenchtmp.v
wc equivbenchtmp.v
#time coqc -I /usr/local/lib/zenon equivbenchmeta.v
