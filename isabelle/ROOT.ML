(*  Title:      TLA+/ROOT.ML
    Author:     Stephan Merz, LORIA
    Copyright (C) 2008-2011  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2011
    Time-stamp: <2011-07-26 16:53:42 merz>

Encoding of TLA+ constant level as an object logic in Isabelle.
*)

val banner = "TLA+";
writeln banner;

use_thy "Constant";
use_thy "Zenon";
