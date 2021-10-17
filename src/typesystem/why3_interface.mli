(************************************************************************
*  alt-ergo_interface.mli
*
*
*  Created by Hernán Vanzetto on 2 Nov 2013.
*  Copyright (c) 2013 __MyCompanyName__. All rights reserved.
************************************************************************)

open Expr.T

val solve : (Typ_e.t * expr) -> string
