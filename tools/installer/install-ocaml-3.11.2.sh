#!/bin/bash

OCAML_RELEASE=3.11
OCAML_VERSION=${OCAML_RELEASE}.2
OCAMLDIST=ocaml-${OCAML_VERSION}

cat <<EOF
This script will download, build, and install the following
components:

   1. OCaml version ${OCAML_VERSION}
EOF

echo "Getting OCaml ${OCAML_VERSION}..."
if test -f ${OCAMLDIST}.tar.gz ; then
	echo "  (already present)"
else
	wget -q http://caml.inria.fr/pub/distrib/ocaml-${OCAML_RELEASE}/${OCAMLDIST}.tar.gz
fi

echo "Unpacking OCaml ${OCAML_VERSION} into ${OCAMLDIST}..."
if test -d ${OCAMLDIST} ; then
	echo "  (already unpacked)"
else
	tar xzf ${OCAMLDIST}.tar.gz
fi

echo "Building OCaml ${OCAML_VERSION}..."
if test -f ${OCAMLDIST}/.built ; then
	echo "  (already built)"
else
	cd ${OCAMLDIST}
	if test -f .configured ; then
		echo "  (already configured)"
	else
		./configure -no-shared-libs
		touch .configured
	fi
# 	cat >ocamldoc/remove_DEBUG <<\EOF
# #!/bin/sh
# echo "# 1 \"$1\""
# LC_ALL=C sed -e '/DEBUG/c\
# (* DEBUG statement removed *)' "$1"
# EOF
	make world.opt
	make install
	touch .built
fi

cat <<EOF
*******************************************************************************
OCaml ${OCAML_VERSION} has been successfully installed
*******************************************************************************
EOF
