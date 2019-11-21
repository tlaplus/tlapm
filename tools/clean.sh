#!/bin/bash

cat >/tmp/lineclean.sh <<EOF
#!/bin/bash
ed \$1 <<INNEREOF
f
,s/  *\$//g
w
INNEREOF
EOF
chmod a-x /tmp/lineclean.sh

find src -name '*.ml' -o -name '*.mli' -print0 | xargs -0 -n 1 bash /tmp/lineclean.sh
