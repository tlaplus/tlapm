#!/bin/sh

cd ../content
printf '<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">\n'
printf '<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en-US" lang="en-US">\n'
printf '<head></head>\n'
printf '<body>\n'
printf '<ul>\n'
find . -name \*.html -print | awk '
BEGIN {
  prefix = "http://msr-inria.inria.fr/~doligez/web-js/content/";
  suffix = "";
}
{
  x = $0;
  gsub (/\//, "%2F", x);
  gsub (/\+/, "%2B", x);
  printf ("<li><a href=\"%s%s%s\">%s</a>\n", prefix, $0, suffix, $0);
}
'
printf "</ul></body></html>\n"
