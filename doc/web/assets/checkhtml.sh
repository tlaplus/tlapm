#!/bin/sh

cd ../content
printf '<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">\n'
printf '<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en-US" lang="en-US">\n'
printf '<head></head>\n'
printf '<body>\n'
printf '<ul>\n'
find . -name \*.html -print | awk '
BEGIN {
  prefix = "http://validator.w3.org/check?uri=http%3A%2F%2Fmsr-inria.inria.fr%2F%7Edoligez%2Fweb-js%2Fcontent%2F";
  suffix = "&charset=%28detect+automatically%29&doctype=Inline&group=0&user-agent=W3C_Validator%2F1.3";
}
{
  x = $0;
  gsub (/\//, "%2F", x);
  gsub (/\+/, "%2B", x);
  printf ("<li><a href=\"%s%s%s\">%s</a>\n", prefix, x, suffix, $0);
}
'
printf "</ul></body></html>\n"
