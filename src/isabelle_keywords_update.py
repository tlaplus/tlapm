"""Generate OCaml list of Isabelle keywords.

This script reads the output of the invocation:
    isabelle outer_keywords Pure > isabelle_keywords.txt
The script `outer_keywords.scala` is present in this directory,
and contains its installation and usage documentation.
"""
infile = 'isabelle_keywords.txt'


def main():
    with open(infile, 'r') as f:
        text = f.read()
    for line in text.split('\n'):
        s = '"{line}";'.format(line=line)
        if not s:
            continue
        print(s)


if __name__ == '__main__':
    main()
