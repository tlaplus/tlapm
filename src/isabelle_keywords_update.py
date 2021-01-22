"""Generate OCaml list of Isabelle keywords.

This script reads the output of the invocation:
./Isabelle2021-RC2.app/Isabelle/bin/isabelle outer_keywords Pure
which is contained in the file with name equal to `infile`.
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

