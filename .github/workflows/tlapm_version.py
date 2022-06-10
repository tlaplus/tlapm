"""Print `tlapm` version string `X.Y.Z`."""


# The environment constants
# `INSTALLER` and `DOWNLOADS` in
# `main.yml` and similar YAML files
# are used before the file `tlapm` has
# been installed.
#
# So running `tlapm --version` to
# obtain the version of `tlapm` is
# impossible. This is one reason why
# the version of `tlapm` is read
# from the OCaml source.


VERSION_FILE = 'src/version.ml'
    # ASSUMPTION: This file contains
    # exactly one line that starts
    # with the `_PREFIX` defined below.
_PREFIX = 'let (major,minor,micro)'


def _print_tlapm_version():
    """Print `tlapm` version."""
    print(_tlapm_version_string())


def tlapm_version_string() -> str:
    """Return `tlapm` version string."""
    tlapm_version = _read_tlapm_version(
        VERSION_FILE)
    return '.'.join(map(
        str, tlapm_version))


def _read_tlapm_version(
        filepath:
            str
        ) -> tuple[int, ...]:
    """Return `tlapm` version.

    The version of `tlapm` is read from
    the OCaml file at `filepath`.
    """
    with open(filepath, 'r') as fd:
        text = fd.read()
    lines = text.splitlines()
    def is_version_line(line):
        return line.startswith(_PREFIX)
    version_line, *rest = filter(
        is_version_line,
        lines)
    if rest:
        raise ValueError(rest)
    version = version_line.split('=')[-1]
    version = version.rstrip(';')
    return eval(version)


if __name__ == '__main__':
    _print_tlapm_version()
