"""Array of OCaml versions tested in CI."""
import argparse


OCAML_VERSIONS = [
    '4.13.1',
    '5.1.0',
    ]


def _main():
    """Entry point."""
    index = _parse_args()
    ocaml_version = OCAML_VERSIONS[index]
    print(ocaml_version)


def _parse_args():
    """Return command-line arguments."""
    parser = argparse.ArgumentParser()
    parser.add_argument(
        'index',
        help='index in array of OCaml versions, '
            'to return the corresponding '
            'OCaml version',
        type=int)
    args = parser.parse_args()
    return args.index


if __name__ == '__main__':
    _main()
