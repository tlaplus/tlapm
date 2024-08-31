"""Change blank space in file."""
import argparse
import os
import subprocess
import sys
import warnings

# inline:
# import chardet


def _main():
    """Entry point."""
    _assert_python_ge_3()
    args = _parse_args()
    if args.rm_cr:
        _rm_cr(args.filename)
    elif args.rm_trailing_blank:
        _rm_trailing_blank(args.filename)
    elif args.chardet:
        _filetypes_in_directory(
            args.filename)
    else:
        raise ValueError(
            'nothing given to do')


def _rm_cr(filename):
    r"""Replace `\r\n` with `\n`.

    Reads from and writes to
    the file at `filename`.

    @type filename: `str`
    """
    if filename is None:
        raise ValueError(filename)
    with _open_file(filename) as fd:
        text = fd.readlines()
    out = list()
    for line in text:
        out.append(_replace_crlf(line))
    with _open_file(filename, 'wt') as fd:
        fd.writelines(out)


def _replace_crlf(line):
    r"""Replace line endings with `\n`.

    Replaces `\r\n` with `\n`
    in the string `line`.

    Raises `RuntimeError` if any other
    `\r` character is found in `line`.

    @type line: `str`
    @rtype: `str`
    """
    if line.endswith('\r\n'):
        line_out = f'{line[:-2]}\n'
    else:
        line_out = line
    if '\r' not in line_out:
        return line_out
    raise RuntimeError(
        r'found character `\r` '
        r'outside of the string `\r\n`, '
        'in the line: '
        f'{line!r}')


def _rm_trailing_blank(filename):
    """Replace trailing blank characters.

    Reads from and writes to
    the file at `filename`.

    @type filename: `str`
    """
    if filename is None:
        raise ValueError(filename)
    with _open_file(filename) as fd:
        lines_in = fd.readlines()
    lines_out = list()
    for i, line in enumerate(lines_in):
        if not line.endswith('\n'):
            raise RuntimeError(
                f'Line {i} of file '
                f'`{filename}` does not '
                r'end with the character `\n`. '
                f'Line {i} is: {line!r}')
        if '\r' in line:
            raise RuntimeError(
                f'Line {i} of file '
                f'`{filename}` contains '
                r'the character `\r`. '
                f'Line {i} is: {line!r}')
        line = line.rstrip()
        lines_out.append(f'{line}\n')
    with _open_file(filename, 'wt') as fd:
        fd.writelines(lines_out)


def _filetypes_in_directory(dir_tree):
    """Summarize file types in directory tree.

    @param dir_tree: root of directory tree
    """
    if dir_tree is None:
        raise ValueError(dir_tree)
    for dirpath, subdirs, files in os.walk(
            dir_tree):
        dirpath = os.path.normpath(dirpath)
        if dirpath.startswith('.git'):
            continue
        for file in files:
            filepath = os.path.join(
                dirpath, file)
            _print_filetype(filepath)


TEXT_TYPES = {
    'ASCII text',
    'empty',
    'SVG Scalable Vector Graphics image',
    'Unicode text',
    }
BINARY_TYPES = {
    'data',
    'GIF image data',
    'JPEG image data',
    'Mach-O',
    'OCaml interface file',
    'OCaml native object file',
    'PDF document',
    'PNG image data',
    'PostScript document text',
    'TeX DVI file',
    }


def _print_filetype(filepath):
    """Print output of `file` for unknown filetypes."""
    cmd = ['file', '--version']
    proc = subprocess.run(
        cmd, capture_output=True)
    if proc.returncode != 0:
        raise RuntimeError(
            'requires program `file` in `PATH`')
    cmd = ['file', filepath]
    proc = subprocess.run(
        cmd,
        capture_output=True,
        check=True,
        text=True)
    if proc.returncode != 0:
        raise RuntimeError(proc)
    out = proc.stdout
    _, message = out.split(
        sep=':',
        maxsplit=1)
    for filetype in TEXT_TYPES:
        if filetype in message:
            return
    for filetype in BINARY_TYPES:
        if filetype in message:
            return
    encoding = _chardet_file(filepath)
    if encoding is None:
        chardet_line = '    `chardet` error'
    else:
        chardet_line = (
            f'    `chardet` detected: {encoding}')
    print(
        f'{filepath}:\n'
        f'    `file` detected: {message.rstrip()}\n'
        f'{chardet_line}')


def _chardet_file(filepath):
    """Return encoding guess by `chardet`."""
    try:
        import chardet
    except ImportError:
        raise ImportError(
            'function `_chardet_file` requires '
            'the package `chardet`, which '
            'can be installed with '
            '`pip install chardet`')
    if not os.path.isfile(filepath):
        print(f'file not found: `{filepath}`')
        return None
    with open(filepath, 'rb') as fd:
        bytes = fd.read()
    res = chardet.detect(bytes)
    encoding = res['encoding']
    return encoding
    print(f'chardet of `{filepath}`: {encoding}')


def _open_file(filename, mode='rt'):
    """Return output of `open`."""
    return open(
        filename,
        mode=mode,
        encoding='utf-8',
        newline='')


def _parse_args():
    """Return namespace of command-line input."""
    parser = argparse.ArgumentParser(
        description=
            'Modify blank-space characters in '
            'given file. This script considers '
            r'`\n` and `\r\n` as line endings. '
            'For more information read: '
            '<https://en.wikipedia.org/'
            'wiki/Newline>')
    parser.add_argument(
        'filename',
        help='name of file to modify '
            'in-place')
    parser.add_argument(
        '--rm-cr',
        action='store_true',
        help=r'replace `\r\n` with `\n`. '
            'Raise `RuntimeError` if any '
            r'`\r` character is found '
            r'outside of `\r\n`.')
    parser.add_argument(
        '--rm-trailing-blank',
        action='store_true',
        help='replace trailing blank '
            r'characters with `\n`')
    parser.add_argument(
        '--chardet',
        action='store_true',
        help='detect file types')
    return parser.parse_args()


def _assert_python_ge_3():
    """Raise `RuntimeError` if Python <= 2."""
    if sys.version_info.major >= 3:
        return
    raise RuntimeError(
        'This script requires Python 3.')


if __name__ == '__main__':
    _main()
