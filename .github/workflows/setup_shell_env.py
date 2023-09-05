"""Define environment variables for CI testing."""
import sys

import tlapm_version as _version


def _main():
    """Entry point."""
    tlapm_version = _version.tlapm_version_string()
    env_vars = _env_vars(tlapm_version)
    shell_definitions = _make_shell_definitions(
        env_vars)
    print(shell_definitions)


def _env_vars(tlapm_version: str) -> dict:
    """Return values for environment variables."""
    if sys.platform == 'darwin':
        tail = 'i386-darwin'
    elif sys.platform == 'linux':
        tail = 'x86_64-linux-gnu'
    else:
        raise ValueError(
            'unexpected operating system: '
            f'{sys.platform = }')
    prefix = f'tlaps-{tlapm_version}-{tail}'
    installer = f'{prefix}-inst.bin'
    downloads = f'{prefix}/download'
    return dict(
        TLAPM_VERSION=tlapm_version,
        INSTALLER=installer,
        DOWNLOADS=downloads)


def _make_shell_definitions(kv: dict) -> str:
    """Return assignments to shell variables.

    For example, given the argument
    `kv=dict(NAME='value')`,
    returns the string`"NAME='value'"`.
    """
    any_blanks = any(map(
        _contains_blanks,
        kv.values()))
    if any_blanks:
        raise ValueError(kv)
    return '\n'.join(
        f'{name}={value}'
        for name, value in kv.items())


def _contains_blanks(value: str) -> bool:
    """Return `True` if blankspace in `value`."""
    value_ = ''.join(value.split())
    return len(value) != len(value_)


if __name__ == '__main__':
    _main()
