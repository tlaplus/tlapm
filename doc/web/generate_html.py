"""Read Markdown files and create HTML files from them.

Traverses the directory tree rooted in the directory `ROOT_DIR`.
For all Markdown files encountered during this traversal,
those files that are known to this script are converted to
HTML. Any known files that are not found raise an exception
after conversion of all found files has been completed.

The conversion is performed by reading the Markdown source,
determining whether it is a redirection page or not,
and if it is, then append only a suitable HTML footer,
otherwise append both a suitable HTML header, and a suitable
HTML footer. The resulting Markdown with footer and header is
then passed to `PANDOC`, which converts it to HTML.

The program with name stored in the constant `PANDOC` (below)
is expected to be available in the runtime environment's `PATH`.

The names of the generated HTML files differ from the
corresponding Markdown sources only in their extension.
"""
import os
import pprint
import subprocess
import sys

import assets.header


ROOT_DIR = 'content/'
MARKDOWN_SOURCES = [
    # the below listing is lexicographic,
    # as when browsing files
    # `content/`
    'content/community.md',
    'content/documentation.md',
    'content/download.md',
    'content/home.md',
    # `content/community/`
    'content/community/contact.md',
    'content/community/developers.md',
    'content/community/tla+_net.md',
    # `content/documentation/`
    'content/documentation/misc.md',
    'content/documentation/publications.md',
    'content/documentation/tla+_hyperbook.md',
    'content/documentation/tla+_video_course.md',
    'content/documentation/tutorial.md',
    'content/documentation/unsupported_features.md',
    # `content/documentation/tutorial/`
    'content/documentation/tutorial/a_simple_proof.md',
    'content/documentation/tutorial/advanced_options.md',
    'content/documentation/tutorial/hierarchical_proofs.md',
    'content/documentation/tutorial/other_proof_constructs.md',
    'content/documentation/tutorial/practical_hints.md',
    'content/documentation/tutorial/tactics.md',
    'content/documentation/tutorial/the_example.md',
    # `content/download/`
    'content/download/binaries.md',
    'content/download/license.md',
    'content/download/previous_releases.md',
    'content/download/source.md',
    'content/download/unsupported.md',
    'content/download/what_s_new.md',
    # `content/download/binaries/`
    'content/download/binaries/linux.md',
    'content/download/binaries/macos.md',
    'content/download/binaries/windows.md',
]
PANDOC = 'pandoc'
# the templates for the below HTML strings are in the files:
# `doc/web/assets/template-redirect.html`
# `doc/web/assets/template.html`
CONTENT_PAGE_HEADER = (
r'''<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN"
"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en-US" lang="en-US">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=utf-8" />
<link
rel="stylesheet" type="text/css"
id="ss"
href="{path_to_assets_root}assets/css/common.css"
/>
<title>TLA+ Proof System</title>
</head>
<body>
''')
CONTENT_PAGE_FOOTER = '''
    </div>
  </div>
</div>

</script>
</body>
</html>
'''
REDIRECT_PAGE_FOOTER = '''
</body>
</html>
'''


def _main():
    """Entry point."""
    _check_python_version()
    markdown_sources = list(MARKDOWN_SOURCES)
    unknown_markdown_files = list()
    for root, dirs, files in os.walk(ROOT_DIR):
        for name in files:
            path = os.path.join(root, name)
            r = _convert_file_to_html(
                path, markdown_sources)
            if r == 'success':
                markdown_sources.remove(path)
            elif r == 'unknown':
                unknown_markdown_files.append(path)
            else:
                assert r is None, r
    if unknown_markdown_files:
        s = pprint.pformat(unknown_markdown_files)
        print(f'Found unknown Markdown files:\n{s}')
    if not markdown_sources:
        return
    s = pprint.pformat(s=markdown_sources)
    raise FileNotFoundError(
        'Expected to find the following '
        f'Markdown files too:\n{s}')


def _convert_file_to_html(
        path:
            str,
        markdown_sources:
            list[str]
            ) -> str:
    """Read Markdown file at `path`, and convert to HTML file.

    - if `path` is not a Markdown file, return `None`
    - if `path` is not in `markdown_sources`,
      do not convert it, and return `'unknown'`
    - otherwise, convert the file, and return `'success'`
    """
    _, ext = os.path.splitext(path)
    if ext != '.md':
        return
    if path not in markdown_sources:
        print(f'skipping unknown Markdown file `{path}`')
        return 'unknown'
    print(f'processing file:  {path}')
    with open(path, 'rt') as f:
        md_src = f.read()
    _convert_source_to_html(md_src, path)
    return 'success'


def _convert_source_to_html(
        md_src:
            str,
        md_path:
            str
            ) -> str:
    """Convert Markdown `md_src` to HTML, dump to file.

    The path to the HTML file to be created is
    obtained from `md_path` by replacing the
    extension `'.md'` with `'.html'`.

    @param md_src:
        Markdown source
    @param md_path:
        path to Markdown source file
    """
    assert os.extsep == '.', os.extsep
    basepath, ext = os.path.splitext(md_path)
    assert ext == '.md', ext
    if '<title>Redirection</title>' in md_src:
        html_src = _convert_redirection_page_to_html(md_src)
    else:
        html_src = _convert_content_page_to_html(
            md_src, basepath)
    html_path = f'{basepath}.html'
    with open(html_path, 'wt') as f:
        f.write(html_src)


def _convert_redirection_page_to_html(md_src) -> str:
    """Return HTML from converting Markdown `md_src`.

    This function appends the HTML footer for
    redirection webpages.
    """
    html = _convert_md_to_html(md_src)
    return html + REDIRECT_PAGE_FOOTER


def _convert_content_page_to_html(
        md_src:
            str,
        basepath:
            str
            ) -> str:
    """Return HTML from converting Markdown `md_src`.

    This function prepends the HTML header and
    appends the HTML footer for redirection webpages.
    """
    depth = basepath.count('/')
    root_path = '../' * depth
    html = _convert_md_to_html(md_src)
    html = assets.header.colorize_tla_blocks(html)
    menu = assets.header.make_menu(f'{basepath}.html')
    header = CONTENT_PAGE_HEADER.format(
        path_to_assets_root=root_path)
    return '\n'.join([
        header,
        menu,
        html,
        CONTENT_PAGE_FOOTER])


def _convert_md_to_html(
        md_src:
            str
            ) -> str:
    """Return HTML resulting from `md_src` via `PANDOC`."""
    cmd = [PANDOC, '-f', 'gfm', '-t', 'html']
    proc = subprocess.Popen(
        cmd,
        text=True,
        stdin=subprocess.PIPE,
        stderr=subprocess.PIPE,
        stdout=subprocess.PIPE)
    stdout_text, stderr_text = proc.communicate(
        input=md_src)
    returncode = proc.wait()
    if returncode == 0:
        return stdout_text
    raise RuntimeError(
        f'`{PANDOC}` returned exit code:  {returncode}\n'
        f'and stdout:\n{stdout_text}\n'
        f'and stderr:\n{stderr_text}')


def _check_python_version():
    """Raise `RuntimeError` if running on Python < 3.7."""
    if sys.version_info.major > 3:
        return
    if (sys.version_info.major == 3 and
            sys.version_info.minor >= 7):
        return
    raise RuntimeError(
        'This script requires Python >= 3.7')


if __name__ == '__main__':
    _main()
