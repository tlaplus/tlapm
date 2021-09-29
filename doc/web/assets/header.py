"""Generate headers of HTML pages of TLAPS website.

To use, update `BASE_URL`, `URL`, and `menumap`.
"""
import argparse
import os
import re


# The menu hierarchy.
# Spaces at the beginning of the strings
# give the nesting level.
# The corresponding file/directory names
# are the same with prefixed spaces
# removed, all special characters replaced
# by underscores, and `.html`
# added at the end of file names
# (but not directories).
#
# Special characters are all characters
# except letters, digits, `-`, and `+`
#
# For the moment, the depth is limited to
# 3 levels: 0, 1, or 2 spaces.
MENUMAP = [
    'Home',
    'Download',
    ' Binaries',
    '  Windows',
    '  Linux',
    '  MacOS',
    ' Source',
    " What's new",
    ' Unsupported',
    ' License',
    ' Previous releases',
    'Documentation',
    ' Tutorial',
    '  The example',
    '  A simple proof',
    '  Hierarchical proofs',
    '  Advanced options',
    '  Other proof constructs',
    '  Tactics',
    '  Practical hints',
    ' Unsupported features',
    ' Publications',
    ' TLA+ Hyperbook',
    ' TLA+ Video Course',
    ' Misc',
    'Community',
    ' Contact',
    ' Developers',
    ' TLA+.net']
# order of decreasing length guarantees
# that any word that is a substring of
# another will appear after it.
tla_keywords = [
    'PROPOSITION',
    'ASSUMPTION',
    'CONSTANTS',
    'RECURSIVE',
    'UNCHANGED',
    'VARIABLES',
    'CONSTANT',
    'INSTANCE',
    'SUFFICES',
    'TEMPORAL',
    'VARIABLE',
    'ENABLED',
    'EXTENDS',
    'OBVIOUS',
    'OMITTED',
    'THEOREM',
    'WITNESS',
    'ACTION',
    'ASSUME',
    'CHOOSE',
    'DEFINE',
    'DOMAIN',
    'EXCEPT',
    'LAMBDA',
    'MODULE',
    'SUBSET',
    'AXIOM',
    'LEMMA',
    'LOCAL',
    'OTHER',
    'PROOF',
    'PROVE',
    'STATE',
    'UNION',
    'CASE',
    'DEFS',
    'ELSE',
    'HAVE',
    'HIDE',
    'ONLY',
    'PICK',
    'TAKE',
    'THEN',
    'WITH',
    'DEF',
    'LET',
    'NEW',
    'QED',
    'SF_',
    'USE',
    'WF_',
    'BY',
    'IF',
    'IN']
tla_keywords = sorted(
    tla_keywords,
    key=len,
    reverse=True)
LOGO_IMG = (
    'logo-MS-Research-Inria-Joint-Centre-Small.png')
TEMPLATE_1 = f'''
<div id="wrapper">
  <div id="header">
    <div id="title">
      <a class="title"
        href="{{base}}Home.html">
            TLA+ Proof System
      </a>
    </div>
    <div class="logomsr">
      <a href="https://www.msr-inria.inria.fr">
        <img
            src="{{base}}../assets/images/{LOGO_IMG}"
            alt="Microsoft Research - Inria Joint Centre"
            class="logo"
        />
      </a>
    </div>
  </div>
  <ul id="nav">
'''
TEMPLATE_2 = '''
</ul>
<div id="transp"></div>
<div id="content" class="clearfix">
  <div id="col_1">
'''
TEMPLATE_3 = '''
</ul>
</div>
<div id="col_2">
'''


def make_menu(
        filepath:
            str
            ) -> str:
    """Return HTML for the menu.

    @param filepath:
        path to HTML file of webpage
    """
    base = _make_relative_path_to_content_dir(filepath)
    _, path = filepath.split('content/')
    path = [p for p in path.split('/') if p]
    branch = _find_branch(0, 0, path)
    out = list()
    out.append(TEMPLATE_1.format(base=base))
    for i, item in enumerate(branch[0]):
        on_ = _on('', 0, i, path, branch)
        out.append(
            f'''
            <li>
                <a{on_}
                    href="{base}{_file(item)}.html">
                    {item}
                </a>
            </li>
            ''')
    out.append(TEMPLATE_2)
    if branch[1]:
        menu = '      <h2>Menu</h2>'
    else:
        menu = '      <h2 class="white">Menu</h2>'
    out.append(menu)
    out.append('      <ul id="menu">')
    for i, item in enumerate(branch[1]):
        on_menu = _on('menu', 1, i, path, branch)
        html_path = (
            f'{base}{_file(path[0])}/'
            f'{_file(item)}.html')
        out.append(
            f'''
            <li{on_menu}>
                <a
                    href="{html_path}">
                    {item}
                </a>
            </li>
            ''')
        if path[1].lower() != _file(item).lower():
            continue
        for k, title in enumerate(branch[2]):
            on_index = _on(
                'index', 2, k, path, branch)
            html_path = (
                f'{base}{_file(path[0])}/'
                f'{_file(path[1])}/'
                f'{_file(title)}.html')
            out.append(
                f'''
                <li{on_index}>
                    <a
                        href="{html_path}">
                        {title}
                    </a>
                </li>
                ''')
    out.append(TEMPLATE_3)
    return '\n'.join(out)


def _make_relative_path_to_content_dir(
        filepath):
    """Return path to `context/` directory.

    The returned path is a relative path that
    points to the directory `content/`.
    """
    if filepath.count('content') != 1:
        raise ValueError(
            '`"content"` should occur once '
            'as a substring of `filepath`, '
            f'which is `{filepath}`')
    filepath = os.path.normpath(filepath)
    if '\\' in filepath:
        raise ValueError(
            '`filepath` must not contain '
            f'backslashes: {filepath = }')
    _, tail = filepath.split('content/')
    return '../' * tail.count('/')


def _find_branch(
        index,
        level,
        path):
    """Parse the MENUMAP `list` and find
    the current branch within it.
    Fill the array `branch` with the
    other nodes that are successors of
    the ancestor of the current node:
    `branch[lvl][k]` is the
    `k`-th successor of the `lvl - 1`
    ancestor of the current node.

    @param index:
        current position in
        the list `MENUMAP`
    @param level:
        current level being filled
    @return:
        next position in array `MENUMAP`
    """
    branch = [[], [], []]
    _find_branch_recurse(
        index, level, path, branch)
    return branch


def _find_branch_recurse(
        index,
        level,
        path,
        branch):
    while index < len(MENUMAP):
        item = MENUMAP[index]
        level_of_index = _get_level(item)
        if level_of_index < level:
            return index
        elif level_of_index == level:
            menu_item = MENUMAP[index].lstrip()
            branch[level].append(menu_item)
            if menu_item.lower() == path[level]:
                index = _find_branch_recurse(
                    index + 1,
                    level + 1,
                    path,
                    branch)
            else:
                index += 1
        else:
            index += 1
    return index


def _get_level(
        string:
            str
            ) -> int:
    """Return number of spaces at start of `string`."""
    return len(string) - len(string.lstrip(' '))


def _on(
        prefix,
        depth,
        index,
        path,
        branch):
    """Return annotation for HTML element."""
    if path[depth] == _file(branch[depth][index]):
        return f' class="{prefix}on"'
    else:
        return f' class="{prefix}off"'


def _file(
        title):
    """Return filename associated with `title`."""
    return re.sub('[^-a-zA-Z0-9+]', '_', title)


def colorize_tla_blocks(
        html):
    """Return HTML with TLA+ elements in color.

    The syntactical elements that are colorized
    are TLA+ keywords and comments.

    Assumes that within `html`, lines of TLA+
    are between `<pre class="tla"><code>` and
    `</code></pre>`.
    """
    opening = '<pre class="tla"><code>'
    closing = '</code></pre>'
    if opening not in html:
        return html
    pieces = html.split(opening)
    head, *tail = pieces
    out = [head]
    for piece in tail:
        if '</code></pre>' not in piece:
            raise ValueError(
                f'Unmatched `{opening}` '
                f'in HTML: no matching `{closing}` '
                f'found in: {piece}')
        tla, *rest = piece.split(closing)
        tla = _colorize_tla(tla)
        out.extend((opening, tla, closing))
        out.extend(rest)
    return ''.join(out)


def _colorize_tla(
        tla_text:
            str
            ) -> str:
    """Color TLA+ keywords and comments."""
    # multiline comments
    tla_text = re.sub(
        r' \( \* ',
        '<span class="comment">(*',
        tla_text,
        flags=re.VERBOSE)
    tla_text = re.sub(
        r' \* \) ',
        '*)</span>',
        tla_text,
        flags=re.VERBOSE)
    # trailing comments
    tla_text = re.sub(
        r' (\\ \* .*) \n ',
        r'<span class="comment">\1</span>\n',
        tla_text,
        flags=re.VERBOSE)
    # TLA+ keywords
    for keyword in tla_keywords:
        if keyword.strip() != keyword:
            raise AssertionError(
                'keyword contains blankspace: '
                f'`{keyword}`')
        tla_text = re.sub(
            keyword,
            '<span class="purple">'
            f'{keyword}</span>',
            tla_text,
            flags=re.VERBOSE)
    return tla_text
