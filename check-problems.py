#!/usr/bin/env python3

# encoding: utf-8

# This script is a quick hack to check a collection of problems for things like
# the following:
#
# - problem names are not used already in Kattis
# - metadata:
#     - consistent sources
#     - consistent source_url
#     - not too many defaults changed
# - problem statement
#     - width of images should be specified with something like \includegraphics[width=0.5\textwidth]...
#     - problem statement images should be small
#     - numbers should be in math mode
#     - numbers in math mode should use "\," as thousands separators
#     - words should be spelled correctly
#     - problem name should be close to title

# An explanation of the possible warnings (suitable for github issues):
#
# * `bad includegraphics width` -- Kattis uses plasTeX for rendering into HTML, which usually does best when using `\includegraphics[width=x\textwidth]`, for some x between 0.1 and 0.9 (but not blank)
# * `difference in name and title` -- the problem title and directory name should match
# * `has no TLE submissions` -- while having TLE submissions is not necessary, it is encouraged, especially on problems where there may be a suboptimal solution strategy that should be prevented
# * `has no WA submissions` -- while having TLE submissions is not necessary, it is encouraged, especially on problems where there may be an incorrect solution strategy that should be prevented
# * `has only one AC submission` -- having multiple AC submissions, from multiple authors, helps ensure robustness
# * `image is large (X kB)` -- large images are usually not necessary and can slow down web performance
# * `incorrect math: [...]` -- use "\," to separate thousands groups for numbers in math mode
# * `mentions floating-point rather than real number` -- use the mathematical concept (real number) to describe values, not the programming concept (floating-point)
# * `missing math mode: [...]` -- put all numbers in LaTeX math mode (except possibly dates and strings that are composed of digits)
# * `misspelled words: [...]` -- should be clear what this means
# * `specifies default value for X` -- in problem.yaml, try only to specify those things which should be non-defaults. The more specification is given, the less "future-proof" a problem may be (e.g. the defaults may change in the future).
# * `specifying unusual value X` -- in problem.yaml, specifying a field that is not commonly used; be careful
# * `there are no "slow" accepted submissions (only: C++)` -- the time limit is based on the slowest accepted submission; thus it is good to have accepted submissions in slower languages
# * `uses \times; use \cdot instead` -- preference of Kattis style
# * `uses double-quotes` -- standard LaTeX: use one or two single backticks (`) to begin a quote, and one or two single quotes (') to end a quote
# * `uses future tense ("will")` -- preference of Kattis style; use present tense and active voice wherever possible
# * `uses three periods rather than \ldots` -- standard LaTeX: use \ldots instead of "..."

import argparse
import collections
import datetime
import glob
import io
import os.path
import pathlib
import re
import subprocess
import sys
import traceback
import yaml

def try_importing(module):
    '''Load the non-standard modules that we can load into the global namespace,
    without dying.'''

    # if the module has multiple parts, load each separately
    parts = module.split('.')
    for i in range(len(parts)):
        name = '.'.join(parts[:i+1])
        try:
            globals()[name] = __import__(name)
        except ModuleNotFoundError:
            print(f'could not import module {name} (while loading {module})')
            # if we cannot load a parent module, we won't be able to load the
            # children either
            break

try_importing('kattis.util.db')
try_importing('plasTeX.TeX')
try_importing('plasTeX.Logging')
try_importing('problemtools.verifyproblem')

# globals, yuck
_SPELLING_DICTIONARIES = {}
_ERRORS = {}

################################################################
# code for logging warnings and errors

def _log(dest, key, message):
    """General-purpose logging function."""
    if key not in dest:
        dest[key] = []
    dest[key].append(message)

warning = lambda key, message: _log(_ERRORS, key, message)
error = lambda key, message: _log(_ERRORS, key, message)

def _check_problem_name_uniqueness(problems, cache_filename=None):
    """Check that all the names are not already used in Kattis."""

    kattis_names = None

    if 'kattis.util.db' in sys.modules:
        # TODO: don't depend on the Kattis database; use a REST endpoint
        with kattis.util.db.db_admin_txn() as conn:
            cursor = conn.cursor()
            cursor.execute('SELECT problem_name FROM problem')
            kattis_names = {p for [p] in cursor}
    elif cache_filename is not None:
        with open(cache_filename) as names:
            kattis_names = set(map(str.strip, names))

    if not kattis_names:
        error('_general_', 'could not check whether problem names are already used in Kattis')
        return

    non_unique = sorted(set(problems) & kattis_names)

    if non_unique:
        error('_general_', f'some problems use names already in Kattis: {non_unique}')

def display_warnings_errors():
    p = subprocess.run(['git', 'rev-parse', '--short', 'HEAD'], capture_output=True)
    git_hash = p.stdout.strip().decode('utf-8')

    sep = '-' if git_hash else ''
    logfile_fmt = f'problem-check-log-%Y%m%d-%H%M%S{sep}{git_hash}.txt'
    logfilename = datetime.datetime.now().strftime(logfile_fmt)

    last_prefix = None
    with open(logfilename, 'w') as out:

        def _write(x):
            print(x)
            out.write(x + '\n')

        _write(f'logfile is {logfilename}, working directory is {os.getcwd()}, git hash is "{git_hash}"\n')

        for k in sorted(set(_ERRORS.keys())):
            prefix = k.split('/')[0]
            if last_prefix != prefix:
                last_prefix = prefix
                _write(f'\n* {prefix}')
            for e in _ERRORS.get(k, []):
                _write(f'    * [ ] {k}: {e}')

################################################################

def find_problem_directories(wd='.'):
    """Walk through the given directory looking for problem packages (signified
    by the presence of problem.yaml)."""
    problem_names = []
    for root, dirs, files in os.walk(wd, followlinks=True):
        if 'problem.yaml' in files:
            problem_names.append(os.path.basename(root))
        if root != wd:
            del dirs[:] # don't descend further
    return sorted(problem_names)

################################################################
# checks involving metadata and names


def _check_problem_name_title(name, title):
    """Check that the problem_name and title seem to match."""
    short_title = re.sub('[^a-zA-Z0-9]', '', title).lower()
    if name != short_title:
        warning(name, f'use matching directory name and title: {name} "{title}"')

# If people are setting these values, investigate...
_WARN_ABOUT_SETTINGS = {
        'validation',
        'type',
        'limits/memory',
        'limits/output',
        'limits/compilation_time',
        'limits/validation_time',
        'limits/validation_memory',
        'limits/validation_output',
        }

def _check_metadata_recursive(problem, data, default, path=None):
    path = path or ''

    problem_yaml = problem + '/problem.yaml'

    if data is None:
        error(problem_yaml, 'there is no metadata')
        return

    for k in data:
        full_key = path + ('/' if path else '') + k
        if full_key in _WARN_ABOUT_SETTINGS:
            warning(problem_yaml, f'specifying unusual metadata value {full_key}')

        if k not in default:
            error(problem_yaml, f'option {full_key} is not in default')
        elif type(data[k]) == dict:
            _check_metadata_recursive(problem, data[k], default[k], full_key)

################################################################
# checks involving the problem statement

def _check_statement(problem):
    """Check for several things that often go wrong in problem statements."""

    s = lambda p: re.compile(r'^[^%]*' + p, re.I | re.U).search
    _regex_checks = [
        (s(r'"'), 'uses double-quotes; use two single-quotes instead'),
        (s(r'\\includegraphics(?!\[width=[0-9.]+\\(textwidth|linewidth)\])'), 'bad includegraphics width; use a multiplier (e.g. width=0.9\\textwidth) or HTML layout can break'),
        (s(r'\.\.\.'), 'use \\ldots rather than three periods'),
        (s(r'floating[- ]*point'), 'use "real" rather than "floating-point"'),
        (s(r'\\times\b'), 'use \\cdot instead of \\times for multiplication'),
    ]

    for filename in glob.glob(os.path.join(problem, 'problem_statement', 'problem*.tex')):
        m = re.match(r'.*problem(?:\.([a-z][a-z]))?.tex$', filename)
        if not m:
            continue
        language = m.group(1) or 'en'

        spelling_dictionary = _SPELLING_DICTIONARIES.get(language)
        if spelling_dictionary is not None:
            spelling_dictionary |= _SPELLING_DICTIONARIES.get('global', set())

        _parse_for_tex_errors(problem, filename, spelling_dictionary)

        with open(filename) as filedata:
           lines = filedata.readlines()
           for search, msg in _regex_checks:
               if any(map(search, lines)):
                   warning(filename, msg)


def _parse_for_tex_errors(problem, filename, spelling_dictionary):
    """Use the plasTeX parser to iterate over the problem statement and look for
    issues like:
        - misspelled words (if spelling_dictionary is not None)
        - numbers not in math mode
        - numbers in math mode not formatted correctly
    """

    if 'plasTeX.TeX' not in sys.modules:
        error(problem, 'could not load plasTeX for parsing problem description')
        return

    misspelled_words = set()
    incorrect_math = set()
    missing_math_mode = set()

    # in non-math mode, look for words as things that begin and end with a word
    # character and have no spaces
    plain_text_word_re = re.compile(r"\b\w([^\s]*\w)?\b", re.U)
    missing_math_mode_re = re.compile(r"^[0-9.,]+", re.U)
    incorrect_math_re = re.compile(r"\b([0-9]+[0-9,]*,[0-9]+|[0-9]{4,})\b", re.U)

    def _check_plain_text(text):
        words = {m.group(0) for m in plain_text_word_re.finditer(text)}
        if spelling_dictionary:
            for word in words - spelling_dictionary:
                if missing_math_mode_re.match(word):
                    missing_math_mode.add(word)
                else:
                    misspelled_words.add(word)

    def _check_math_text(text):
        for word in incorrect_math_re.finditer(text):
            incorrect_math.add(word.group(0))

    def _dfs(node, plain_text, math_text, path=None, in_math=None):
        path = path or []
        path.append(node)
        in_math = in_math or False

        is_plain_text = isinstance(node, plasTeX.DOM.Text)
        text = node.lower() if is_plain_text else (node.nodeName + ' ')

       # for debugging latex parsing issues
       #print('{indent} {nodeType} {in_math} {is_plain_text} "{nodeRepr}" "{nodeName}"'.format(
       #            indent='  ' * len(path),
       #            nodeType=type(node),
       #            in_math=in_math,
       #            is_plain_text=is_plain_text,
       #            nodeRepr=repr(node),
       #            nodeName=repr(node.nodeName)
       #            )
       #        )

        if in_math:
            math_text.append(text)
        elif is_plain_text:
            plain_text.append(text)
        elif node.nodeName == 'bgroup':
            # add spaces between groups, so that they are separated later when
            # we join the tokens
            plain_text.append(' ')
            math_text.append(' ')
        elif node.nodeName == 'math':
            math_text.append(' ')
            in_math = True

        for child in node.childNodes:
            _dfs(child, plain_text, math_text, path, in_math)

        path.pop()

    try:
        tex = plasTeX.TeX.TeX(myfile=filename)
        plasTeX.Logging.disableLogging()
        document = tex.parse()
        #print(document)
    except Exception as e:
        warning(filename, 'could not parse tex', e)
        return

    plain_text = []
    math_text = []

    _dfs(document, plain_text, math_text)
    _check_plain_text(''.join(plain_text))
    _check_math_text(''.join(math_text))

    if misspelled_words:
        warning(filename, f'misspelled words: {sorted(misspelled_words)}')
    if incorrect_math:
        warning(filename, f"incorrect math: {sorted(incorrect_math)} (use `\\,` (backslash comma) to separate thousands groups)")
    if missing_math_mode:
        warning(filename, f'missing math mode: {sorted(missing_math_mode)}')

def _check_metadata(problem):
    """Load the metadata for the given problem and compare its keys and values
        to the default set, and look for unusual settings."""
    full_metadata = problem.config._data
    with open(problem.config.configfile) as f:
        specified_metadata = yaml.safe_load(f)

    n = full_metadata['name']
    title = n.get('en', list(n.values())[0])
    _check_problem_name_title(problem.shortname, title)

    defaults = problemtools.verifyproblem.ProblemConfig._OPTIONAL_CONFIG
    for f in problemtools.verifyproblem.ProblemConfig._MANDATORY_CONFIG:
        defaults[f] = None
    _check_metadata_recursive(problem.shortname, specified_metadata, defaults)

    return full_metadata

def _check_large_images(problem):
    """Warn if there are large images in the problem_statement directory."""
    for filename in glob.glob(os.path.join(problem, 'problem_statement', '*')):
        if filename.endswith(('.jpg', '.jpeg', '.png', '.pdf', '.svg')):
            s = os.stat(filename)
            if 1024 * 200 < s.st_size:
                warning(filename, f'image is large ({s.st_size // 1024} kB) -- try to keep images under 200kB')

def _check_submissions(problem):
    """Warn if there is not a suitably-robust set of submissions."""
    languages_in_accepted = set()
    has_wa = has_tle = False
    num_accepted = 0
    for sub_type in problem.submissions._submissions:
        for s in problem.submissions._submissions[sub_type]:
            has_wa |= (sub_type == 'WA')
            has_tle |= (sub_type == 'TLE')
            if sub_type == 'AC':
                languages_in_accepted.add(s.language.name)
            num_accepted += (sub_type == 'AC')

    if not has_wa:
        warning(problem.shortname, 'has no WA submissions')
    if not has_tle:
        warning(problem.shortname, 'has no TLE submissions')
    if num_accepted == 1:
        warning(problem.shortname, 'has only one AC submission')

    fast_pattern = re.compile(r'\bC(\+\+)?\b')
    has_slow = False
    for lang in languages_in_accepted:
        if not fast_pattern.match(lang):
            has_slow = True
    if not has_slow:
        warning(problem.shortname, f'there are no "slow" accepted submissions (only: {", ".join(languages_in_accepted)})')

def _check_problem(problem):

    if 'problemtools.verifyproblem' not in sys.modules:
        error(problem, 'could not load problemtools')
        return {}

    with problemtools.verifyproblem.Problem(problem) as p:
        full_metadata = _check_metadata(p)
        _check_submissions(p)

    _check_statement(problem)

    _check_large_images(problem)

    return full_metadata

################################################################
# main code for checking everything

def check_problems(problems, problem_name_cache=None):
    """Go through the list of problem names and check each one; then compare
    metadata across problems for consistency."""
    _check_problem_name_uniqueness(problems, problem_name_cache)

    metadata = {}
    errors = []
    for p in problems:
        try:
            metadata[p] = _check_problem(p)
        except:
            errors.append(p)
            error(p, f'an exception occurred when checking this problem: {traceback.format_exc()}')

    for k in ['source', 'source_url', 'license']:
        try:
            values = dict(collections.Counter(metadata[p][k] for p in problems if p not in errors))
            if 1 < len(values):
                warning('_general_', f'multiple values for {k}: {values}')
        except:
            warning('_general_', f'could not check for consistency of metadata field {k}')

def load_spelling_dictionaries(root):
    global _SPELLING_DICTIONARIES
    for path, dirs, files in os.walk(root, followlinks=True):
        if path == root:
            continue

        language = os.path.basename(path)
        if language not in _SPELLING_DICTIONARIES:
            _SPELLING_DICTIONARIES[language] = set()

        for filename in files:
            with io.open(os.path.join(path, filename)) as words:
                _SPELLING_DICTIONARIES[language] |= {line.strip().lower() for line in words}

            print(f'loaded dictionary {filename} for {language}')

def main():
    p = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    p.add_argument('problems', metavar='problem', nargs='*', default=[],
            help='one or more problems to check (directory names)')
    p.add_argument('--problem-name-cache',
            help='file containing a cache of existing problem names used in Kattis, one per line')
    p.add_argument('--dictionaries',
            default=os.path.join(pathlib.Path.home(), 'etc', 'dictionaries'),
            help='directory containing dictionaries for spell checking, one per language')
    args = p.parse_args()

    load_spelling_dictionaries(args.dictionaries)

    if args.problems:
        problem_names = args.problems
    else:
        problem_names = find_problem_directories()

    check_problems(problem_names, args.problem_name_cache)

    display_warnings_errors()


if __name__ == '__main__':
    main()

