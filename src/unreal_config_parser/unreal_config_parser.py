"""Custom ConfigParser class to parse UE5 config files.
You can sort and reformat them while preserving comments in file and Array keys order."""
from __future__ import annotations

from collections import OrderedDict
from collections.abc import Iterable
from configparser import (
    RawConfigParser,
    DuplicateSectionError,
    SectionProxy,
    MissingSectionHeaderError,
    DuplicateOptionError,
    DEFAULTSECT,
    _UNSET,
)
from io import StringIO
from typing import TYPE_CHECKING
import itertools
import os
import re
import sys

if TYPE_CHECKING:
    from _typeshed import StrOrBytesPath
    from _typeshed import SupportsWrite

__all__ = ["UnrealConfigParser"]

COMMENT_PTN = re.compile(r"^\s*[#|;]\s*(.*)\s*")
SECTION_PTN = re.compile(r"^\s*\[(.+)\]\s*$")


# Ordered Dict that allow duplicates on !+-. keys, transform them to list
class UnrealConfigMultiOrderedDict(OrderedDict):
    def __setitem__(self, key, value):
        # We only want duplicate on array operators
        if (
            UnrealConfigParser.is_special_key(key)
            and isinstance(value, list)
            and key in self
        ):
            self[key].extend(value)
        else:
            super().__setitem__(key, value)


# try to sort keys in a natural way for human.
# e.g: a2, a12, aa, aaa, Aaa, aaaaaaaaa, aba, aBa, bb, bbb, Bbb
# - split the strings into segments of numbers and non-numbers.
# - compare the segments individually, in a case-insensitive way or as number.
def natural_sort_key(key):
    def convert(segment):
        if segment.isdigit():
            return int(segment)
        else:
            return segment.casefold(), segment.swapcase()

    segments = re.findall(r"(\d+|\D+)", key)
    return [convert(segment) for segment in segments]


class UnrealConfigParser(RawConfigParser):
    """Custom ConfigParser that preserves comments when writing a loaded config out."""

    # --- Overriding RawConfigParser function to support Unreal config array operators ---

    SPECIAL_KEYS = (
        ";;;;;;"  # key content doesn't matter as long as it can't be an ini key
    )
    _OPT_TMPL = r"""
        ^\s*(?P<option>[^\s]+?)                    # very permissive!
        \s*(?P<vi>{delim})\s*              # any number of space/tab,
                                           # followed by any of the
                                           # allowed delimiters,
                                           # followed by any space/tab
        (?P<value>.*)$                     # everything up to eol
        """
    _OPT_NV_TMPL = r"""
        ^\s*(?P<option>[^\s]+?)                    # very permissive!
        \s*(?:                             # any number of space/tab,
        (?P<vi>{delim})\s*                 # optionally followed by
                                           # any of the allowed
                                           # delimiters, followed by any
                                           # space/tab
        (?P<value>.*))?$                   # everything up to eol
        """

    def __init__(
        self,
        defaults=None,
        dict_type=UnrealConfigMultiOrderedDict,
        allow_no_value=True,
        *,
        delimiters=("="),
        comment_prefixes=("#", ";"),
        inline_comment_prefixes=None,
        strict=False,
        empty_lines_in_values=True,
        default_section=DEFAULTSECT,
        interpolation=_UNSET,
        converters=_UNSET,
    ):
        super().__init__(
            defaults=defaults,
            dict_type=dict_type,
            allow_no_value=allow_no_value,
            delimiters=delimiters,
            comment_prefixes=comment_prefixes,
            inline_comment_prefixes=inline_comment_prefixes,
            strict=strict,
            empty_lines_in_values=empty_lines_in_values,
            default_section=default_section,
            interpolation=interpolation,
            converters=converters,
        )

    def sort(self):
        unsorted_sections = dict(self._sections)

        sections = sorted(self._sections, key=natural_sort_key)
        self.clear()
        for s in sections:
            self.add_section(s)

            items = sorted(
                unsorted_sections[s].items(),
                key=lambda key_value: natural_sort_key(key_value[0]),
            )

            for i in items:
                self.set(s, i[0], i[1])

    # override to preserve case
    def optionxform(self, optionstr):
        return optionstr

    @staticmethod
    def is_special_key(key):
        special_key_regex = re.compile(r"[!+-.][^!+-.].*")
        return re.match(special_key_regex, key) is not None

    def _write_section(self, fp, section_name, section_items, delimiter):
        """Write a single section to the specified `fp`."""
        fp.write("[{}]\n".format(section_name))
        for key, value in section_items:
            # CORVUS_BEGIN support for Unreal config array operators
            if key == self.SPECIAL_KEYS:
                continue
            # CORVUS_END
            value = self._interpolation.before_write(self, section_name, key, value)
            if value is not None or not self._allow_no_value:
                value = delimiter + str(value).replace("\n", "\n\t")
            else:
                value = ""
            fp.write("{}{}\n".format(key, value))

        # CORVUS_BEGIN support for Unreal config array operators

        # Always write special keys (list +-.!) at the end of section.
        for key, value in section_items:
            if key == self.SPECIAL_KEYS:
                for array_key_value in sorted(value.items()):
                    for special_key, special_value in array_key_value[1]:
                        fp.write(f"{special_key}{delimiter}{special_value}\n")
        # CORVUS_END
        fp.write("\n")

    def _read(self, fp, fpname):
        """Parse a sectioned configuration file.

        Each section in a configuration file contains a header, indicated by
        a name in square brackets (`[]'), plus key/value options, indicated by
        `name' and `value' delimited with a specific substring (`=' or `:' by
        default).

        Values can span multiple lines, as long as they are indented deeper
        than the first line of the value. Depending on the parser's mode, blank
        lines may be treated as parts of multiline values or ignored.

        Configuration files may include comments, prefixed by specific
        characters (`#' and `;' by default). Comments may appear on their own
        in an otherwise empty line or may be entered in lines holding values or
        section names. Please note that comments get stripped off when reading configuration files.
        """
        elements_added = set()
        cursect = None  # None, or a dictionary
        sectname = None
        optname = None
        lineno = 0
        indent_level = 0
        e = None  # None, or an exception
        for lineno, line in enumerate(fp, start=1):
            comment_start = sys.maxsize
            # strip inline comments
            inline_prefixes = {p: -1 for p in self._inline_comment_prefixes}
            while comment_start == sys.maxsize and inline_prefixes:
                next_prefixes = {}
                for prefix, index in inline_prefixes.items():
                    index = line.find(prefix, index + 1)
                    if index == -1:
                        continue
                    next_prefixes[prefix] = index
                    if index == 0 or (index > 0 and line[index - 1].isspace()):
                        comment_start = min(comment_start, index)
                inline_prefixes = next_prefixes
            # strip full line comments
            for prefix in self._comment_prefixes:
                if line.strip().startswith(prefix):
                    comment_start = 0
                    break
            if comment_start == sys.maxsize:
                comment_start = None
            value = line[:comment_start].strip()
            if not value:
                if self._empty_lines_in_values:
                    # add empty line to the value, but only if there was no
                    # comment on the line
                    if (
                        comment_start is None
                        and cursect is not None
                        and optname
                        and optname in cursect
                    ):  # CORVUS support for Unreal config array operators
                        cursect[optname].append("")  # newlines added at join
                else:
                    # empty line marks end of value
                    indent_level = sys.maxsize
                continue
            # continuation line?
            first_nonspace = self.NONSPACECRE.search(line)
            cur_indent_level = first_nonspace.start() if first_nonspace else 0
            if cursect is not None and optname and cur_indent_level > indent_level:
                cursect[optname].append(value)
            # a section header or option header?
            else:
                indent_level = cur_indent_level
                # is it a section header?
                mo = self.SECTCRE.match(value)
                if mo:
                    sectname = mo.group("header")
                    if sectname in self._sections:
                        if self._strict and sectname in elements_added:
                            raise DuplicateSectionError(sectname, fpname, lineno)
                        cursect = self._sections[sectname]
                        elements_added.add(sectname)
                    elif sectname == self.default_section:
                        cursect = self._defaults
                    else:
                        cursect = self._dict()
                        self._sections[sectname] = cursect
                        self._proxies[sectname] = SectionProxy(self, sectname)
                        elements_added.add(sectname)
                    # So sections can't start with a continuation line
                    optname = None
                # no section header in the file?
                elif cursect is None:
                    raise MissingSectionHeaderError(fpname, lineno, line)
                # an option line?
                else:
                    mo = self._optcre.match(value)
                    if mo:
                        optname, vi, optval = mo.group("option", "vi", "value")
                        if not optname:
                            e = self._handle_error(e, fpname, lineno, line)
                        optname = self.optionxform(optname.rstrip())
                        if self._strict and (sectname, optname) in elements_added:
                            raise DuplicateOptionError(
                                sectname, optname, fpname, lineno
                            )
                        elements_added.add((sectname, optname))
                        # This check is fine because the OPTCRE cannot
                        # match if it would set optval to None
                        if optval is not None:
                            optval = optval.strip()

                            # CORVUS_BEGIN support for Unreal config array operators
                            if self.is_special_key(
                                optname
                            ):  # Treat special keys differently
                                cursect[self.SPECIAL_KEYS] = cursect.get(
                                    self.SPECIAL_KEYS, {}
                                )

                                array_key = optname[1:]
                                cursect[self.SPECIAL_KEYS][array_key] = cursect[
                                    self.SPECIAL_KEYS
                                ].get(array_key, [])
                                cursect[self.SPECIAL_KEYS][array_key].append(
                                    (optname, optval)
                                )
                                continue
                            # CORVUS_END
                            cursect[optname] = [optval]
                        else:
                            # valueless option handling
                            cursect[optname] = None
                    else:
                        # a non-fatal parsing error occurred. set up the
                        # exception but keep going. the exception will be
                        # raised at the end of the file and will contain a
                        # list of all bogus lines
                        e = self._handle_error(e, fpname, lineno, line)
        self._join_multiline_values()
        # if any parsing errors occurred, raise an exception
        if e:
            raise e

    def _join_multiline_values(self):
        defaults = self.default_section, self._defaults
        all_sections = itertools.chain((defaults,), self._sections.items())
        for section, options in all_sections:
            for name, val in options.items():
                # CORVUS_BEGIN support for Unreal config array operators
                if name == self.SPECIAL_KEYS:
                    continue
                # CORVUS_END

                if isinstance(val, list):
                    val = "\n".join(val).rstrip()
                options[name] = self._interpolation.before_read(
                    self, section, name, val
                )

    # --------------------------------------------------------------------------

    _comment_map: dict[str, dict[str, list[str]]] | None = None
    _orphan_array_modifier_comment: dict[str, dict[str, list[str]]] | None = None

    def read(
        self,
        filenames: StrOrBytesPath | Iterable[StrOrBytesPath],
        encoding: str | None = None,
    ) -> list[str]:

        if isinstance(filenames, (str, bytes, os.PathLike)):
            filenames = [filenames]

        for filename in filenames:
            content = self._fileload(filename, encoding)
            self._map_comments(content)

        return super().read(filenames, encoding)

    def read_file(self, f: Iterable[str], source: str | None = None) -> None:

        content = [line for line in f]
        self._map_comments("".join(content))

        return super().read_file(content, source)

    def write(
        self, fp: SupportsWrite[str], space_around_delimiters: bool = True
    ) -> None:
        # Early exit if the config was never loaded with comments (from_dict/run-time)
        if self._comment_map is None:
            return super().write(fp, space_around_delimiters)

        capture_output = StringIO()
        super().write(capture_output, space_around_delimiters)

        self._merge_deleted_keys()

        rendered_output = self._restore_comments(capture_output.getvalue())

        fp.write(rendered_output)

    @staticmethod
    def _fileload(
        filepath: StrOrBytesPath,
        encoding: str | None = None,
    ) -> str | None:
        """Load a file if it exists."""
        try:
            with open(filepath, encoding=encoding) as infile:
                return infile.read()
        except OSError:
            return None

    @staticmethod
    def _is_comment(line: str) -> bool:
        """True if the line is a valid ini comment."""
        return bool(COMMENT_PTN.search(line))

    @staticmethod
    def _is_empty(line: str) -> bool:
        """True if line is just whitespace."""
        return not bool(re.sub(r"\s*", "", line))

    @staticmethod
    def _is_section(line: str) -> bool:
        """True if line is a section."""
        return bool(SECTION_PTN.search(line))

    def _is_key(self, line: str) -> bool:
        """True if line is a key_value."""
        return bool(self._optcre.search(line))

    def _get_key(self, line: str) -> str:
        """
        Return the key of a line trimmed of leading/trailing whitespace.

        Respects both `=` and `:` delimiters, uses which happens first. If
        the line contains neither, the entire line is returned.
        """
        # Find which of the two assignment delimiters is used first
        matches = self._optcre.match(line)
        return matches.group(1).strip() if matches else line.strip()

    def _get_value(self, line: str) -> str:
        """
        /!\ will only work with `allow_no_value=True`
        Return the value of a line trimmed of leading/trailing whitespace.

        Respects both `=` and `:` delimiters, uses which happens first. If
        the line contains neither, the entire line is returned.
        """
        # Find which of the two assignment delimiters is used first
        matches = self._optcre.match(line)
        return matches.group(3).strip() if matches else line.strip()

    def _map_comments(self, content: str | None) -> None:
        """Map comments of config internally for restoration on write."""
        # The map holds comments that happen under the given key
        # @@header is an arbitrary section and key assigned to
        # capture the top of a file or section.
        section = "@@header"
        key = "@@header"

        content_lines = content.split("\n") if content is not None else []
        comment_lines: list[str] = []
        comment_map = self._comment_map if self._comment_map else {}

        comment_map[section] = comment_map.get(section, {})
        comment_map[section][key] = comment_map[section].get(key, [])

        self._orphan_array_modifier_comment = {}

        last_array_value = None
        for line in content_lines:
            if self._is_comment(line):
                matches = COMMENT_PTN.match(line)
                if matches:
                    comment = matches.group(1)
                    comment_key = self._get_key(comment)

                    # Regroup all "orphan" array modifier comment to the latest matching uncommented array modifier so it's easier to find them
                    if (
                        len(comment_lines) == 0
                        and section != "@@header"
                        and self.is_special_key(comment_key)
                    ):
                        comment_key = comment_key[1:]
                        self._orphan_array_modifier_comment[
                            section
                        ] = self._orphan_array_modifier_comment.get(section, {})
                        self._orphan_array_modifier_comment[section][
                            comment_key
                        ] = self._orphan_array_modifier_comment[section].get(
                            comment_key, []
                        )
                        self._orphan_array_modifier_comment[section][
                            comment_key
                        ].append(line)
                        continue

                comment_lines.append(line)

            # We allow empty lines to be ignored giving the library
            # control over general line spacing format.
            elif not self._is_empty(line):
                # Figure out if we have a key or a new section
                if self._is_section(line):
                    # TODO: Probably should rename this method. _get_token() ?
                    new_section = self._get_key(line)
                    new_key = "@@header"

                    if key != "@@header":
                        key = "@@footer"

                else:
                    new_section = section
                    new_key = self._get_key(line)

                if key not in [
                    "@@header",
                    "@@footer",
                ]:  # or not self._is_section(line):
                    if self.is_special_key(key):
                        value = self._get_value(line)
                        comment_map[section][key] = comment_map[section].get(key, {})
                        comment_map[section][key][value] = comment_map[section][
                            key
                        ].get(value, [])
                    else:
                        comment_map[section][key] = comment_map[section].get(key, [])

                    key = new_key
                    section = new_section

                # Define the section or use existing
                comment_map[section] = comment_map.get(section, {})

                # for special keys (list operator +-!.) we want to store the value too,
                # to remember which line the comment should be put back (duplicate keys)
                if self.is_special_key(key):
                    last_array_value = self._get_value(line)

                    # Update the current section, clear, and start again
                    comment_map[section][key] = comment_map[section].get(key, {})
                    comment_map[section][key][last_array_value] = (
                        comment_map[section][key].get(last_array_value, [])
                        + comment_lines
                    )
                    comment_lines.clear()
                else:
                    # Update the current section, clear, and start again
                    comment_map[section][key] = (
                        comment_map[section].get(key, []) + comment_lines.copy()
                    )
                    comment_lines.clear()

                key = new_key
                section = new_section

        last_section_comments = []
        footer_comments = []
        for comment in comment_lines:
            if self._is_key(comment):
                last_section_comments.append(comment)
            else:
                footer_comments.append(comment)

        # last section comments
        comment_map[section] = comment_map.get(section, {})
        comment_map[section]["@@footer"] = last_section_comments

        # footer comments
        comment_map["@@footer"] = comment_map.get("@@footer", {})
        comment_map["@@footer"]["@@footer"] = footer_comments.copy()

        self._comment_map = comment_map

    def _restore_comments(self, content: str) -> str:
        """Restore comments from internal map."""
        if self._comment_map is None:
            # This should never be needed
            return content

        section = "@@header"
        key = "@@header"
        # Apply the headers before parsing the config lines
        header = self._comment_map[section].get(key, [])
        rendered: list[str] = header
        if len(header) > 0:
            rendered.append("")

        for line in content.splitlines():
            # Order of reconstruction is section comments then any config-line
            if self._is_section(line):
                if len(rendered) > 0 and rendered[-1] == "":
                    rendered.pop()
                    rendered.extend(
                        self._comment_map.get(section, {}).get("@@footer", [])
                    )
                    rendered.append("")

                section = self._get_key(line)
                key = "@@header"

                rendered.append(line)
                rendered.extend(self._comment_map.get(section, {}).get(key, []))
            else:
                key = self._get_key(line)

                if self.is_special_key(key):
                    value = self._get_value(line)
                    comment = (
                        self._comment_map.get(section, {}).get(key, {}).get(value, [])
                    )
                    rendered.extend(comment)
                    if len(comment) > 0:
                        self._comment_map[section][key][value] = []
                else:
                    rendered.extend(self._comment_map.get(section, {}).get(key, []))
                    self._comment_map[section][key] = []
                rendered.append(line)
        if section != "@@header":
            rendered.extend(self._comment_map.get(section, {}).get("@@footer", []))
        rendered.extend(self._comment_map.get("@@footer", {}).get("@@footer", []))

        return "\n".join(rendered)

    def _merge_deleted_keys(self) -> None:
        """Find and merges comments of deleted keys up the comment_map tree."""
        if self._comment_map is None:
            return

        # Regroup all "orphan" array modifier comment to the latest matching uncommented array modifier so it's easier to find them
        for section in self._orphan_array_modifier_comment:
            for comment_key in self._orphan_array_modifier_comment[section]:
                for key, value in self._sections[section[1:-1]].items():
                    if key == self.SPECIAL_KEYS:
                        last_match = None
                        for array_key_value in value.items():
                            for special_key, special_value in array_key_value[1]:
                                if special_key[1:] == comment_key:
                                    last_match = array_key_value[1][-1]

                        if last_match is not None:
                            special_key, special_value = last_match
                            self._comment_map[section][special_key] = self._comment_map[
                                section
                            ].get(special_key, {})
                            self._comment_map[section][special_key][
                                special_value
                            ] = self._comment_map[section][special_key].get(
                                special_value, []
                            )
                            self._comment_map[section][special_key][
                                special_value
                            ] += self._orphan_array_modifier_comment[section][
                                comment_key
                            ]
                        else:
                            self._comment_map[section]["@@footer"] = self._comment_map[
                                section
                            ].get("@@footer", [])
                            self._comment_map[section]["@@footer"] = (
                                self._orphan_array_modifier_comment[section][
                                    comment_key
                                ]
                                + self._comment_map[section]["@@footer"]
                            )

        orphaned_comments: list[str] = []
        # Walk the sections and keys backward, so we merge 'up'.
        for section in list(self._comment_map.keys())[::-1]:
            section_mch = SECTION_PTN.match(section)
            if section_mch is None:
                # Strange that we have a section value that isn't a valid section
                continue

            for key in list(self._comment_map[section])[::-1]:
                if self.is_special_key(key):
                    continue
                # Key no longer exists, gather comments and loop upward
                elif key not in ["@@header", "@@footer"] and not self.has_option(
                    section_mch.group(1), key
                ):
                    # Comments need to be stored in reverse order to avoid
                    # needing to insert into front of list
                    orphaned_comments.extend(self._comment_map[section].pop(key)[::-1])

                elif section_mch.group(1) in self.keys():
                    # Drop everything in the next key that exists
                    # If the section is gone carry all comments up to bottom of next
                    # Reverse the order as they were added in reverse
                    self._comment_map[section][key].extend(orphaned_comments[::-1])
                    orphaned_comments.clear()

            # Remove sections that should now be empty
            if not section_mch.group(1) in self.keys():
                self._comment_map.pop(section)

        # All remaining orphans moved to the top of the file
        self._comment_map["@@header"]["@@header"].extend(orphaned_comments[::-1])
