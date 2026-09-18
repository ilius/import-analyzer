#!/usr/bin/env python3

import argparse
import ast
import json
import os
import re
import subprocess
import sys
import warnings
from collections.abc import Callable, Iterable, Sequence
from functools import lru_cache
from os.path import dirname, isdir, isfile, join, realpath, split

import tomllib

warnings.simplefilter("ignore")

# AST node types with no traversable children.
_LEAF_TYPES: tuple[type[ast.AST], ...] = (
	ast.Name,
	ast.Pass,
	ast.Break,
	ast.Continue,
	ast.Delete,
	ast.Constant,
	ast.Slice,
	ast.Global,
	ast.Nonlocal,
	ast.MatchSingleton,
	ast.MatchStar,
)


def _all_children(node: ast.AST) -> Iterable[ast.AST | None]:
	return ast.iter_child_nodes(node)


def _function_children(
	node: ast.FunctionDef | ast.AsyncFunctionDef,
) -> Sequence[ast.AST | None]:
	return (*node.args.defaults, *node.body, *node.decorator_list)


def _class_children(node: ast.ClassDef) -> Sequence[ast.AST | None]:
	return tuple(node.body)


def _lambda_children(node: ast.Lambda) -> Sequence[ast.AST | None]:
	return (node.body,)


def _raise_children(node: ast.Raise) -> Sequence[ast.AST | None]:
	return (node.exc,)


def _no_children(_node: ast.AST) -> Sequence[ast.AST | None]:
	return ()


# AST node types whose traversal differs from "visit every child node".
_CHILD_GETTERS: dict[type[ast.AST], Callable[..., Iterable[ast.AST | None]]] = {
	ast.FunctionDef: _function_children,
	ast.AsyncFunctionDef: _function_children,
	ast.ClassDef: _class_children,
	ast.Lambda: _lambda_children,
	ast.Raise: _raise_children,
	ast.TypeAlias: _no_children,
}


def formatList(lst: list[str]) -> str:
	return json.dumps(lst)


def find__all__(code: ast.Module) -> tuple[ast.Assign | None, list[str] | None]:
	for stm in code.body:
		if not isinstance(stm, ast.Assign):
			continue
		target = stm.targets[0]
		if not isinstance(target, ast.Name):
			continue
		# print(target)
		if target.id != "__all__":
			continue
		if not isinstance(stm.value, ast.List | ast.Tuple):
			return None, None
		if len(stm.targets) != 1:
			return None, None
		all_ = []
		for elem in stm.value.elts:
			if not isinstance(elem, ast.Constant) or not isinstance(elem.value, str):
				return None, None
			all_.append(elem.value)
		return stm, all_
	return None, None


class ImportAnalyzer:
	def __init__(self, scan_dir: str, modify_and_open_files: bool) -> None:
		self.modify_and_open_files = modify_and_open_files
		self.editor = os.getenv("IDE", "xdg-open")
		self.modified_files: set[str] = set()
		self.scan_dir = realpath(scan_dir)
		self.root_dir = self._findRootDir(self.scan_dir)
		self.imported_from_by_module_path: dict[str, set[str]] = {}
		self.all_module_attr_access: set[tuple[str, str]] = set()
		self.exclude_toplevel_module: set[str] = set()
		self._loadConfig()

	def _findRootDir(self, scan_dir: str) -> str:
		root_dir = scan_dir
		parts = scan_dir.split("/")
		for count in range(len(parts), 1, -1):
			test_dir = join("/", *parts[:count])
			if isfile(join(test_dir, "pyproject.toml")):
				root_dir = test_dir
		if not root_dir.endswith("/"):
			root_dir += "/"
		print(f"Root Dir: {root_dir}")
		return root_dir

	def _loadConfig(self) -> None:
		with open(join(self.root_dir, "pyproject.toml"), "rb") as file_:
			full_config = tomllib.load(file_)
		config = (full_config.get("tool") or {}).get("import-analyzer") or {}
		self.exclude_toplevel_module = set(config.get("exclude_toplevel_module", []))
		re_exclude_list = [re.compile("^" + pat) for pat in config.get("exclude", [])]

		@lru_cache(maxsize=None, typed=False)
		def is_excluded(fpath: str) -> bool:
			return any(pat.match(fpath) for pat in re_exclude_list)

		@lru_cache(maxsize=None, typed=False)
		def moduleFilePath(
			module: str,
			dirPathRel: str,
			subDirs: tuple[str, ...],
			files: tuple[str, ...],
			silent: bool = False,
		) -> str | None:
			if not module:
				return None
			parts = module.split(".")
			if not parts:
				return None
			main = parts[0]
			if main in sys.stdlib_module_names:
				return None
			if main in self.exclude_toplevel_module:
				return None
			if main in files or main + ".py" in files or main in subDirs:
				parts = list(split(dirPathRel)) + parts
			# else:
			# 	try:
			# 		mod = __import__(main)
			# 	except ModuleNotFoundError:
			# 		pass
			# 	except Exception as e:
			# 		print(f"error importing {main}: {e}", file=sys.stderr)

			pathRel = join(*parts)
			dpath = join(self.root_dir, pathRel)
			if isdir(dpath):
				if isfile(join(dpath, "__init__.py")):
					return join(pathRel, "__init__.py")
				return None
			if isfile(dpath + ".py"):
				return pathRel + ".py"
			if not silent:
				print(
					f"Unknown module {module}: {pathRel=}, used in {dirPathRel}",
					file=sys.stderr,
				)
			return None

		self.is_excluded = is_excluded
		self.moduleFilePath = moduleFilePath

	def processFile(
		self, dirPathRel: str, fname: str, subDirs: list[str], files: list[str]
	) -> None:
		if not fname.endswith(".py"):
			return
		fpath = join(self.root_dir, dirPathRel, fname)
		if self.is_excluded(fpath):
			return
		# strip rootDir prefix
		fpathRel = fpath[len(self.root_dir) :]

		if self.is_excluded(fpathRel):
			return
		# print(f"{fpathRel = }")

		imports_by_name: dict[str, tuple[str, str | None]] = {}
		attr_access: set[tuple[str, str, int]] = set()

		def handleImport(stm: ast.Import) -> None:
			for name in stm.names:
				module_fpath = self.moduleFilePath(
					name.name,
					dirPathRel,
					tuple(subDirs),
					tuple(files),
				)
				if module_fpath is None:
					continue
				if name.asname:
					imports_by_name[name.asname] = (name.name, module_fpath)
				else:
					imports_by_name[name.name.split(".")[0]] = (name.name, module_fpath)

		def handleImportFrom(stm: ast.ImportFrom) -> None:
			module = stm.module
			if module is None:
				# print(f"{module = }, {stm!r}", file=sys.stderr)
				module = dirPathRel.replace("/", ".")
			module_fpath = self.moduleFilePath(
				module,
				dirPathRel,
				tuple(subDirs),
				tuple(files),
			)
			if module_fpath is None:
				return
			import_froms_set = self.imported_from_by_module_path.setdefault(
				module_fpath, set()
			)
			for name in stm.names:
				if not name.name:
					# print(f"{name = }", file=sys.stderr)
					continue
				full_name = module + "." + name.name
				tmp_module_fpath = self.moduleFilePath(
					full_name,
					dirPathRel,
					tuple(subDirs),
					tuple(files),
					silent=True,
				)
				if name.asname:
					imports_by_name[name.asname] = (full_name, tmp_module_fpath)
				else:
					imports_by_name[name.name] = (full_name, tmp_module_fpath)
				import_froms_set.add(name.name)

		def handleAttribute(stm: ast.Attribute) -> None:
			assert isinstance(stm.attr, str)
			attrs = []
			node: ast.AST = stm
			while isinstance(node, ast.Attribute):
				attrs.append(node.attr)
				node = node.value
			if isinstance(node, ast.Name):
				depth = len(attrs)
				for i, attr in enumerate(attrs):
					attr_access.add((node.id, attr, depth - i))
			else:
				handleStatement(stm.value)

		def handleStatement(stm: ast.AST | None) -> None:
			if stm is None:
				return
			if isinstance(stm, ast.Import):
				handleImport(stm)
			elif isinstance(stm, ast.ImportFrom):
				handleImportFrom(stm)
			elif isinstance(stm, ast.Attribute):
				handleAttribute(stm)
			elif isinstance(stm, _LEAF_TYPES):
				return
			else:
				getter = _CHILD_GETTERS.get(type(stm), _all_children)
				for child in getter(stm):
					handleStatement(child)

		with open(fpath, encoding="utf-8") as file_:
			text = file_.read()
		try:
			code = ast.parse(text)
		except Exception as e:
			print(f"failed to parse {fpath}: {e}", file=sys.stderr)
			return
		for stm in code.body:
			if isinstance(stm, ast.Import):
				handleImport(stm)
				continue

			if isinstance(stm, ast.ImportFrom):
				handleImportFrom(stm)
				continue

			handleStatement(stm)

		attr_access_by_name: dict[str, list[tuple[str, int]]] = {}
		for id_, attr, depth in attr_access:
			attr_access_by_name.setdefault(id_, []).append((attr, depth))

		for id_, items in attr_access_by_name.items():
			if id_ in {"self", "msg"}:
				continue
			if id_ not in imports_by_name:
				# print(f"{fpathRel}: {id_}.{attr}  (Unknown)")
				continue
			_module, module_fpath = imports_by_name[id_]
			if module_fpath is None:
				continue
			module_parts = _module.split(".")
			if len(module_parts) > 1 and id_ == module_parts[0]:
				# unaliased dotted import: submodule-deref hops come first,
				# the actual symbols are the deepest hops
				max_depth = max(item[1] for item in items)
				for attr, depth in items:
					if depth == max_depth and attr != module_parts[-1]:
						self.all_module_attr_access.add((attr, module_fpath))
			else:
				# plain or aliased import: keep all first-level attributes
				min_depth = min(item[1] for item in items)
				for attr, depth in items:
					if depth == min_depth:
						self.all_module_attr_access.add((attr, module_fpath))

		# print(json.dumps(list(attr_access)))

	def _scanFiles(self) -> None:
		for dirPath, subDirs, files in os.walk(self.scan_dir):
			dirPathRel = dirPath[len(self.root_dir) :]
			for fname in files:
				self.processFile(dirPathRel, fname, subDirs, files)

	def _modulesToCheck(self) -> set[str]:
		to_check_imported_modules = set()
		for module_fpath in self.imported_from_by_module_path:
			if module_fpath is None:
				continue
			to_check_imported_modules.add(module_fpath)

		for _attr, module_fpath in self.all_module_attr_access:
			if module_fpath is None:
				continue
			to_check_imported_modules.add(module_fpath)
		return to_check_imported_modules

	def _aggregateAttrAccess(self) -> dict[str, set[str]]:
		module_attr_access_by_fpath: dict[str, set[str]] = {}
		for attr, module_fpath in self.all_module_attr_access:
			if module_fpath is None:
				continue
			try:
				attrs = module_attr_access_by_fpath[module_fpath]
			except KeyError:
				attrs = module_attr_access_by_fpath[module_fpath] = set()
			attrs.add(attr)
		return module_attr_access_by_fpath

	@staticmethod
	def _lineOffsets(text: str) -> list[int]:
		line_offsets = []
		offset = 0
		for line in text.splitlines(keepends=True):
			line_offsets.append(offset)
			offset += len(line)
		return line_offsets

	def _replaceAllValue(
		self, text: str, all_stm: ast.Assign, new_all: list[str]
	) -> str:
		value = all_stm.value
		assert value.lineno is not None
		assert value.col_offset is not None
		assert value.end_lineno is not None
		assert value.end_col_offset is not None
		line_offsets = self._lineOffsets(text)
		start = line_offsets[value.lineno - 1] + value.col_offset
		end = line_offsets[value.end_lineno - 1] + value.end_col_offset
		return text[:start] + formatList(new_all) + text[end:]

	def _insertAll(self, text: str, code: ast.Module, new_all: list[str]) -> str:
		insert_at = 0
		first = code.body[0] if code.body else None
		if (
			isinstance(first, ast.Expr)
			and isinstance(first.value, ast.Constant)
			and isinstance(first.value.value, str)
		):
			assert first.end_lineno is not None
			line_offsets = self._lineOffsets(text)
			lines = text.splitlines(keepends=True)
			insert_at = line_offsets[first.end_lineno - 1] + len(
				lines[first.end_lineno - 1]
			)
		return (
			text[:insert_at] + f"__all__ = {formatList(new_all)}\n" + text[insert_at:]
		)

	def _writeFile(self, full_path: str, module_fpath: str, new_text: str) -> None:
		with open(full_path, "w", encoding="utf-8") as file:
			file.write(new_text)
		self.modified_files.add(module_fpath)

	def _processModule(
		self,
		module_fpath: str,
		module_attr_access_by_fpath: dict[str, set[str]],
	) -> None:
		# print(module, module_fpath)
		full_path = join(self.root_dir, module_fpath)
		with open(full_path, encoding="utf-8") as file_:
			text = file_.read()
		if self.is_excluded(module_fpath):
			return
		module_top = module_fpath.split("/", maxsplit=1)[0]
		if module_top in self.exclude_toplevel_module:
			return
		try:
			code = ast.parse(text)
		except Exception as e:
			print(f"failed to parse {module_fpath=}: {e}", file=sys.stderr)
			return
		all_stm, all_list = find__all__(code)
		has_all = False
		all_set = set()
		all_set_current = set()
		if all_list is not None:
			has_all = True
			all_set = set(all_list)
			all_set_current = all_set.copy()
		names1 = self.imported_from_by_module_path.get(module_fpath)
		if names1:
			slash_dunder_init = os.sep + "__init__.py"
			for name in names1:
				if module_fpath.endswith(slash_dunder_init):
					module_dir_name = join(dirname(module_fpath), name)
					if isfile(module_dir_name + ".py") or isdir(module_dir_name):
						continue
				all_set.add(name)
		names2 = module_attr_access_by_fpath.get(module_fpath)
		if names2:
			all_set.update(names2)
		all_set.discard("*")
		all_set_current.discard("*")
		if not all_set:
			return

		if has_all:
			used_set = set(names1 or []) | set(names2 or [])
			unused_set = all_set_current.difference(used_set)
			# print(f"{module_fpath}: used {sorted(used_set)}")
			for symbol in sorted(unused_set):
				if symbol.startswith("__") and symbol.endswith("__"):
					continue
				print(f"{module_fpath}: unused symbol {symbol} in __all__")

		add_list = sorted(all_set.difference(all_set_current))
		if not add_list:
			return

		if has_all and self.modify_and_open_files:
			assert all_stm is not None
			new_text = self._replaceAllValue(text, all_stm, sorted(all_set))
			self._writeFile(full_path, module_fpath, new_text)
		elif has_all:
			print(module_fpath)
			print("ADD to __all__:", formatList(add_list))
			print()
		elif self.modify_and_open_files:
			new_text = self._insertAll(text, code, add_list)
			self._writeFile(full_path, module_fpath, new_text)
		else:
			print(module_fpath)
			print("__all__ =", formatList(add_list))
			print()

	def _checkModules(self) -> None:
		module_attr_access_by_fpath = self._aggregateAttrAccess()
		for module_fpath in sorted(self._modulesToCheck()):
			self._processModule(module_fpath, module_attr_access_by_fpath)

	def run(self) -> None:
		self._scanFiles()
		self._checkModules()
		if self.modified_files:
			cmd = [self.editor] + [join(self.root_dir, p) for p in self.modified_files]
			print(cmd)
			subprocess.call(cmd)


def main() -> None:
	parser = argparse.ArgumentParser(
		prog=sys.argv[0],
		add_help=False,
		# allow_abbrev=False,
	)
	parser.add_argument(
		"--no-modify",
		action="store_true",
		help="do not modify files, only print",
	)
	parser.add_argument(
		"scan_dir",
		action="store",
		default=".",
		nargs="?",
	)
	args = parser.parse_args()
	ImportAnalyzer(args.scan_dir, not args.no_modify).run()


if __name__ == "__main__":
	main()
