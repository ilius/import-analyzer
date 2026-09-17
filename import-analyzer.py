#!/usr/bin/env python3

import argparse
import ast
import json
import os
import re
import subprocess
import sys
import warnings
from collections.abc import Sequence
from functools import lru_cache
from os.path import dirname, isdir, isfile, join, realpath, split

import tomllib

warnings.simplefilter("ignore")

editor = os.getenv("IDE", "xdg-open")
modifiedFiles = set()

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

modifyAndOpenFiles = not args.no_modify

scanDir = realpath(args.scan_dir)

rootDir = scanDir
scanDirParts = scanDir.split("/")
for count in range(len(scanDirParts), 1, -1):
	_testDir = join("/", *scanDirParts[:count])
	if isfile(join(_testDir, "pyproject.toml")):
		rootDir = _testDir
if not rootDir.endswith("/"):
	rootDir += "/"
print(f"Root Dir: {rootDir}")

with open(join(rootDir, "pyproject.toml"), "rb") as _cfg_file:
	full_config = tomllib.load(_cfg_file)
tool_config = full_config.get("tool") or {}
config = tool_config.get("import-analyzer") or {}

re_exclude_list = [re.compile("^" + pat) for pat in config.get("exclude", [])]
exclude_toplevel_module = set(config.get("exclude_toplevel_module", []))

imported_from_by_module_path: dict[str, set[str]] = {}

all_module_attr_access: set[tuple[str, str]] = set()


@lru_cache(maxsize=None, typed=False)
def is_excluded(fpath: str) -> bool:
	return any(pat.match(fpath) for pat in re_exclude_list)


def formatList(lst: list[str]) -> str:
	return json.dumps(lst)


@lru_cache(maxsize=None, typed=False)
def moduleFilePath(
	module: str,
	dirPathRel: str,
	subDirs: list[str],
	files: list[str],
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
	if main in exclude_toplevel_module:
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
	dpath = join(rootDir, pathRel)
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
		if isinstance(stm.value, ast.Tuple):
			print("WARNING: __all__ is a tuple: ", code)
		assert isinstance(stm.value, ast.List | ast.Tuple), f"{stm.value=}"
		assert len(stm.targets) == 1
		# stm.value.elts[i]: ast.Constant
		all_ = []
		for elem in stm.value.elts:
			assert isinstance(elem, ast.Constant)
			all_.append(elem.value)
		return stm, all_
	return None, None


def processFile(dirPathRel: str, fname: str, subDirs: list[str]) -> None:
	if not fname.endswith(".py"):
		return
	fpath = join(dirPath, fname)
	if is_excluded(fpath):
		return
	# print(fpath)
	# strip rootDir prefix
	fpathRel = fpath[len(rootDir) :]

	if is_excluded(fpathRel):
		return
	# print(f"{fpathRel = }")

	imports_by_name: dict[str, tuple[str, str | None]] = {}
	attr_access = set()

	def handleImport(stm: ast.Import) -> None:
		for name in stm.names:
			module_fpath = moduleFilePath(
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
				imports_by_name[name.name] = (name.name, module_fpath)

	def handleImportFrom(stm: ast.ImportFrom) -> None:
		module = stm.module
		if module is None:
			# print(f"{module = }, {stm!r}", file=sys.stderr)
			module = dirPathRel.replace("/", ".")
		module_fpath = moduleFilePath(
			module,
			dirPathRel,
			tuple(subDirs),
			tuple(files),
		)
		if module_fpath is None:
			return
		try:
			import_froms_set = imported_from_by_module_path[module_fpath]
		except KeyError:
			import_froms_set = imported_from_by_module_path[module_fpath] = set()
		for name in stm.names:
			if not name.name:
				# print(f"{name = }", file=sys.stderr)
				continue
			full_name = module + "." + name.name
			tmp_module_fpath = moduleFilePath(
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
		if isinstance(stm.value, ast.Name):
			attr_access.add((stm.value.id, stm.attr))
		else:
			handleStatement(stm.value)

	def handleStatementList(statements: Sequence[ast.AST | None]) -> None:
		for stm in statements:
			handleStatement(stm)

	def handleStatements(*statements: ast.AST | None) -> None:
		for stm in statements:
			handleStatement(stm)

	def handleStatement(stm: ast.AST | None) -> None:
		if stm is None:
			return
		if isinstance(stm, ast.Import):
			handleImport(stm)
		elif isinstance(stm, ast.ImportFrom):
			handleImportFrom(stm)
		elif isinstance(stm, ast.Name):
			# print(f"name: id={stm.id}")
			pass
		elif isinstance(
			stm,
			ast.Pass
			| ast.Break
			| ast.Continue
			| ast.Delete
			| ast.Constant
			| ast.JoinedStr
			| ast.Slice
			| ast.Global,
		):
			pass
		elif isinstance(stm, ast.Assign):
			handleStatement(stm.value)
			handleStatementList(stm.targets)
		elif isinstance(stm, ast.AugAssign):
			handleStatements(stm.target, stm.value)
		elif isinstance(stm, (ast.Expr, ast.Return, ast.Yield, ast.YieldFrom)):
			handleStatement(stm.value)
		elif isinstance(stm, ast.Assert):
			handleStatements(stm.test, stm.msg)
		elif isinstance(stm, ast.IfExp):
			handleStatements(stm.test, stm.body, stm.orelse)
		elif isinstance(stm, ast.FunctionDef):
			handleStatementList(stm.args.defaults)
			handleStatementList(stm.body)
			handleStatementList(stm.decorator_list)
		elif isinstance(stm, ast.ClassDef):
			handleStatementList(stm.body)
		elif isinstance(stm, ast.BoolOp):
			handleStatementList(stm.values)
		elif isinstance(stm, ast.Subscript):
			handleStatements(stm.value, stm.slice)
		elif isinstance(stm, ast.With):
			handleStatementList([*stm.items, *stm.body])
		elif isinstance(stm, ast.List | ast.Tuple | ast.Set):
			handleStatementList(stm.elts)
		elif isinstance(stm, ast.Lambda):
			handleStatement(stm.body)
		elif isinstance(stm, ast.For):
			handleStatementList([stm.target, stm.iter, *stm.body, *stm.orelse])
		elif isinstance(stm, ast.While):
			handleStatementList([stm.test, *stm.body, *stm.orelse])
		elif isinstance(stm, ast.BinOp):
			handleStatements(stm.left, stm.right)
		elif isinstance(stm, ast.UnaryOp):
			handleStatement(stm.operand)
		elif isinstance(stm, ast.Try):
			handleStatementList(
				[*stm.body, *stm.handlers, *stm.orelse, *stm.finalbody],
			)
		elif isinstance(stm, ast.ExceptHandler):
			handleStatementList([stm.type, *stm.body])
		elif isinstance(stm, ast.Call):
			for arg in stm.args:
				handleStatement(arg)
			for kw in stm.keywords:
				handleStatement(kw.value)
			handleStatement(stm.func)
		elif isinstance(stm, ast.If):
			handleStatementList([stm.test, *stm.body])
		elif isinstance(stm, ast.Compare):
			handleStatementList([stm.left, *stm.comparators])
		elif isinstance(stm, ast.withitem):
			handleStatements(stm.context_expr, stm.optional_vars)
		elif isinstance(stm, ast.Raise):
			handleStatement(stm.exc)
		elif isinstance(stm, ast.Dict):
			handleStatementList(stm.keys)
			handleStatementList(stm.values)
		elif isinstance(
			stm,
			ast.ListComp | ast.SetComp | ast.GeneratorExp | ast.DictComp,
		):
			handleStatementList(stm.generators)
		elif isinstance(stm, ast.comprehension):
			handleStatementList([stm.target, stm.iter] + stm.ifs)
		elif isinstance(stm, ast.Attribute):
			handleAttribute(stm)
		elif isinstance(stm, ast.AnnAssign):
			handleStatements(stm.target, stm.annotation, stm.value)
		elif isinstance(stm, ast.NamedExpr):
			handleStatements(stm.target, stm.value)
		elif isinstance(stm, ast.AsyncFunctionDef):
			handleStatementList(stm.args.defaults)
			handleStatementList(stm.body)
			handleStatementList(stm.decorator_list)
		elif isinstance(stm, ast.Starred):
			handleStatement(stm.value)
		elif isinstance(stm, ast.Nonlocal):
			# stm.names is list[str]
			pass
		elif isinstance(stm, ast.TypeAlias):
			# TODO
			pass
		else:
			print(f"Unknown statemnent type: {stm} with type {type(stm)}")
		return

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

	for id_, attr in attr_access:
		if id_ in {"self", "msg"}:
			continue
		if id_ not in imports_by_name:
			# print(f"{fpathRel}: {_id}.{attr}  (Unknown)")
			continue
		_module, module_fpath = imports_by_name[id_]
		# print(f"{fpathRel}: {module}.{attr} from file ({module_fpath})")
		all_module_attr_access.add((attr, module_fpath))

	# print(json.dumps(list(attr_access)))


for dirPath, subDirs, files in os.walk(scanDir):
	dirPathRel = dirPath[len(rootDir) :]

	for fname in files:
		processFile(dirPathRel, fname, subDirs)


to_check_imported_modules = set()
for module_fpath in imported_from_by_module_path:
	if module_fpath is None:
		continue
	to_check_imported_modules.add(module_fpath)


for _attr, module_fpath in all_module_attr_access:
	if module_fpath is None:
		continue
	to_check_imported_modules.add(module_fpath)


module_attr_access_by_fpath: dict[str, set[str]] = {}
for attr, module_fpath in all_module_attr_access:
	if module_fpath is None:
		continue
	try:
		attrs = module_attr_access_by_fpath[module_fpath]
	except KeyError:
		attrs = module_attr_access_by_fpath[module_fpath] = set()
	attrs.add(attr)


slashDunderInit = os.sep + "__init__.py"

for module_fpath in sorted(to_check_imported_modules):
	# print(module, module_fpath)
	full_path = join(rootDir, module_fpath)
	with open(full_path, encoding="utf-8") as _file:
		text = _file.read()
	if is_excluded(module_fpath):
		continue
	module_top = module_fpath.split("/")[0]
	if module_top in exclude_toplevel_module:
		continue
	try:
		code = ast.parse(text)
	except Exception as e:
		print(f"failed to parse {module_fpath=}: {e}", file=sys.stderr)
		continue
	_, _all = find__all__(code)
	has_all = False
	if _all is None:
		_all_set = set()
		_all_set_current = set()
	else:
		has_all = True
		_all_set = set(_all)
		_all_set_current = _all_set.copy()
	names1 = imported_from_by_module_path.get(module_fpath)
	if names1:
		for name in names1:
			if module_fpath.endswith(slashDunderInit):
				moduleDirName = join(dirname(module_fpath), name)
				if isfile(moduleDirName + ".py") or isdir(moduleDirName):
					continue
			_all_set.add(name)
	names2 = module_attr_access_by_fpath.get(module_fpath)
	if names2:
		_all_set.update(names2)
	_all_set.discard("*")
	if not _all_set:
		continue

	if has_all:
		used_set = set(names1 or []) | set(names2 or [])
		unused_set = _all_set_current.difference(used_set)
		# print(f"{module_fpath}: used {sorted(used_set)}")
		for symbol in sorted(unused_set):
			if symbol.startswith("__") and symbol.endswith("__"):
				continue
			print(f"{module_fpath}: unused symbol {symbol} in __all__")

	if len(_all_set) == len(_all_set_current):
		continue
	add_list = list(_all_set.difference(_all_set_current))

	if has_all:
		print(module_fpath)
		print("ADD to __all__:", formatList(add_list))
		print()
	elif modifyAndOpenFiles:
		with open(module_fpath, encoding="utf-8") as file:
			text = file.read()
		text = f"__all__ = {add_list!r}" + "\n" + text
		with open(module_fpath, "w", encoding="utf-8") as file:
			file.write(text)
		modifiedFiles.add(module_fpath)
	else:
		print(module_fpath)
		print("__all__ =", formatList(add_list))
		print()


if modifiedFiles:
	cmd = [editor] + [join(rootDir, p) for p in modifiedFiles]
	print(cmd)
	subprocess.call(cmd)
