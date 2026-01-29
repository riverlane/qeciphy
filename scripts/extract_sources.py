# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2025 Riverlane Ltd.

import sys
import os

def process_f_file(filepath, root, visited):
    sources = []
    incdirs = []
    try:
        with open(filepath, 'r') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                if line.startswith("+incdir+"):
                    incdir = line[len("+incdir+"):]
                    incdirs.append(incdir)
                elif line.startswith("-F "):
                    subfile = line[3:].strip()
                    # Resolve relative to project root
                    subfile_path = os.path.normpath(os.path.join(root, subfile))
                    key = os.path.abspath(subfile_path)
                    if key not in visited:
                        visited.add(key)
                        sub_sources, sub_incdirs = process_f_file(subfile_path, root, visited)
                        sources.extend(sub_sources)
                        incdirs.extend(sub_incdirs)
                elif line.endswith(".sv") or line.endswith(".v") or line.endswith(".xci"):
                    sources.append(line)
    except Exception as e:
        sys.stderr.write(f"Error reading file {filepath}: {e}\n")
    return sources, incdirs

def main():
    if len(sys.argv) < 2:
        print("Usage: extract_sources.py <file1.f> [file2.f ...]")
        sys.exit(1)

    files = sys.argv[1:]
    all_sources = []
    all_incdirs = []
    visited = set()

    # Project root is where script is run from
    root = os.getcwd()
    for f in files:
        f_path = os.path.normpath(os.path.join(root, f))
        sources, incdirs = process_f_file(f_path, root, visited)
        all_sources.extend(sources)
        all_incdirs.extend(incdirs)

    for s in all_sources:
        print(s)

if __name__ == "__main__":
    main()