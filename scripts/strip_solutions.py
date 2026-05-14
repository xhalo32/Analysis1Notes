#!/usr/bin/env python
import os, re

exercisedir = 'Exercises'
basedir = 'Solutions'

# TODO just strip out solutions...

# Finds declarations (in this case examples, lemmas or theorems)
# decl_regex = re.compile(r'[^ ]((.\n?)*by)', re.MULTILINE)

# header_regex = re.compile(r'((.|\n)*?)theorem', re.MULTILINE)

# def process(file):
#     out = ""
#     with open(file) as f:
#         content = f.read()
#         out += header_regex.search(content).group(1)
        
#         for (decl, _) in decl_regex.findall(content):
#             out += decl
#             out += "\n  sorry\n\n"
#     return out.strip()

def process(file):
    out = ""
    with open(file) as f:
        content = f.read().split('\n')
        in_decl = False # Have we seen a declaration statement
        in_body = False # Have we seen := by
        for line in content:
            if in_body and not line.startswith("  "):
                in_decl = False
                in_body = False
                out += "  sorry\n"
            if not in_body:
                out += line
                out += "\n"
            if line.startswith("theorem") or line.startswith("example") or line.startswith("lemma"):
                in_decl = True
            if in_decl and line.endswith(":= by"):
                in_body = True
            # print(in_decl, in_body, line)

    return out.strip()

for root, dirs, files in os.walk(basedir):
    for file in files:
        if file.endswith(".lean"):
            out = process(os.path.join(basedir, file))
            # print(out)
            with open(os.path.join(exercisedir, file), 'w') as f:
                f.write(out)
