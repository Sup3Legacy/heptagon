# Translate -deps produced by hacked Heptagon into a normal .depend file

import sys
import re

ignored_reqs = [ '', '_null' ]

re_depline = re.compile(r'(?P<filename>[^=]*)=(?P<defs>[^:]*):(?P<reqs>.*)')

filedeps = {}       # map filename to the symbols they require
definedby = {}      # map symbols to the filenames that define them

# Read from stdin into the two mappings above
for l in sys.stdin.readlines():
    r = re_depline.match(l)
    if not r: continue

    filename = r.group('filename')
    defined = filter(lambda s: s <> '', r.group('defs').split(" "))
    required = filter(lambda s: s not in ignored_reqs,
                      r.group('reqs').split(" "))

    filedeps[filename] = required

    for d in defined:
        definedby[d] = filename

# Print a default target
print "_default: default"

# Translate the dependencies using the mappings
filenames = filedeps.keys()
filenames.sort()

missing = []
for filename in filenames:
    deps = {}
    for r in filedeps[filename]:
        try:
            deps[definedby[r]] = True
        except KeyError:
            missing.append(r)
    print "%s:%s" % (filename, " ".join(deps.keys()))

# print out all the filenames
print "OBJS=",
first=True
for filename in filenames:
    if first:
        first = False
        print "%s" % filename,
    else:
        print " \\\n\t%s" % filename,
print

# Print the symbols that could not be resolved
for m in missing:
    print "! could not find '%s'" % m

