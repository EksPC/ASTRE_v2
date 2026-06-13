python3 - <<'PY'
import re
from pathlib import Path

path = Path("patches/Problem15_best_patch.txt")
text = path.read_text()
match = re.search(r"originalOperators=\[(.*?)\]", text, re.S)
operators = [x.strip() for x in match.group(1).split(",")]

for index in [285, 632, 645, 1060]:
    print(f"[{index}] = {operators[index]}")
PY